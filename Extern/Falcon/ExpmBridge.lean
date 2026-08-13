/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPRBridge
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPRBridge

/-!
# The fixed-point layer of Falcon's `expm_p63`

`Falcon.Concrete.FPR.expm_p63` evaluates a degree-twelve polynomial in `UInt64` fixed point and
scales the result, computing `⌊2 ^ 63 * ccs * exp (-x)⌋` for a scale factor `ccs` in `[0, 1)` and
an argument `x` in `[0, log 2)`. Its accuracy therefore splits in two:

* how faithfully the fixed-point pipeline evaluates the polynomial it is given, and
* how well that polynomial approximates `exp (-x)`.

This module is the first half. It reads each machine operation as exact arithmetic on `ℕ` and
bounds the truncation each one contributes: `mulHi64` is the high half of a `128`-bit product, and
`mtwop63` is the conversion of an `FPR` in `[0, 1)` to a `63`-bit fixed-point fraction. The second
half — certifying the coefficient table against `Real.exp` — is a numerical-certification problem
of a different character, described in `docs/agents/expm-certification.md`.
-/

@[expose] public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

/-! ## The high half of a 64-bit product

`mulHi64` splits both operands into `32`-bit limbs and reassembles the carries, exactly as
`FPR.mul` does at `25` bits. The result is the top half of the `128`-bit product, and no
intermediate leaves its register. -/

private theorem toNat_and_low32 (v : UInt64) : (v &&& 0xFFFFFFFF).toNat = v.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem toNat_shiftRight_32_uint64 (v : UInt64) : (v >>> 32).toNat = v.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from by decide,
    Nat.shiftRight_eq_div_pow]

/-- The limb identity behind `mulHi64`, as plain arithmetic on `ℕ`: the high half of the product
is the top partial product plus the carries out of the two cross terms and the middle column. -/
private theorem mulHi_limbs (aHi aLo bHi bLo : ℕ) :
    (aHi * 2 ^ 32 + aLo) * (bHi * 2 ^ 32 + bLo) / 2 ^ 64
      = aHi * bHi + (aHi * bLo) / 2 ^ 32 + (aLo * bHi) / 2 ^ 32
        + ((aLo * bLo) / 2 ^ 32 + (aHi * bLo) % 2 ^ 32 + (aLo * bHi) % 2 ^ 32) / 2 ^ 32 := by
  -- name every quotient and remainder, so the identity becomes polynomial
  obtain ⟨q1, r1, hr1, he1⟩ : ∃ q r, r < 2 ^ 32 ∧ aHi * bLo = q * 2 ^ 32 + r :=
    ⟨aHi * bLo / 2 ^ 32, aHi * bLo % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _), by omega⟩
  obtain ⟨q2, r2, hr2, he2⟩ : ∃ q r, r < 2 ^ 32 ∧ aLo * bHi = q * 2 ^ 32 + r :=
    ⟨aLo * bHi / 2 ^ 32, aLo * bHi % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _), by omega⟩
  obtain ⟨q3, r3, hr3, he3⟩ : ∃ q r, r < 2 ^ 32 ∧ aLo * bLo = q * 2 ^ 32 + r :=
    ⟨aLo * bLo / 2 ^ 32, aLo * bLo % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _), by omega⟩
  have hd1 : (aHi * bLo) / 2 ^ 32 = q1 := by omega
  have hm1 : (aHi * bLo) % 2 ^ 32 = r1 := by omega
  have hd2 : (aLo * bHi) / 2 ^ 32 = q2 := by omega
  have hm2 : (aLo * bHi) % 2 ^ 32 = r2 := by omega
  have hd3 : (aLo * bLo) / 2 ^ 32 = q3 := by omega
  rw [hd1, hm1, hd2, hm2, hd3]
  -- the product, split at bit 64
  have hexp : (aHi * 2 ^ 32 + aLo) * (bHi * 2 ^ 32 + bLo)
      = (aHi * bHi + q1 + q2) * 2 ^ 64 + ((q3 + r1 + r2) * 2 ^ 32 + r3) := by
    calc (aHi * 2 ^ 32 + aLo) * (bHi * 2 ^ 32 + bLo)
        = aHi * bHi * 2 ^ 64 + (aHi * bLo) * 2 ^ 32 + (aLo * bHi) * 2 ^ 32
          + aLo * bLo := by ring
      _ = aHi * bHi * 2 ^ 64 + (q1 * 2 ^ 32 + r1) * 2 ^ 32 + (q2 * 2 ^ 32 + r2) * 2 ^ 32
          + (q3 * 2 ^ 32 + r3) := by rw [he1, he2, he3]
      _ = (aHi * bHi + q1 + q2) * 2 ^ 64 + ((q3 + r1 + r2) * 2 ^ 32 + r3) := by ring
  rw [hexp]
  -- the low part cannot reach the next multiple of 2 ^ 64
  obtain ⟨M, s, hs, hM⟩ : ∃ M s, s < 2 ^ 32 ∧ q3 + r1 + r2 = M * 2 ^ 32 + s :=
    ⟨(q3 + r1 + r2) / 2 ^ 32, (q3 + r1 + r2) % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _),
      by omega⟩
  have hMdiv : (q3 + r1 + r2) / 2 ^ 32 = M := by omega
  rw [hMdiv, hM]
  have hlow : (M * 2 ^ 32 + s) * 2 ^ 32 + r3 = M * 2 ^ 64 + (s * 2 ^ 32 + r3) := by ring
  rw [hlow, ← add_assoc, ← add_mul]
  have hfit : s * 2 ^ 32 + r3 < 2 ^ 64 := by nlinarith [hs, hr3]
  omega

/-- `mulHi64` is the high half of the exact product: `⌊a * b / 2 ^ 64⌋`. -/
private theorem toNat_mulHi64 (a b : UInt64) :
    (mulHi64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
  have haLo : (a &&& 0xFFFFFFFF).toNat = a.toNat % 2 ^ 32 := toNat_and_low32 a
  have hbLo : (b &&& 0xFFFFFFFF).toNat = b.toNat % 2 ^ 32 := toNat_and_low32 b
  have haHi : (a >>> 32).toNat = a.toNat / 2 ^ 32 := toNat_shiftRight_32_uint64 a
  have hbHi : (b >>> 32).toNat = b.toNat / 2 ^ 32 := toNat_shiftRight_32_uint64 b
  have hb32 : ∀ n : ℕ, n < 2 ^ 64 → n / 2 ^ 32 < 2 ^ 32 := by
    intro n hn; exact Nat.div_lt_of_lt_mul (by omega)
  -- every limb product fits a register
  have hprod : ∀ u v : UInt64, u.toNat < 2 ^ 32 → v.toNat < 2 ^ 32 →
      (u * v).toNat = u.toNat * v.toNat := by
    intro u v hu hv
    have hlt : u.toNat * v.toNat < 2 ^ 64 := by
      calc u.toNat * v.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_lt hu hv
        _ = 2 ^ 64 := by norm_num
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
  -- WIP: `mulHi_limbs` above carries the whole mathematical content; what remains is pushing
  -- `.toNat` through the unfolded expression tree, one `UInt64.toNat_*` lemma per node with a
  -- no-overflow side condition (all discharged by `hprod`, `hb32`, `haLo`/`hbLo`/`haHi`/`hbHi`),
  -- and then `exact mulHi_limbs _ _ _ _`.
  simp only [mulHi64]
  sorry

end Falcon.Concrete.FPRBridge
