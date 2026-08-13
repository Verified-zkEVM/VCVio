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
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

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

open Falcon.Concrete.FPR Polynomial

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

/-- Three `UInt64` additions whose exact sum fits a register agree with addition on `ℕ`. -/
private theorem toNat_add3_of_lt {x y z : UInt64}
    (h : x.toNat + y.toNat + z.toNat < 2 ^ 64) :
    (x + y + z).toNat = x.toNat + y.toNat + z.toNat := by
  have h1 : (x + y).toNat = x.toNat + y.toNat := toNat_add_of_lt_uint64 (by omega)
  rw [toNat_add_of_lt_uint64 (by omega : (x + y).toNat + z.toNat < 2 ^ 64), h1]

/-- Four `UInt64` additions whose exact sum fits a register agree with addition on `ℕ`. -/
private theorem toNat_add4_of_lt {x y z w : UInt64}
    (h : x.toNat + y.toNat + z.toNat + w.toNat < 2 ^ 64) :
    (x + y + z + w).toNat = x.toNat + y.toNat + z.toNat + w.toNat := by
  have h3 : (x + y + z).toNat = x.toNat + y.toNat + z.toNat := toNat_add3_of_lt (by omega)
  rw [toNat_add_of_lt_uint64 (by omega : (x + y + z).toNat + w.toNat < 2 ^ 64), h3]

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

/-- The final column of `mulHi64`, assembled. Given the exact values of the top partial product
`X`, of the two cross carries `Y` and `Z`, and of the three middle-column pieces `u`, `v`, `w`,
the column sums without leaving its register and equals the high half of `A * B`. -/
private theorem toNat_finalColumn {X Y Z u v w : UInt64} {A B : ℕ}
    (hA : A < 2 ^ 64) (hB : B < 2 ^ 64)
    (hX : X.toNat = A / 2 ^ 32 * (B / 2 ^ 32))
    (hY : Y.toNat = A / 2 ^ 32 * (B % 2 ^ 32) / 2 ^ 32)
    (hZ : Z.toNat = A % 2 ^ 32 * (B / 2 ^ 32) / 2 ^ 32)
    (hu : u.toNat = A % 2 ^ 32 * (B % 2 ^ 32) / 2 ^ 32)
    (hv : v.toNat = A / 2 ^ 32 * (B % 2 ^ 32) % 2 ^ 32)
    (hw : w.toNat = A % 2 ^ 32 * (B / 2 ^ 32) % 2 ^ 32)
    (hmid : u.toNat + v.toNat + w.toNat < 2 ^ 64) :
    (X + Y + Z + ((u + v + w) >>> 32)).toNat = A * B / 2 ^ 64 := by
  -- the middle column, as exact arithmetic, then its carry out
  have hcarry : ((u + v + w) >>> 32).toNat
      = (A % 2 ^ 32 * (B % 2 ^ 32) / 2 ^ 32 + A / 2 ^ 32 * (B % 2 ^ 32) % 2 ^ 32
        + A % 2 ^ 32 * (B / 2 ^ 32) % 2 ^ 32) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, toNat_add3_of_lt hmid, hu, hv, hw]
  -- the limb identity, with the limbs of `A` and `B` reassembled
  have key := mulHi_limbs (A / 2 ^ 32) (A % 2 ^ 32) (B / 2 ^ 32) (B % 2 ^ 32)
  rw [Nat.div_add_mod' A (2 ^ 32), Nat.div_add_mod' B (2 ^ 32)] at key
  have hlt : A * B / 2 ^ 64 < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt hA hB)
  have hsum : X.toNat + Y.toNat + Z.toNat + ((u + v + w) >>> 32).toNat = A * B / 2 ^ 64 := by
    rw [hX, hY, hZ, hcarry, key]
  exact (toNat_add4_of_lt (by omega)).trans hsum

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
  simp only [mulHi64]
  -- the four limbs, and the four partial products they form
  have hAH : (a >>> 32).toNat < 2 ^ 32 := by rw [haHi]; exact hb32 _ ha
  have hAL : (a &&& (0xFFFFFFFF : UInt64)).toNat < 2 ^ 32 := by rw [haLo]; omega
  have hBH : (b >>> 32).toNat < 2 ^ 32 := by rw [hbHi]; exact hb32 _ hb
  have hBL : (b &&& (0xFFFFFFFF : UInt64)).toNat < 2 ^ 32 := by rw [hbLo]; omega
  have p11 := hprod _ _ hAH hBH
  have p10 := hprod _ _ hAH hBL
  have p01 := hprod _ _ hAL hBH
  have p00 := hprod _ _ hAL hBL
  -- each partial product's high and low halves
  have s10 : (((a >>> 32) * (b &&& (0xFFFFFFFF : UInt64))) >>> 32).toNat
      = (a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32)) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, p10, haHi, hbLo]
  have s01 : (((a &&& (0xFFFFFFFF : UInt64)) * (b >>> 32)) >>> 32).toNat
      = ((a.toNat % 2 ^ 32) * (b.toNat / 2 ^ 32)) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, p01, haLo, hbHi]
  have s00 : (((a &&& (0xFFFFFFFF : UInt64)) * (b &&& (0xFFFFFFFF : UInt64))) >>> 32).toNat
      = ((a.toNat % 2 ^ 32) * (b.toNat % 2 ^ 32)) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, p00, haLo, hbLo]
  have m10 : (((a >>> 32) * (b &&& (0xFFFFFFFF : UInt64))) &&& (0xFFFFFFFF : UInt64)).toNat
      = (a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32)) % 2 ^ 32 := by
    rw [toNat_and_low32, p10, haHi, hbLo]
  have m01 : (((a &&& (0xFFFFFFFF : UInt64)) * (b >>> 32)) &&& (0xFFFFFFFF : UInt64)).toNat
      = ((a.toNat % 2 ^ 32) * (b.toNat / 2 ^ 32)) % 2 ^ 32 := by
    rw [toNat_and_low32, p01, haLo, hbHi]
  -- the middle column, then the final sum; neither leaves its register
  have hmidlt : ((((a &&& (0xFFFFFFFF : UInt64)) * (b &&& (0xFFFFFFFF : UInt64))) >>> 32).toNat
      + (((a >>> 32) * (b &&& (0xFFFFFFFF : UInt64))) &&& (0xFFFFFFFF : UInt64)).toNat
      + (((a &&& (0xFFFFFFFF : UInt64)) * (b >>> 32)) &&& (0xFFFFFFFF : UInt64)).toNat)
        < 2 ^ 64 := by
    have h1 : ((a.toNat % 2 ^ 32) * (b.toNat % 2 ^ 32)) / 2 ^ 32 < 2 ^ 32 := by
      refine Nat.div_lt_of_lt_mul ?_
      calc (a.toNat % 2 ^ 32) * (b.toNat % 2 ^ 32) < 2 ^ 32 * 2 ^ 32 :=
            Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
        _ = 2 ^ 32 * 2 ^ 32 := rfl
    have h2 : (a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32)) % 2 ^ 32 < 2 ^ 32 :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have h3 : ((a.toNat % 2 ^ 32) * (b.toNat / 2 ^ 32)) % 2 ^ 32 < 2 ^ 32 :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [s00, m10, m01]; omega
  -- the top partial product, then the whole final column
  have t11 : ((a >>> 32) * (b >>> 32)).toNat = a.toNat / 2 ^ 32 * (b.toNat / 2 ^ 32) := by
    rw [p11, haHi, hbHi]
  exact toNat_finalColumn ha hb t11 s10 s01 s00 m10 m01 hmidlt

/-! ## The `63`-bit fixed-point conversion

`mtwop63` converts an `FPR` in `[0, 1)` to a `63`-bit fixed-point fraction. It reassembles the
significand into bits `62..10` of a register by a shift, an implicit-bit `|||`, and a mask, and
then rescales it by a right shift whose amount saturates at `63`. Both halves are exact: the
saturation bites only for operands below `2 ^ (-64)`, where the answer is `0` on either reading. -/

/-- Setting bit `k` of a value and then truncating to `k + 1` bits keeps the low `k` bits and
forces bit `k`. -/
private theorem or_two_pow_mod_two_pow_succ (A k : ℕ) :
    (A ||| 2 ^ k) % 2 ^ (k + 1) = A % 2 ^ k + 2 ^ k := by
  rw [← or_two_pow_add_of_lt _ k (Nat.mod_lt _ (Nat.two_pow_pos _))]
  refine Nat.eq_of_testBit_eq fun j => ?_
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy j k with h | h | h
  · simp [h, show j < k + 1 by omega, show ¬ k = j by omega]
  · subst h; simp
  · simp [show ¬ j < k by omega, show ¬ j < k + 1 by omega, show ¬ k = j by omega]

/-- Masking to six bits is the identity below `64`. -/
private theorem and_63_of_lt {n : ℕ} (h : n < 64) : n &&& 63 = n := by
  rw [show (63 : ℕ) = 2 ^ 6 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

/-- A value carrying all sixteen low bits saturates the six-bit mask. -/
private theorem and_63_or_65535 (n : ℕ) : (n ||| 65535) &&& 63 = 63 := by
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from by norm_num,
    show (63 : ℕ) = 2 ^ 6 - 1 from by norm_num]
  refine Nat.eq_of_testBit_eq fun j => ?_
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 6
  · simp [hj, show j < 16 from by omega]
  · simp [hj]

/-- The fraction word `mtwop63` builds before shifting: the operand's significand, scaled by
`2 ^ 10`. The sign bit is shifted out and the implicit-bit `|||` overwrites the one exponent bit
that survives, so no field of the operand other than its mantissa reaches the result. -/
private theorem toNat_m_of (x : FPR) :
    ((((x <<< 10) ||| ((1 : UInt64) <<< 62)) &&& M63)).toNat
      = 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52) := by
  have hM63 : (M63 : UInt64).toNat = 2 ^ 63 - 1 := by decide
  have hbit : ((1 : UInt64) <<< 62).toNat = 2 ^ 62 := by decide
  have hshl : (x <<< (10 : UInt64)).toNat = x.toNat * 2 ^ 10 % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft, show ((10 : UInt64).toNat % 64) = 10 from by decide,
      Nat.shiftLeft_eq]
  rw [UInt64.toNat_and, hM63, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_or, hbit,
    show (63 : ℕ) = 62 + 1 from rfl, or_two_pow_mod_two_pow_succ, hshl,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : (62 : ℕ) ≤ 64)),
    show (2 : ℕ) ^ 62 = 2 ^ 52 * 2 ^ 10 from by norm_num, Nat.mul_mod_mul_right]
  unfold FPR.decode
  ring

/-- The shift amount `mtwop63` derives from `e`: the true gap when it fits in six bits, and a
saturated `63` otherwise. Beyond `63` the `UInt32` subtraction `63 - e` wraps, and the top half of
the wrapped value fills all six low bits of the mask. -/
private theorem toNat_ue_of (e : UInt32) (he : e.toNat < 2 ^ 16) :
    ((e ||| ((63 - e) >>> 16)) &&& 63).toNat = min e.toNat 63 := by
  have h63 : (63 : UInt32).toNat = 63 := by decide
  have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
  rw [UInt32.toNat_and, UInt32.toNat_or, h63, UInt32.toNat_shiftRight, h16,
    Nat.shiftRight_eq_div_pow]
  rcases le_or_gt e.toNat 63 with h | h
  · have hsub : ((63 : UInt32) - e).toNat = 63 - e.toNat := by
      rw [toNat_sub_of_le_uint32 (by rw [h63]; exact h), h63]
    rw [hsub, Nat.div_eq_of_lt (show 63 - e.toNat < 2 ^ 16 by omega), Nat.or_zero,
      and_63_of_lt (by omega), min_eq_left h]
  · have hsub : ((63 : UInt32) - e).toNat = 2 ^ 32 - e.toNat + 63 := by
      rw [UInt32.toNat_sub, h63]
      exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (2 ^ 32 - e.toNat + 63) / 2 ^ 16 = 65535 :=
      Nat.div_eq_of_lt_le (by norm_num; omega) (by norm_num; omega)
    rw [hsub, hdiv, and_63_or_65535, min_eq_right h.le]

/-- The final shift of `mtwop63`, read as a division. -/
private theorem toNat_shiftRight_ue {m : UInt64} {e : UInt32} {k : ℕ} (he : e.toNat = k)
    (hk : k < 2 ^ 16) :
    (m >>> (((e ||| ((63 - e) >>> 16)) &&& 63).toUInt64)).toNat = m.toNat / 2 ^ min k 63 := by
  have hue : ((e ||| ((63 - e) >>> 16)) &&& 63).toNat = min k 63 := by
    rw [toNat_ue_of e (by omega), he]
  rw [UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, hue, Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow]

/-- The exponent word `mtwop63` forms: the true gap `1022 - ex`, with no wraparound. -/
private theorem toNat_e_of (x : FPR) (hexle : (FPR.decode x).exponent ≤ 1022) :
    ((1022 : UInt32) - ((x >>> 52).toUInt32 &&& 0x7FF)).toNat
      = 1022 - (FPR.decode x).exponent := by
  have hfield : ((x >>> 52).toUInt32 &&& 0x7FF).toNat = (FPR.decode x).exponent :=
    toNat_ex_field_of x
  have h1022 : (1022 : UInt32).toNat = 1022 := by decide
  rw [toNat_sub_of_le_uint32 (by rw [hfield, h1022]; exact hexle), hfield, h1022]

/-- `mtwop63`, read as exact arithmetic on `ℕ`: the significand scaled by `2 ^ 10`, divided by
`2 ^ (1022 - ex)` with the shift amount saturated at `63`. -/
private theorem toNat_mtwop63_aux (x : FPR) (hexle : (FPR.decode x).exponent ≤ 1022) :
    (mtwop63 x).toNat = 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52)
      / 2 ^ min (1022 - (FPR.decode x).exponent) 63 := by
  simp only [mtwop63]
  rw [toNat_shiftRight_ue (toNat_e_of x hexle) (by omega), toNat_m_of]

/-- A normal operand with nonnegative value denotes `significand * 2 ^ (ex - 1075)`: the sign bit
is clear, so the case split in `FPR.Bits.toReal` collapses. -/
private theorem toReal_eq_significand_of_nonneg (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) :
    toReal x = (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ)
      * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by
  obtain ⟨hne0, hne2047⟩ := hn
  have hsig : (FPR.decode x).significand = (FPR.decode x).mantissa + 2 ^ 52 := by
    unfold FPR.Bits.significand
    rw [if_neg hne0]
  have hkey := toReal_eq_significand_mul_two_zpow hne0 hne2047
  rw [hsig] at hkey
  change toReal x = _ at hkey
  have hpos : (0 : ℝ) < (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ) := by
    have h : 0 < (FPR.decode x).mantissa + 2 ^ 52 := by omega
    exact_mod_cast h
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by positivity
  by_cases hs : (FPR.decode x).sign = true
  · rw [hkey, if_pos hs] at h0
    nlinarith
  · rw [hkey, if_neg hs]
    ring

/-- An operand below `1` has biased exponent at most `1022`: with the implicit leading bit, an
exponent field of `1023` already denotes a value of at least `1`. -/
private theorem exponent_le_of_toReal_lt_one (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) (h1 : toReal x < 1) : (FPR.decode x).exponent ≤ 1022 := by
  by_contra hcon
  have hc : 1022 < (FPR.decode x).exponent := by omega
  rw [toReal_eq_significand_of_nonneg x hn h0] at h1
  have hsig : (2 : ℝ) ^ (52 : ℕ) ≤ (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ) := by
    have h : (2 : ℕ) ^ 52 ≤ (FPR.decode x).mantissa + 2 ^ 52 := by omega
    exact_mod_cast h
  have hz : (2 : ℝ) ^ ((1023 : ℤ) - 1075)
      ≤ (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ ((1023 : ℤ) - 1075) := by positivity
  have hone : (2 : ℝ) ^ (52 : ℕ) * (2 : ℝ) ^ ((1023 : ℤ) - 1075) = 1 := by
    rw [show ((1023 : ℤ) - 1075) = (-52 : ℤ) from by norm_num,
      ← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  nlinarith [mul_le_mul hsig hz hzpos.le (by positivity : (0 : ℝ) ≤
    (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ))]

/-- The exact value `mtwop63` is asked for, as a quotient of naturals. -/
private theorem floor_two_pow_63_mul_toReal (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) (h1 : toReal x < 1) :
    ⌊(2 : ℝ) ^ 63 * toReal x⌋₊ = 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52)
      / 2 ^ (1022 - (FPR.decode x).exponent) := by
  have hexle := exponent_le_of_toReal_lt_one x hn h0 h1
  have hexz : ((1022 - (FPR.decode x).exponent : ℕ) : ℤ)
      = (1022 : ℤ) - ((FPR.decode x).exponent : ℤ) := by omega
  have hcast : ((2 ^ (1022 - (FPR.decode x).exponent) : ℕ) : ℝ)
      = (2 : ℝ) ^ ((1022 : ℤ) - ((FPR.decode x).exponent : ℤ)) := by
    rw [← hexz, zpow_natCast]
    push_cast
    ring
  have hval : (2 : ℝ) ^ 63 * toReal x
      = ((2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52) : ℕ) : ℝ)
        / ((2 ^ (1022 - (FPR.decode x).exponent) : ℕ) : ℝ) := by
    rw [toReal_eq_significand_of_nonneg x hn h0, eq_div_iff (by positivity), hcast]
    have hexp : (2 : ℝ) ^ (63 : ℕ) * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075)
        * (2 : ℝ) ^ ((1022 : ℤ) - ((FPR.decode x).exponent : ℤ)) = (2 : ℝ) ^ (10 : ℕ) := by
      rw [← zpow_natCast (2 : ℝ) 63, ← zpow_natCast (2 : ℝ) 10,
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring
    push_cast
    linear_combination (((FPR.decode x).mantissa : ℝ) + 2 ^ 52) * hexp
  rw [hval, Nat.floor_div_natCast, Nat.floor_natCast]

/-- `mtwop63` converts an `FPR` in `[0, 1)` to a `63`-bit fixed-point fraction: it computes
`⌊2 ^ 63 * toReal x⌋`, exactly and with no rounding of its own. -/
private theorem toNat_mtwop63 (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) (h1 : toReal x < 1) :
    (mtwop63 x).toNat = ⌊(2 : ℝ) ^ 63 * toReal x⌋₊ := by
  have hexle := exponent_le_of_toReal_lt_one x hn h0 h1
  have hmanlt : (FPR.decode x).mantissa < 2 ^ 52 := FPR.decode_mantissa_lt x
  rw [floor_two_pow_63_mul_toReal x hn h0 h1, toNat_mtwop63_aux x hexle]
  rcases le_or_gt (1022 - (FPR.decode x).exponent) 63 with h | h
  · rw [min_eq_left h]
  · have hN : 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52) < 2 ^ 63 := by omega
    have hD : (2 : ℕ) ^ 63 ≤ 2 ^ (1022 - (FPR.decode x).exponent) :=
      Nat.pow_le_pow_right (by norm_num) h.le
    rw [min_eq_right h.le, Nat.div_eq_of_lt hN, Nat.div_eq_of_lt (lt_of_lt_of_le hN hD)]

/-! ## The Horner pipeline

`expm_p63` evaluates the FACCT coefficient table by Horner's rule in `UInt64` fixed point and then
applies a second `mtwop63` reading as a scale. Every step truncates, since `mulHi64` keeps only the
high half of a `128`-bit product. This section reads the loop as the exact real Horner recurrence
`hornerExact` on the same coefficients at the same quantised argument, and bounds the accumulated
truncation.

The bound is a fixed point of the step estimate `e ↦ ζ * e + 1`: one unit of fresh truncation per
step, on top of the incoming error scaled by the argument `ζ`, which `mtwop63` pins below `0.694`.
The same estimate also shows the `UInt64` subtraction `facctCoeffs[i] - mulHi64 z y` never wraps —
in fact `mulHi64 z y ≤ y` outright, so the wrap-freedom needs no numeric input at all. -/

/-- The fixed-point reading of `mtwop63 v <<< 1` as a real in `[0, 1)`. Both the polynomial's
argument `z` and its final scale `w` take this form. -/
private noncomputable def scaledArg (v : FPR) : ℝ := (((mtwop63 v) <<< 1).toNat : ℝ) / 2 ^ 64

/-- The `UInt64` Horner sequence that `expm_p63`'s loop computes. -/
private def hornerMachine (z : UInt64) : ℕ → UInt64
  | 0 => facctCoeffs[0]!
  | (i + 1) => facctCoeffs[i + 1]! - mulHi64 z (hornerMachine z i)

/-- The exact real Horner sequence on the same coefficients at the same quantised argument: the
value `hornerMachine` would compute if `mulHi64` did not truncate. -/
private noncomputable def hornerExact (ζ : ℝ) : ℕ → ℝ
  | 0 => ((facctCoeffs[0]!).toNat : ℝ)
  | (i + 1) => ((facctCoeffs[i + 1]!).toNat : ℝ) - ζ * hornerExact ζ i

/-- `expm_p63`'s loop, unrolled: its twelve iterations are exactly `hornerMachine`. -/
private theorem expm_p63_eq (x ccs : FPR) :
    expm_p63 x ccs = mulHi64 ((mtwop63 ccs) <<< 1) (hornerMachine ((mtwop63 x) <<< 1) 12) := by
  simp only [expm_p63, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    show ((Std.Legacy.Range.mk 1 facctCoeffs.size 1 (by decide)).size) = 12 from by decide,
    List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, hornerMachine]
  rfl

/-- `mulHi64` never exceeds its second operand: the high half of `a * b` is at most `b`, whatever
`a` is. This alone rules out wraparound in the loop's subtraction. -/
private theorem toNat_mulHi64_le (a b : UInt64) : (mulHi64 a b).toNat ≤ b.toNat := by
  rw [toNat_mulHi64]
  calc a.toNat * b.toNat / 2 ^ 64 ≤ 2 ^ 64 * b.toNat / 2 ^ 64 :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ a.toNat_lt_size.le)
    _ = b.toNat := Nat.mul_div_cancel_left _ (by norm_num)

/-- `mulHi64 a b` is `⌊(a / 2 ^ 64) * b⌋`: the fixed-point product, truncated by less than one. -/
private theorem mulHi64_bracket (a b : UInt64) :
    ((mulHi64 a b).toNat : ℝ) ≤ (a.toNat : ℝ) / 2 ^ 64 * (b.toNat : ℝ) ∧
      (a.toNat : ℝ) / 2 ^ 64 * (b.toNat : ℝ) < ((mulHi64 a b).toNat : ℝ) + 1 := by
  have hval : (a.toNat : ℝ) / 2 ^ 64 * (b.toNat : ℝ)
      = ((a.toNat * b.toNat : ℕ) : ℝ) / ((2 ^ 64 : ℕ) : ℝ) := by push_cast; ring
  have hfl : ((mulHi64 a b).toNat : ℝ)
      = ((⌊((a.toNat * b.toNat : ℕ) : ℝ) / ((2 ^ 64 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) := by
    rw [Nat.floor_div_eq_div, toNat_mulHi64]
  rw [hval, hfl]
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- The coefficient table is nondecreasing, so a bound at one index carries to the next. -/
private theorem facctCoeffs_mono {i : ℕ} (hi : i < 12) :
    (facctCoeffs[i]!).toNat ≤ (facctCoeffs[i + 1]!).toNat := by
  interval_cases i <;> decide

/-- One Horner step. The `UInt64` subtraction cannot wrap, since `mulHi64 z y ≤ y ≤ c`; and the
step's own truncation costs at most `1`, on top of the incoming error scaled by `ζ`. -/
private theorem horner_step {z y c : UInt64} {Y ζ : ℝ}
    (hζ : ζ = (z.toNat : ℝ) / 2 ^ 64) (hζ1 : ζ ≤ 694 / 1000)
    (hyc : y.toNat ≤ c.toNat) (hy : |(y.toNat : ℝ) - Y| ≤ 4) :
    (c - mulHi64 z y).toNat ≤ c.toNat ∧
      |((c - mulHi64 z y).toNat : ℝ) - ((c.toNat : ℝ) - ζ * Y)| ≤ 4 := by
  have hmc : (mulHi64 z y).toNat ≤ c.toNat := le_trans (toNat_mulHi64_le z y) hyc
  have hsub : (c - mulHi64 z y).toNat = c.toNat - (mulHi64 z y).toNat :=
    toNat_sub_of_le_uint64 c _ hmc
  refine ⟨by omega, ?_⟩
  obtain ⟨hb1, hb2⟩ := mulHi64_bracket z y
  rw [← hζ] at hb1 hb2
  have hζ0 : 0 ≤ ζ := by rw [hζ]; positivity
  rw [hsub, Nat.cast_sub hmc,
    show (c.toNat : ℝ) - ((mulHi64 z y).toNat : ℝ) - ((c.toNat : ℝ) - ζ * Y)
      = ζ * Y - ((mulHi64 z y).toNat : ℝ) from by ring, abs_le]
  rw [abs_le] at hy
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hy.2 hζ0],
    by nlinarith [mul_le_mul_of_nonneg_left hy.1 hζ0]⟩

/-- The loop invariant: each iterate stays under its own coefficient — so the next subtraction
cannot wrap — and tracks the exact recurrence to within `4`. -/
private theorem hornerMachine_error {z : UInt64} {ζ : ℝ}
    (hζ : ζ = (z.toNat : ℝ) / 2 ^ 64) (hζ1 : ζ ≤ 694 / 1000) :
    ∀ i, i ≤ 12 → (hornerMachine z i).toNat ≤ (facctCoeffs[i]!).toNat ∧
      |((hornerMachine z i).toNat : ℝ) - hornerExact ζ i| ≤ 4 := by
  intro i
  induction i with
  | zero => intro _; simp [hornerMachine, hornerExact]
  | succ k ih =>
    intro hk
    obtain ⟨hle, herr⟩ := ih (by omega)
    have hstep := horner_step hζ hζ1 (le_trans hle (facctCoeffs_mono (by omega))) herr
    rw [show hornerMachine z (k + 1)
        = facctCoeffs[k + 1]! - mulHi64 z (hornerMachine z k) from rfl,
      show hornerExact ζ (k + 1)
        = ((facctCoeffs[k + 1]!).toNat : ℝ) - ζ * hornerExact ζ k from rfl]
    exact hstep

/-- `scaledArg` lands in `[0, 1]`, which is all the final scaling multiply needs of it. -/
private theorem scaledArg_nonneg (v : FPR) : 0 ≤ scaledArg v := by
  unfold scaledArg; positivity

private theorem scaledArg_le_one (v : FPR) : scaledArg v ≤ 1 := by
  unfold scaledArg
  rw [div_le_one (by norm_num)]
  exact_mod_cast ((mtwop63 v) <<< 1).toNat_lt_size.le

/-- `mtwop63 x <<< 1` reads `2 ^ 64 * toReal x` rounded down, so `scaledArg x` never exceeds
`toReal x`. -/
private theorem scaledArg_le_toReal (x : FPR) (hn : FPR.IsNormal x) (h0 : 0 ≤ toReal x)
    (h1 : toReal x < 1) : scaledArg x ≤ toReal x := by
  have hm : (mtwop63 x).toNat = ⌊(2 : ℝ) ^ 63 * toReal x⌋₊ := toNat_mtwop63 x hn h0 h1
  have hlt : (mtwop63 x).toNat < 2 ^ 63 := by
    rw [hm]
    exact (Nat.floor_lt (by positivity)).mpr (by push_cast; nlinarith)
  have hsh : ((mtwop63 x) <<< 1).toNat = (mtwop63 x).toNat * 2 := by
    rw [toNat_shiftLeft_one]
    exact Nat.mod_eq_of_lt (by omega)
  have hfl : ((mtwop63 x).toNat : ℝ) ≤ (2 : ℝ) ^ 63 * toReal x := by
    rw [hm]; exact Nat.floor_le (by positivity)
  unfold scaledArg
  rw [hsh, div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 64)]
  push_cast
  nlinarith

/-- On `expm_p63`'s documented domain the argument is below `0.694`, the contraction factor the
error induction runs on. -/
private theorem scaledArg_le_694 (x : FPR) (hn : FPR.IsNormal x) (h0 : 0 ≤ toReal x)
    (hlog : toReal x < Real.log 2) : scaledArg x ≤ 694 / 1000 := by
  have hlog9 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h1 : toReal x < 1 := by norm_num at hlog9; linarith
  have := scaledArg_le_toReal x hn h0 h1
  norm_num at hlog9 ⊢
  linarith

/-- **(a)** Every Horner iterate of the fixed-point loop tracks the exact real recurrence at the
same quantised argument to within `4`. -/
private theorem hornerMachine_sub_hornerExact_le (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) (hlog : toReal x < Real.log 2) (i : ℕ) (hi : i ≤ 12) :
    |((hornerMachine ((mtwop63 x) <<< 1) i).toNat : ℝ) - hornerExact (scaledArg x) i| ≤ 4 :=
  (hornerMachine_error rfl (scaledArg_le_694 x hn h0 hlog) i hi).2

/-- The loop's `UInt64` subtractions never wrap: every iterate stays below its own coefficient. -/
private theorem hornerMachine_le_coeff (x : FPR) (hn : FPR.IsNormal x) (h0 : 0 ≤ toReal x)
    (hlog : toReal x < Real.log 2) (i : ℕ) (hi : i ≤ 12) :
    (hornerMachine ((mtwop63 x) <<< 1) i).toNat ≤ (facctCoeffs[i]!).toNat :=
  (hornerMachine_error rfl (scaledArg_le_694 x hn h0 hlog) i hi).1

/-- **(b)** The whole pipeline, including the final scaling multiply: `expm_p63 x ccs` tracks
`scaledArg ccs * hornerExact (scaledArg x) 12` to within `5`. -/
private theorem expm_p63_sub_exact_le (x ccs : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) (hlog : toReal x < Real.log 2) :
    |((expm_p63 x ccs).toNat : ℝ) - scaledArg ccs * hornerExact (scaledArg x) 12| ≤ 5 := by
  have hy := hornerMachine_sub_hornerExact_le x hn h0 hlog 12 le_rfl
  obtain ⟨hb1, hb2⟩ := mulHi64_bracket ((mtwop63 ccs) <<< 1) (hornerMachine ((mtwop63 x) <<< 1) 12)
  rw [show (((mtwop63 ccs) <<< 1).toNat : ℝ) / 2 ^ 64 = scaledArg ccs from rfl] at hb1 hb2
  have hs0 := scaledArg_nonneg ccs
  have hs1 := scaledArg_le_one ccs
  rw [expm_p63_eq, abs_le]
  rw [abs_le] at hy
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hy.1 hs0],
    by nlinarith [mul_le_mul_of_nonneg_left hy.2 hs0]⟩

/-! ## From the quantised arguments to the true ones

The bounds above are stated at `scaledArg x` and `scaledArg ccs`, the arguments the machine
actually uses. Because `mtwop63` is exact, each differs from the operand it stands for by a pure
floor error below `2 ^ (-63)`, and transporting the bound across that gap costs a little over one
unit at each of the two places an argument enters: through the polynomial's argument, where the
Lipschitz constant is about `2 ^ 63`, and through the final scale, where the polynomial's own
magnitude is about `2 ^ 63`. -/

private theorem two_zpow_neg_63 : (2 : ℝ) ^ (-63 : ℤ) = 1 / 2 ^ (63 : ℕ) := by norm_num

/-- `scaledArg v` is exactly `⌊2 ^ 63 * toReal v⌋ / 2 ^ 63`: the shift by one cannot overflow, so
the doubling cancels one power of two against the `2 ^ 64` scale. -/
private theorem scaledArg_eq (v : FPR) (hn : FPR.IsNormal v) (h0 : 0 ≤ toReal v)
    (h1 : toReal v < 1) :
    scaledArg v = ((⌊(2 : ℝ) ^ 63 * toReal v⌋₊ : ℕ) : ℝ) / 2 ^ 63 := by
  have hm : (mtwop63 v).toNat = ⌊(2 : ℝ) ^ 63 * toReal v⌋₊ := toNat_mtwop63 v hn h0 h1
  have hlt : (mtwop63 v).toNat < 2 ^ 63 := by
    rw [hm]
    exact (Nat.floor_lt (by positivity)).mpr (by push_cast; nlinarith)
  have hsh : ((mtwop63 v) <<< 1).toNat = (mtwop63 v).toNat * 2 := by
    rw [toNat_shiftLeft_one]
    exact Nat.mod_eq_of_lt (by omega)
  unfold scaledArg
  rw [hsh, hm]
  push_cast
  ring

/-- **(1)** The quantisation gap: `scaledArg v` sits within `2 ^ (-63)` below `toReal v`. -/
private theorem scaledArg_bracket (v : FPR) (hn : FPR.IsNormal v)
    (h0 : 0 ≤ toReal v) (h1 : toReal v < 1) :
    scaledArg v ≤ toReal v ∧ toReal v < scaledArg v + (2 : ℝ) ^ (-63 : ℤ) := by
  refine ⟨scaledArg_le_toReal v hn h0 h1, ?_⟩
  have hfl := Nat.lt_floor_add_one ((2 : ℝ) ^ 63 * toReal v)
  rw [scaledArg_eq v hn h0 h1, two_zpow_neg_63,
    show ((⌊(2 : ℝ) ^ 63 * toReal v⌋₊ : ℕ) : ℝ) / 2 ^ (63 : ℕ) + 1 / 2 ^ (63 : ℕ)
      = (((⌊(2 : ℝ) ^ 63 * toReal v⌋₊ : ℕ) : ℝ) + 1) / 2 ^ (63 : ℕ) from by ring,
    lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (63 : ℕ))]
  linarith

/-- Every coefficient fits in `63` bits. -/
private theorem facctCoeffs_le {i : ℕ} (hi : i ≤ 12) : (facctCoeffs[i]!).toNat ≤ 2 ^ 63 := by
  interval_cases i <;> decide

/-- The exact Horner iterates stay in `[0, facctCoeffs[i]]`: nonnegative because the table grows
faster than the argument shrinks it, and bounded by the coefficient because the subtracted term is
nonnegative. -/
private theorem hornerExact_mem (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 694 / 1000) :
    ∀ i, i ≤ 12 → 0 ≤ hornerExact t i ∧ hornerExact t i ≤ ((facctCoeffs[i]!).toNat : ℝ) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [show hornerExact t 0 = ((facctCoeffs[0]!).toNat : ℝ) from rfl]
    exact ⟨Nat.cast_nonneg _, le_rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hlo, hhi⟩ := ih (by omega)
    have hmono : ((facctCoeffs[k]!).toNat : ℝ) ≤ ((facctCoeffs[k + 1]!).toNat : ℝ) :=
      Nat.cast_le.mpr (facctCoeffs_mono (by omega))
    have hprod : t * hornerExact t k ≤ 694 / 1000 * ((facctCoeffs[k]!).toNat : ℝ) :=
      mul_le_mul ht1 hhi hlo (by norm_num)
    have hck : (0 : ℝ) ≤ ((facctCoeffs[k]!).toNat : ℝ) := Nat.cast_nonneg _
    rw [show hornerExact t (k + 1)
      = ((facctCoeffs[k + 1]!).toNat : ℝ) - t * hornerExact t k from rfl]
    exact ⟨by linarith, by nlinarith [mul_nonneg ht0 hlo]⟩

/-- The exact Horner iterates never exceed `2 ^ 63` in magnitude. -/
private theorem hornerExact_abs_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 694 / 1000) (i : ℕ)
    (hi : i ≤ 12) : |hornerExact t i| ≤ 2 ^ 63 := by
  obtain ⟨hlo, hhi⟩ := hornerExact_mem t ht0 ht1 i hi
  rw [abs_of_nonneg hlo]
  exact le_trans hhi (by exact_mod_cast facctCoeffs_le hi)

/-- **(2)** The exact Horner sequence is Lipschitz in its argument, with constant `2 ^ 65`. The
step estimate is `d ↦ t * d + 2 ^ 63`, whose fixed point needs a constant at least
`2 ^ 63 / (1 - 0.694) ≈ 3.27 * 2 ^ 63`; `2 ^ 65` is the next power of two above that, and closes
the induction since `0.694 * 4 + 1 ≤ 4`. -/
private theorem hornerExact_lipschitz (s t : ℝ) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs1 : s ≤ 694 / 1000) (ht1 : t ≤ 694 / 1000) :
    ∀ i, i ≤ 12 → |hornerExact s i - hornerExact t i| ≤ (2 : ℝ) ^ 65 * |s - t| := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [show hornerExact s 0 = ((facctCoeffs[0]!).toNat : ℝ) from rfl,
      show hornerExact t 0 = ((facctCoeffs[0]!).toNat : ℝ) from rfl, sub_self, abs_zero]
    positivity
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hmag := hornerExact_abs_le t ht0 ht1 k (by omega)
    have hkey : hornerExact s (k + 1) - hornerExact t (k + 1)
        = (t - s) * hornerExact t k + s * (hornerExact t k - hornerExact s k) := by
      rw [show hornerExact s (k + 1)
          = ((facctCoeffs[k + 1]!).toNat : ℝ) - s * hornerExact s k from rfl,
        show hornerExact t (k + 1)
          = ((facctCoeffs[k + 1]!).toNat : ℝ) - t * hornerExact t k from rfl]
      ring
    have h1 : |(t - s) * hornerExact t k| ≤ |s - t| * 2 ^ 63 := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hmag (abs_nonneg _)
    have h2 : |s * (hornerExact t k - hornerExact s k)|
        ≤ 694 / 1000 * ((2 : ℝ) ^ 65 * |s - t|) := by
      rw [abs_mul, abs_of_nonneg hs0, abs_sub_comm]
      exact mul_le_mul hs1 ihk (abs_nonneg _) (by norm_num)
    calc |hornerExact s (k + 1) - hornerExact t (k + 1)|
        ≤ |(t - s) * hornerExact t k| + |s * (hornerExact t k - hornerExact s k)| := by
          rw [hkey]; exact abs_add_le _ _
      _ ≤ |s - t| * 2 ^ 63 + 694 / 1000 * ((2 : ℝ) ^ 65 * |s - t|) := add_le_add h1 h2
      _ ≤ (2 : ℝ) ^ 65 * |s - t| := by nlinarith [abs_nonneg (s - t)]

/-- **(3)** The whole fixed-point pipeline against the exact polynomial at the *true* operands.
The two quantisation gaps contribute `2 ^ 65 * 2 ^ (-63) = 4` through the argument and
`2 ^ (-63) * 2 ^ 63 = 1` through the scale, on top of the truncation bound `5`. -/
private theorem expm_p63_sub_trueArg_le (x ccs : FPR)
    (hn : FPR.IsNormal x) (h0 : 0 ≤ toReal x) (hlog : toReal x < Real.log 2)
    (hcn : FPR.IsNormal ccs) (hc0 : 0 ≤ toReal ccs) (hc1 : toReal ccs < 1) :
    |((expm_p63 x ccs).toNat : ℝ) - toReal ccs * hornerExact (toReal x) 12| ≤ 10 := by
  have h9 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  norm_num at h9
  have hx1 : toReal x < 1 := by linarith
  have hxle : toReal x ≤ 694 / 1000 := by linarith
  have hsx := scaledArg_bracket x hn h0 hx1
  have hsc := scaledArg_bracket ccs hcn hc0 hc1
  rw [two_zpow_neg_63] at hsx hsc
  have hmain := expm_p63_sub_exact_le x ccs hn h0 hlog
  have hLip := hornerExact_lipschitz (scaledArg x) (toReal x) (scaledArg_nonneg x) h0
    (scaledArg_le_694 x hn h0 hlog) hxle 12 le_rfl
  have hmag := hornerExact_abs_le (toReal x) h0 hxle 12 le_rfl
  have hdx : |scaledArg x - toReal x| ≤ 1 / 2 ^ (63 : ℕ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hsx.1])]
    linarith [hsx.2]
  have hdc : |scaledArg ccs - toReal ccs| ≤ 1 / 2 ^ (63 : ℕ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hsc.1])]
    linarith [hsc.2]
  have hHd : |hornerExact (scaledArg x) 12 - hornerExact (toReal x) 12| ≤ 4 :=
    le_trans hLip (by
      calc (2 : ℝ) ^ 65 * |scaledArg x - toReal x|
          ≤ (2 : ℝ) ^ 65 * (1 / 2 ^ (63 : ℕ)) := mul_le_mul_of_nonneg_left hdx (by positivity)
        _ = 4 := by norm_num)
  have hkey : |scaledArg ccs * hornerExact (scaledArg x) 12
      - toReal ccs * hornerExact (toReal x) 12| ≤ 5 := by
    calc |scaledArg ccs * hornerExact (scaledArg x) 12
            - toReal ccs * hornerExact (toReal x) 12|
        ≤ |scaledArg ccs * (hornerExact (scaledArg x) 12 - hornerExact (toReal x) 12)|
          + |(scaledArg ccs - toReal ccs) * hornerExact (toReal x) 12| := by
          rw [show scaledArg ccs * hornerExact (scaledArg x) 12
              - toReal ccs * hornerExact (toReal x) 12
              = scaledArg ccs * (hornerExact (scaledArg x) 12 - hornerExact (toReal x) 12)
                + (scaledArg ccs - toReal ccs) * hornerExact (toReal x) 12 from by ring]
          exact abs_add_le _ _
      _ ≤ 1 * 4 + 1 / 2 ^ (63 : ℕ) * 2 ^ 63 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (scaledArg_nonneg ccs)]
          exact add_le_add
            (mul_le_mul (scaledArg_le_one ccs) hHd (abs_nonneg _) (by norm_num))
            (mul_le_mul hdc hmag (abs_nonneg _) (by positivity))
      _ = 5 := by norm_num
  calc |((expm_p63 x ccs).toNat : ℝ) - toReal ccs * hornerExact (toReal x) 12|
      ≤ |((expm_p63 x ccs).toNat : ℝ) - scaledArg ccs * hornerExact (scaledArg x) 12|
        + |scaledArg ccs * hornerExact (scaledArg x) 12
          - toReal ccs * hornerExact (toReal x) 12| := abs_sub_le _ _ _
    _ ≤ 5 + 5 := add_le_add hmain hkey
    _ = 10 := by norm_num

/-! ## Certifying the coefficient polynomial

The remaining obligation is `sup |certQ|` over `[0, log 2)`, where `certQ` is the exact Horner
polynomial measured against a degree-18 Taylor truncation of `exp (-x)`, in units of `2 ^ (-63)`.
`facctCoeffs` is a minimax fit, so `certQ` is `O(1)` in these units while its coefficients are
`O(2 ^ 63)`: every bound that applies a triangle inequality to coefficients discards exactly the
cancellation that makes the fit good, and misses by orders of magnitude.

What survives is subdivision in a Chebyshev basis. On a subinterval parameterised by
`x = (p + q * y) / s` with `y ∈ [-1, 1]`, writing `D * certQ` as `∑ j, N j * T j y` gives
`|certQ| ≤ (∑ j, |N j|) / D` from `|T j y| ≤ 1` alone, and the cancellation is carried by the
coefficients rather than thrown away.

Two things make the certificates cheap. The interval endpoints are *dyadic*, so `s` is a power of
two and the cleared coefficients stay near 60 digits rather than the ~330 that equal subdivision
of `[0, r]` by a decimal `r` would force; and `certQ_expand` clears `18!` once, so every
per-certificate identity is a polynomial identity over `ℤ` with no division. -/

/-- Monomial form of `Chebyshev.T` at the reals, degree 0. -/
private theorem chebEval0 (y : ℝ) : (Chebyshev.T ℝ (0 : ℤ)).eval y = 1 := by
  simp [Chebyshev.T_zero]

private theorem chebEval1 (y : ℝ) : (Chebyshev.T ℝ (1 : ℤ)).eval y = y := by
  simp [Chebyshev.T_one]

private theorem chebEval2 (y : ℝ) : (Chebyshev.T ℝ (2 : ℤ)).eval y =
    (-1) + 2 * y ^ 2
    := by
  rw [show (2 : ℤ) = 0 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (0 : ℤ) + 1 = 1 from by norm_num,
    chebEval1, chebEval0]
  ring

private theorem chebEval3 (y : ℝ) : (Chebyshev.T ℝ (3 : ℤ)).eval y =
    (-3) * y + 4 * y ^ 3
    := by
  rw [show (3 : ℤ) = 1 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (1 : ℤ) + 1 = 2 from by norm_num,
    chebEval2, chebEval1]
  ring

private theorem chebEval4 (y : ℝ) : (Chebyshev.T ℝ (4 : ℤ)).eval y =
    1 + (-8) * y ^ 2 + 8 * y ^ 4
    := by
  rw [show (4 : ℤ) = 2 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (2 : ℤ) + 1 = 3 from by norm_num,
    chebEval3, chebEval2]
  ring

private theorem chebEval5 (y : ℝ) : (Chebyshev.T ℝ (5 : ℤ)).eval y =
    5 * y + (-20) * y ^ 3 + 16 * y ^ 5
    := by
  rw [show (5 : ℤ) = 3 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (3 : ℤ) + 1 = 4 from by norm_num,
    chebEval4, chebEval3]
  ring

private theorem chebEval6 (y : ℝ) : (Chebyshev.T ℝ (6 : ℤ)).eval y =
    (-1) + 18 * y ^ 2 + (-48) * y ^ 4 + 32 * y ^ 6
    := by
  rw [show (6 : ℤ) = 4 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (4 : ℤ) + 1 = 5 from by norm_num,
    chebEval5, chebEval4]
  ring

private theorem chebEval7 (y : ℝ) : (Chebyshev.T ℝ (7 : ℤ)).eval y =
    (-7) * y + 56 * y ^ 3 + (-112) * y ^ 5 + 64 * y ^ 7
    := by
  rw [show (7 : ℤ) = 5 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (5 : ℤ) + 1 = 6 from by norm_num,
    chebEval6, chebEval5]
  ring

private theorem chebEval8 (y : ℝ) : (Chebyshev.T ℝ (8 : ℤ)).eval y =
    1 + (-32) * y ^ 2 + 160 * y ^ 4 + (-256) * y ^ 6 + 128 * y ^ 8
    := by
  rw [show (8 : ℤ) = 6 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (6 : ℤ) + 1 = 7 from by norm_num,
    chebEval7, chebEval6]
  ring

private theorem chebEval9 (y : ℝ) : (Chebyshev.T ℝ (9 : ℤ)).eval y =
    9 * y + (-120) * y ^ 3 + 432 * y ^ 5 + (-576) * y ^ 7 + 256 * y ^ 9
    := by
  rw [show (9 : ℤ) = 7 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (7 : ℤ) + 1 = 8 from by norm_num,
    chebEval8, chebEval7]
  ring

private theorem chebEval10 (y : ℝ) : (Chebyshev.T ℝ (10 : ℤ)).eval y =
    (-1) + 50 * y ^ 2 + (-400) * y ^ 4 + 1120 * y ^ 6 + (-1280) * y ^ 8 + 512 * y ^ 10
    := by
  rw [show (10 : ℤ) = 8 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (8 : ℤ) + 1 = 9 from by norm_num,
    chebEval9, chebEval8]
  ring

private theorem chebEval11 (y : ℝ) : (Chebyshev.T ℝ (11 : ℤ)).eval y =
    (-11) * y + 220 * y ^ 3 + (-1232) * y ^ 5 + 2816 * y ^ 7 + (-2816) * y ^ 9 + 1024 * y ^ 11
    := by
  rw [show (11 : ℤ) = 9 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (9 : ℤ) + 1 = 10 from by norm_num,
    chebEval10, chebEval9]
  ring

private theorem chebEval12 (y : ℝ) : (Chebyshev.T ℝ (12 : ℤ)).eval y =
    1 + (-72) * y ^ 2 + 840 * y ^ 4 + (-3584) * y ^ 6 + 6912 * y ^ 8 + (-6144) * y ^ 10 + 2048 * y
      ^ 12
    := by
  rw [show (12 : ℤ) = 10 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (10 : ℤ) + 1 = 11 from by norm_num,
    chebEval11, chebEval10]
  ring

private theorem chebEval13 (y : ℝ) : (Chebyshev.T ℝ (13 : ℤ)).eval y =
    13 * y + (-364) * y ^ 3 + 2912 * y ^ 5 + (-9984) * y ^ 7 + 16640 * y ^ 9 + (-13312) * y ^ 11 +
      4096 * y ^ 13
    := by
  rw [show (13 : ℤ) = 11 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (11 : ℤ) + 1 = 12 from by norm_num,
    chebEval12, chebEval11]
  ring

private theorem chebEval14 (y : ℝ) : (Chebyshev.T ℝ (14 : ℤ)).eval y =
    (-1) + 98 * y ^ 2 + (-1568) * y ^ 4 + 9408 * y ^ 6 + (-26880) * y ^ 8 + 39424 * y ^ 10 +
      (-28672) * y ^ 12 + 8192 * y ^ 14
    := by
  rw [show (14 : ℤ) = 12 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (12 : ℤ) + 1 = 13 from by norm_num,
    chebEval13, chebEval12]
  ring

private theorem chebEval15 (y : ℝ) : (Chebyshev.T ℝ (15 : ℤ)).eval y =
    (-15) * y + 560 * y ^ 3 + (-6048) * y ^ 5 + 28800 * y ^ 7 + (-70400) * y ^ 9 + 92160 * y ^ 11
      + (-61440) * y ^ 13 + 16384 * y ^ 15
    := by
  rw [show (15 : ℤ) = 13 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (13 : ℤ) + 1 = 14 from by norm_num,
    chebEval14, chebEval13]
  ring

private theorem chebEval16 (y : ℝ) : (Chebyshev.T ℝ (16 : ℤ)).eval y =
    1 + (-128) * y ^ 2 + 2688 * y ^ 4 + (-21504) * y ^ 6 + 84480 * y ^ 8 + (-180224) * y ^ 10 +
      212992 * y ^ 12 + (-131072) * y ^ 14 + 32768 * y ^ 16
    := by
  rw [show (16 : ℤ) = 14 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (14 : ℤ) + 1 = 15 from by norm_num,
    chebEval15, chebEval14]
  ring

private theorem chebEval17 (y : ℝ) : (Chebyshev.T ℝ (17 : ℤ)).eval y =
    17 * y + (-816) * y ^ 3 + 11424 * y ^ 5 + (-71808) * y ^ 7 + 239360 * y ^ 9 + (-452608) * y ^
      11 + 487424 * y ^ 13 + (-278528) * y ^ 15 + 65536 * y ^ 17
    := by
  rw [show (17 : ℤ) = 15 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (15 : ℤ) + 1 = 16 from by norm_num,
    chebEval16, chebEval15]
  ring

private theorem chebEval18 (y : ℝ) : (Chebyshev.T ℝ (18 : ℤ)).eval y =
    (-1) + 162 * y ^ 2 + (-4320) * y ^ 4 + 44352 * y ^ 6 + (-228096) * y ^ 8 + 658944 * y ^ 10 +
      (-1118208) * y ^ 12 + 1105920 * y ^ 14 + (-589824) * y ^ 16 + 131072 * y ^ 18
    := by
  rw [show (18 : ℤ) = 16 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (16 : ℤ) + 1 = 17 from by norm_num,
    chebEval17, chebEval16]
  ring

/-- **Chebyshev certificate.** If `D * Q` on the interval parameterised by `x = (p + q*y)/s`,
`y ∈ [-1, 1]`, expands in the Chebyshev basis with coefficients `N`, then `|Q| ≤ B` there,
provided `∑ |N j| ≤ D * B`. All the cancellation lives in the coefficients: the only analytic
input is `|T j t| ≤ 1`. -/
private theorem abs_le_of_chebCert {p q s D B : ℝ} (hq : 0 < q) (hs : 0 < s) (hD : 0 < D)
    {n : ℕ} (Q : ℝ → ℝ) (N : ℕ → ℝ)
    (hQ : ∀ y : ℝ, D * Q ((p + q * y) / s)
      = ∑ j ∈ Finset.range (n + 1), N j * (Chebyshev.T ℝ (j : ℤ)).eval y)
    (hB : ∑ j ∈ Finset.range (n + 1), |N j| ≤ D * B)
    (x : ℝ) (hx0 : (p - q) / s ≤ x) (hx1 : x ≤ (p + q) / s) :
    |Q x| ≤ B := by
  rw [div_le_iff₀ hs] at hx0
  rw [le_div_iff₀ hs] at hx1
  have hy : |(s * x - p) / q| ≤ 1 := by
    rw [abs_div, abs_of_pos hq, div_le_one hq, abs_le]
    constructor <;> linarith
  have h1 := hQ ((s * x - p) / q)
  rw [show (p + q * ((s * x - p) / q)) / s = x from by field_simp; ring] at h1
  have h2 : |D * Q x| ≤ ∑ j ∈ Finset.range (n + 1), |N j| := by
    rw [h1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    calc |N j| * |(Chebyshev.T ℝ (j : ℤ)).eval ((s * x - p) / q)| ≤ |N j| * 1 :=
          mul_le_mul_of_nonneg_left (Chebyshev.abs_eval_T_real_le_one _ hy) (abs_nonneg _)
      _ = |N j| := mul_one _
  rw [abs_mul, abs_of_pos hD] at h2
  exact le_of_mul_le_mul_left (by linarith) hD

private theorem facctVal0 : (facctCoeffs[0]!).toNat = 19127174051 := by decide
private theorem facctVal1 : (facctCoeffs[1]!).toNat = 233346759686 := by decide
private theorem facctVal2 : (facctCoeffs[2]!).toNat = 2542029181962 := by decide
private theorem facctVal3 : (facctCoeffs[3]!).toNat = 25415798087749 := by decide
private theorem facctVal4 : (facctCoeffs[4]!).toNat = 228754078003076 := by decide
private theorem facctVal5 : (facctCoeffs[5]!).toNat = 1830034511206115 := by decide
private theorem facctVal6 : (facctCoeffs[6]!).toNat = 12810238987800554 := by decide
private theorem facctVal7 : (facctCoeffs[7]!).toNat = 76861433589428176 := by decide
private theorem facctVal8 : (facctCoeffs[8]!).toNat = 384307168197152512 := by decide
private theorem facctVal9 : (facctCoeffs[9]!).toNat = 1537228672812056320 := by decide
private theorem facctVal10 : (facctCoeffs[10]!).toNat = 4611686018427565056 := by decide
private theorem facctVal11 : (facctCoeffs[11]!).toNat = 9223372036854728704 := by decide
private theorem facctVal12 : (facctCoeffs[12]!).toNat = 9223372036854775808 := by decide

/-- The degree-18 Taylor truncation of `exp (-x)`. -/
private noncomputable def taylorExpNeg (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (-x) ^ i / (i.factorial : ℝ)

/-- The certification target, in units of `2 ^ (-63)`. -/
private noncomputable def certQ (x : ℝ) : ℝ :=
  hornerExact x 12 - 2 ^ 63 * taylorExpNeg 18 x

/-- `18! * certQ` has integer coefficients. -/
private theorem certQ_expand (x : ℝ) :
    (6402373705728000 : ℝ) * certQ x = 0 + 301577411034611712000 * x + 1134193306717126656000 * x
      ^ 2 + (-18739867347641696256000) * x ^ 3 + (-32842982000626237440000) * x ^ 4 +
      326702176168714253107200 * x ^ 5 + 305549933392096365772800 * x ^ 6 +
      (-2413115680306070554214400) * x ^ 7 + (-1208665697255858877235200) * x ^ 8 +
      8596251864142770040012800 * x ^ 9 + 2017429890733951881707520 * x ^ 10 +
      (-14609216358110315699896320) * x ^ 11 + (-821012305358570167664640) * x ^ 12 +
      9483102193412606294753280 * x ^ 13 + (-677364442386614735339520) * x ^ 14 +
      45157629492440982355968 * x ^ 15 + (-2822351843277561397248) * x ^ 16 +
      166020696663385964544 * x ^ 17 + (-9223372036854775808) * x ^ 18 := by
  unfold certQ taylorExpNeg
  simp only [hornerExact, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, facctVal0,
    facctVal1, facctVal2, facctVal3, facctVal4, facctVal5, facctVal6, facctVal7, facctVal8,
    facctVal9, facctVal10, facctVal11, facctVal12]
  norm_num [Nat.factorial]
  ring

/-- The same after clearing the denominator of an affine substitution `u = v / s`. -/
private theorem certQ_shift (s u v : ℝ) (hv : s * u = v) :
    ((6402373705728000 : ℝ) * s ^ 18) * certQ u = 0 * s ^ 18 + 301577411034611712000 * s ^ 17 * v
      + 1134193306717126656000 * s ^ 16 * v ^ 2 + (-18739867347641696256000) * s ^ 15 * v ^ 3 +
      (-32842982000626237440000) * s ^ 14 * v ^ 4 + 326702176168714253107200 * s ^ 13 * v ^ 5 +
      305549933392096365772800 * s ^ 12 * v ^ 6 + (-2413115680306070554214400) * s ^ 11 * v ^ 7 +
      (-1208665697255858877235200) * s ^ 10 * v ^ 8 + 8596251864142770040012800 * s ^ 9 * v ^ 9 +
      2017429890733951881707520 * s ^ 8 * v ^ 10 + (-14609216358110315699896320) * s ^ 7 * v ^ 11
      + (-821012305358570167664640) * s ^ 6 * v ^ 12 + 9483102193412606294753280 * s ^ 5 * v ^ 13
      + (-677364442386614735339520) * s ^ 4 * v ^ 14 + 45157629492440982355968 * s ^ 3 * v ^ 15 +
      (-2822351843277561397248) * s ^ 2 * v ^ 16 + 166020696663385964544 * s ^ 1 * v ^ 17 +
      (-9223372036854775808) * v ^ 18 := by
  subst hv
  rw [show ((6402373705728000 : ℝ) * s ^ 18) * certQ u = s ^ 18 * ((6402373705728000 : ℝ) * certQ
    u) from by ring, certQ_expand u]
  ring

private def certN0 : ℕ → ℤ
  | 0 => 11881511226875854183730651234993383627649187840
  | 1 => 11645475310696677515549319626459146108734013440
  | 2 => (-419008747506919410591667375759940143546368000)
  | 3 => (-180829873027354429998784145600280879169536000)
  | 4 => 2909414929571706713745068551077661759242240
  | 5 => 759499094382365726934447714249898595450880
  | 6 => (-8313529238396370481691713960732168028160)
  | 7 => (-1346451996606859545604784226645735112704)
  | 8 => 10703486790517088849614248869955108864
  | 9 => 1155152406970669618050048975372812288
  | 10 => (-6370672649408901769145347813146624)
  | 11 => (-475568451610850344956206537244672)
  | 12 => 1556967932400366019615559516160
  | 13 => 75296752412977559323583447040
  | 14 => (-84036456362858841838190592)
  | 15 => 87537882057808162062336
  | 16 => (-85486624439304978432)
  | 17 => 78531518502273024
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert0_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((1 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN0 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((1 + 1 * y) / 32) (1 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN0, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[0, 1/16]`: `|certQ| ≤ 3045` units. -/
private theorem cert0 (x : ℝ) (hx0 : (1 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (1 + 1 : ℝ) / 32) : |certQ x| ≤ 3045 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN0 j : ℤ) : ℝ)) cert0_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN0]
      norm_num) x hx0 hx1

end Falcon.Concrete.FPRBridge
