/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPR.Decode
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPR.Decode
import Mathlib.Tactic.IntervalCases

/-!
# Rounding and assembly structure of the FPR arithmetic kernels

Bit-level characterisations, shared by every `FPR` operation, of the three pipeline stages the
integer kernels run: sticky-bit truncation, leading-zero renormalisation, and the final
round-to-nearest-even assembly `FPR.make` / `FPR.make_z`.

Several statements mention `Falcon.Concrete.FPR`'s `private` helpers (`fpr_ulsh`, `fpr_ursh`,
`lzcnt_nonzero`, `lzcnt64_nonzero`, `make`, `make_z`), reachable here through `import all`, and
are therefore `private` themselves. Downstream FPR proof modules reach them through `import all`
of this module.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## Bit-level structure of the `FPR` arithmetic kernels

The integer kernels `FPR.add` / `FPR.mul` / `FPR.div` / `FPR.sqrt` / `FPR.scaled` all run the
same three-stage pipeline on a working significand: an *alignment/truncation* stage that folds
every discarded bit into a single sticky bit, a *renormalisation* stage that left-aligns the
result using a leading-zero count, and a *final assembly* stage that rounds to nearest with
ties to even and packs the sign/exponent/significand fields into an IEEE-754 word.

The three groups below characterise those stages at the bit level, independently of any one
operation, in terms of the actual `UInt64` / `UInt32` / `Int32` objects the kernels manipulate:

* `stickyShift` and the `or_fold_shiftRight*` family: the `(v ||| ((v &&& mask) + mask)) >>> k`
  idiom computes a right shift whose low bit records whether anything was discarded, so it is
  within one output unit of the exact value (`stickyShift_mul_lt`, `lt_stickyShift_mul_add`)
  and never loses zero-ness (`stickyShift_eq_zero_iff`).
* `lzcnt_nonzero_spec` / `lzcnt64_nonzero_spec` / `lzcnt64_nonzero_unique`: the five-step binary
  search counts leading zeros exactly, so the shifted significand has its top bit set
  (`fpr_ulsh_lzcnt64_top_bit`) and loses no bits (`fpr_ulsh_lzcnt64_toNat`); combined with
  `toInt_sub_lzcnt64_nonzero_or_one_toInt32` this covers both halves of the `(significand,
  exponent)` pair `FPR.add` and `FPR.scaled` renormalise to.
* `roundQuarterTiesEven` and `roundTableBit`: the constant table `0xC8` implements
  round-to-nearest-ties-even on the two bits discarded by `m >>> 2`, and the final assembly
  `FPR.make` / `FPR.make_z` denotes `± m * 2 ^ e` up to relative error `2 ^ (-53)`
  (`abs_toRealBits_make_sub_le`), including the self-normalising case where the rounding carry
  overflows the mantissa field into the exponent field.

Several statements mention `Falcon.Concrete.FPR`'s `private` helpers (`fpr_ulsh`, `fpr_ursh`,
`lzcnt_nonzero`, `lzcnt64_nonzero`, `make`, `make_z`), reachable here through the
`import all` above, and are therefore `private` themselves. -/

/-! ### The sticky fold on `ℕ` -/

/-- The value obtained by shifting `v` right by `k` bits while folding the discarded bits into
a *sticky bit*: the low bit of the result is additionally set whenever any of the `k` discarded
bits of `v` was set. -/
private def stickyShift (v k : ℕ) : ℕ := (v >>> k) ||| (if v % 2 ^ k = 0 then 0 else 1)

/-- Bitwise-or with `1` only forces the low bit. -/
theorem or_one_eq (q : ℕ) : q ||| 1 = 2 * (q / 2) + 1 := by
  have h1 : (q ||| 1) / 2 = q / 2 := by
    have := @Nat.shiftRight_or_distrib 1 q 1
    simpa [Nat.shiftRight_eq_div_pow] using this
  have h2 : (q ||| 1) % 2 = 1 := by
    simp
  omega

/-- Adding the all-ones mask `2 ^ k - 1` to a `k`-bit value carries into bit `k` exactly when
that value is nonzero: this is the core of the sticky-bit idiom. -/
private theorem shiftRight_add_two_pow_sub_one (k r : ℕ) (hr : r < 2 ^ k) :
    (r + (2 ^ k - 1)) >>> k = if r = 0 then 0 else 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases h : r = 0
  · subst h
    rw [ite_eq_left rfl]
    exact Nat.div_eq_of_lt (by omega)
  · rw [ite_eq_right h]
    refine Nat.div_eq_of_lt_le ?_ ?_ <;> omega

/-- Closed form of the sticky fold: it is `v` shifted right by `k + 1` and doubled, plus a single
low bit that records whether `v` failed to be an exact multiple of `2 ^ (k + 1)`. -/
private theorem stickyShift_eq (v k : ℕ) :
    stickyShift v k = 2 * (v / 2 ^ (k + 1)) + (if v % 2 ^ (k + 1) = 0 then 0 else 1) := by
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv : v / 2 ^ k / 2 = v / 2 ^ (k + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  unfold stickyShift
  rw [Nat.shiftRight_eq_div_pow]
  by_cases h : v % 2 ^ k = 0
  · rw [ite_eq_left h, Nat.or_zero]
    have hvm : v = 2 ^ k * (v / 2 ^ k) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)).symm
    have hmod : v % 2 ^ (k + 1) = 2 ^ k * ((v / 2 ^ k) % 2) := by
      conv_lhs => rw [hvm]
      rw [pow_succ, Nat.mul_mod_mul_left]
    have hz : v % 2 ^ (k + 1) = 0 ↔ (v / 2 ^ k) % 2 = 0 := by
      rw [hmod]
      constructor
      · intro hc
        rcases Nat.mul_eq_zero.mp hc with hc' | hc' <;> omega
      · intro hc; rw [hc, Nat.mul_zero]
    rw [← hdiv]
    by_cases hm : (v / 2 ^ k) % 2 = 0
    · rw [ite_eq_left (hz.mpr hm)]; omega
    · rw [ite_eq_right (fun hc => hm (hz.mp hc))]; omega
  · rw [ite_eq_right h]
    have h' : v % 2 ^ (k + 1) ≠ 0 := by
      intro hc
      apply h
      have hmm := Nat.mod_mod_of_dvd v (pow_dvd_pow 2 (Nat.le_succ k))
      rw [hc, Nat.zero_mod] at hmm
      exact hmm.symm
    rw [ite_eq_right h', or_one_eq, hdiv]

/-- The sticky fold vanishes exactly on `0`: no information about zero-ness is lost. -/
private theorem stickyShift_eq_zero_iff (v k : ℕ) : stickyShift v k = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [stickyShift_eq] at h
    by_cases hR : v % 2 ^ (k + 1) = 0
    · rw [ite_eq_left hR] at h
      have hD : v / 2 ^ (k + 1) = 0 := by omega
      have hdm := Nat.div_add_mod v (2 ^ (k + 1))
      rw [hD, hR, Nat.mul_zero, Nat.add_zero] at hdm
      exact hdm.symm
    · rw [ite_eq_right hR] at h
      omega
  · rintro rfl
    simp [stickyShift]

/-- The low bit of the sticky fold records whether `v` was an exact multiple of `2 ^ (k + 1)`:
this is precisely the information a subsequent round-to-nearest-even step needs. -/
private theorem stickyShift_mod_two (v k : ℕ) :
    stickyShift v k % 2 = if v % 2 ^ (k + 1) = 0 then 0 else 1 := by
  rw [stickyShift_eq]
  by_cases hR : v % 2 ^ (k + 1) = 0
  · rw [ite_eq_left hR]
    omega
  · rw [ite_eq_right hR]
    omega

/-- The sticky fold moves the value by strictly less than one output unit in the last place. -/
private theorem stickyShift_mul_lt (v k : ℕ) : stickyShift v k * 2 ^ k < v + 2 ^ k := by
  rw [stickyShift_eq]
  have hN : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
  have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hdm := Nat.div_add_mod v (2 ^ (k + 1))
  have hlt := Nat.mod_lt v (Nat.two_pow_pos (k + 1))
  have hkey : 2 ^ (k + 1) * (v / 2 ^ (k + 1)) = 2 * 2 ^ k * (v / 2 ^ (k + 1)) := by rw [hp]
  by_cases hR : v % 2 ^ (k + 1) = 0
  · rw [ite_eq_left hR]
    linarith
  · rw [ite_eq_right hR]
    have : 0 < v % 2 ^ (k + 1) := Nat.pos_of_ne_zero hR
    linarith

/-- The sticky fold never falls short of the original value by a full output unit in the last
place either: together with `stickyShift_mul_lt` this pins it to within one ulp of `v`. -/
private theorem lt_stickyShift_mul_add (v k : ℕ) : v < stickyShift v k * 2 ^ k + 2 ^ k := by
  rw [stickyShift_eq]
  have hN : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
  have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hdm := Nat.div_add_mod v (2 ^ (k + 1))
  have hlt := Nat.mod_lt v (Nat.two_pow_pos (k + 1))
  have hkey : 2 ^ (k + 1) * (v / 2 ^ (k + 1)) = 2 * 2 ^ k * (v / 2 ^ (k + 1)) := by rw [hp]
  by_cases hR : v % 2 ^ (k + 1) = 0
  · rw [ite_eq_left hR]
    linarith
  · rw [ite_eq_right hR]
    linarith

/-! ### The sticky fold on `UInt64` -/

/-- The all-ones mask `(1 <<< k) - 1` denotes `2 ^ k - 1` for shift counts below the word size. -/
private theorem toNat_one_shiftLeft_sub_one {k : UInt64} (hk : k.toNat < 64) :
    ((1 : UInt64) <<< k - 1).toNat = 2 ^ k.toNat - 1 := by
  have hlt : 2 ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  have h1 : (1 : UInt64).toNat = 1 := by decide
  have hone : ((1 : UInt64) <<< k).toNat = 2 ^ k.toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, h1, one_mul,
      Nat.mod_eq_of_lt hlt]
  have hpos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  rw [UInt64.toNat_sub, hone, h1]
  omega

/-- Masking with `(1 <<< k) - 1` keeps exactly the low `k` bits. -/
theorem toNat_and_one_shiftLeft_sub_one (v k : UInt64) (hk : k.toNat < 64) :
    (v &&& ((1 : UInt64) <<< k - 1)).toNat = v.toNat % 2 ^ k.toNat := by
  rw [UInt64.toNat_and, toNat_one_shiftLeft_sub_one hk]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- The masked low bits vanish exactly when the discarded part of `v` is zero. -/
private theorem and_one_shiftLeft_sub_one_eq_zero_iff (v k : UInt64) (hk : k.toNat < 64) :
    v &&& ((1 : UInt64) <<< k - 1) = 0 ↔ v.toNat % 2 ^ k.toNat = 0 := by
  rw [← UInt64.toNat_inj, toNat_and_one_shiftLeft_sub_one v k hk]
  constructor
  · intro h; rw [h]; rfl
  · intro h; rw [h]; rfl

/-- Core sticky-bit step on `UInt64`: adding the low-`k` all-ones mask to the masked low bits of
`v` carries into bit `k` exactly when one of those discarded bits was set. -/
private theorem and_add_mask_shiftRight (v k : UInt64) (hk : k.toNat < 64) :
    ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1)) >>> k
      = if v &&& ((1 : UInt64) <<< k - 1) = 0 then 0 else 1 := by
  have hM := toNat_one_shiftLeft_sub_one hk
  have hr := toNat_and_one_shiftLeft_sub_one v k hk
  have hrlt : v.toNat % 2 ^ k.toNat < 2 ^ k.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hkle : (2 : ℕ) ^ k.toNat ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h63 : (2 : ℕ) ^ 63 * 2 = 2 ^ 64 := by norm_num
  have hsum : ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1)).toNat
      = v.toNat % 2 ^ k.toNat + (2 ^ k.toNat - 1) := by
    rw [UInt64.toNat_add, hr, hM]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases h : v &&& ((1 : UInt64) <<< k - 1) = 0
  · rw [ite_eq_left h, ← UInt64.toNat_inj, UInt64.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hrlt,
      ite_eq_left ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mp h)]
    rfl
  · rw [ite_eq_right h, ← UInt64.toNat_inj, UInt64.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hrlt,
      ite_eq_right fun hc => h ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mpr hc)]
    rfl

/-- The sticky or-fold on `UInt64`: shifting `v ||| ((v &&& mask) + mask)` right by `k` yields
`v >>> k` with its low bit additionally set exactly when one of the `k` discarded bits of `v`
was set. This is the idiom used by `FPR.add`, `FPR.mul` and `FPR.scaled`. -/
private theorem or_fold_shiftRight (v k : UInt64) (hk : k.toNat < 64) :
    (v ||| ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1))) >>> k
      = (v >>> k) ||| (if v &&& ((1 : UInt64) <<< k - 1) = 0 then 0 else 1) := by
  rw [UInt64.shiftRight_or, and_add_mask_shiftRight v k hk]

/-- A shifted value with an explicit sticky bit or-ed in denotes `stickyShift`. -/
private theorem toNat_shiftRight_or_sticky (v k : UInt64) (hk : k.toNat < 64) :
    ((v >>> k) ||| (if v &&& ((1 : UInt64) <<< k - 1) = 0 then 0 else 1)).toNat
      = stickyShift v.toNat k.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, stickyShift]
  by_cases h : v &&& ((1 : UInt64) <<< k - 1) = 0
  · rw [ite_eq_left h, ite_eq_left ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mp h)]
    rfl
  · rw [ite_eq_right h,
      ite_eq_right fun hc => h ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mpr hc)]
    rfl

/-- Semantics of the sticky or-fold: it computes exactly `stickyShift` of the underlying
natural number, so the bounds in `stickyShift_mul_lt`, `lt_stickyShift_mul_add`,
`stickyShift_mod_two` and `stickyShift_eq_zero_iff` apply to it. -/
private theorem toNat_or_fold_shiftRight (v k : UInt64) (hk : k.toNat < 64) :
    ((v ||| ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1))) >>> k).toNat
      = stickyShift v.toNat k.toNat := by
  rw [or_fold_shiftRight v k hk, toNat_shiftRight_or_sticky v k hk]

/-- The or-fold preserves zero-ness exactly: the folded value vanishes iff the input did. This is
what makes the subsequent `make_z` zero-detection faithful: a caller who reduces a working
significand's collapse to a statement about the *pre-fold* value being `0` can transport it
through here, then land on `toRealBits_make_z_of_zero` for the resulting denotation. -/
private theorem or_fold_shiftRight_eq_zero_iff (v k : UInt64) (hk : k.toNat < 64) :
    (v ||| ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1))) >>> k = 0 ↔ v = 0 := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [← UInt64.toNat_inj, ← UInt64.toNat_inj (a := v), h0, toNat_or_fold_shiftRight v k hk]
  exact stickyShift_eq_zero_iff v.toNat k.toNat

/-! ### The `FPR.add` alignment shift

`FPR.add` aligns the smaller operand with `fpr_ursh (yu ||| ((yu &&& m) + m)) n'`, where
`m = fpr_ulsh 1 n' - 1` and `n' = n &&& 63`. -/

/-- The shift count `n &&& 63` used by `FPR.add` always stays below the word size. -/
private theorem toNat_toUInt64_and_63_lt (n : UInt32) : ((n &&& 63).toUInt64).toNat < 64 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_and]
  have hle : n.toNat &&& (63 : UInt32).toNat ≤ (63 : UInt32).toNat := Nat.and_le_right
  have h63 : (63 : UInt32).toNat = 63 := by decide
  omega

/-- Semantics of the `FPR.add` alignment step. -/
private theorem toNat_or_fold_shiftRight_toUInt64_and_63 (yu : UInt64) (n : UInt32) :
    ((yu ||| ((yu &&& ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1))
          + ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1))) >>> (n &&& 63).toUInt64).toNat
      = stickyShift yu.toNat (n &&& 63).toNat := by
  rw [← UInt32.toNat_toUInt64 (n &&& 63)]
  exact toNat_or_fold_shiftRight yu (n &&& 63).toUInt64 (toNat_toUInt64_and_63_lt n)

/-! ### The nine-bit rounding fold of `FPR.add` and `FPR.scaled` -/

/-- Semantics of the nine-bit rounding fold. -/
private theorem toNat_or_fold_shiftRight_nine (v : UInt64) :
    ((v ||| ((v &&& 0x1FF) + 0x1FF)) >>> 9).toNat = stickyShift v.toNat 9 := by
  have hmask : (1 : UInt64) <<< (9 : UInt64) - 1 = 0x1FF := by decide
  have hk : (9 : UInt64).toNat = 9 := by decide
  have h := toNat_or_fold_shiftRight v 9 (by decide)
  rwa [hmask, hk] at h

/-! ### The `(v >>> es) ||| (v &&& 1)` renormalisation of `FPR.mul` and `FPR.div`

Both `FPR.mul` and `FPR.div` renormalise a `55`-bit quotient/product with
`q >>> es ||| (q &&& 1)`, where `es = q >>> 55` is `0` or `1`. Since at most one bit is
discarded, or-ing bit `0` back in is exactly the sticky fold. The hypothesis `es.toNat ≤ 1`
is the surrounding range invariant of those two kernels, not a bit-level fact: the statement
genuinely fails for larger `es`. -/

/-- Bitwise absorption: or-ing a submask of `v` back into `v` changes nothing. -/
private theorem or_and_self (v w : UInt64) : v ||| (v &&& w) = v := by
  rw [← UInt64.toNat_inj, UInt64.toNat_or, UInt64.toNat_and]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_and]
  cases v.toNat.testBit i <;> simp

/-- Masking with `1` extracts the low bit, so the result is `0` or `1`. -/
private theorem and_one_eq_zero_or_one (v : UInt64) : v &&& 1 = 0 ∨ v &&& 1 = 1 := by
  have hmod : (v &&& 1).toNat = v.toNat % 2 := by
    have h1 : (1 : UInt64).toNat = 2 ^ 1 - 1 := by decide
    rw [UInt64.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, pow_one]
  have h2 : v.toNat % 2 = 0 ∨ v.toNat % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · left
    rw [← UInt64.toNat_inj, hmod, h2]
    rfl
  · right
    rw [← UInt64.toNat_inj, hmod, h2]
    rfl

/-- Renormalising by `es ≤ 1` places and or-ing bit `0` back in is the sticky fold for a
shift of `es` places. -/
private theorem shiftRight_or_and_one (v es : UInt64) (hes : es.toNat ≤ 1) :
    (v >>> es) ||| (v &&& 1)
      = (v >>> es) ||| (if v &&& ((1 : UInt64) <<< es - 1) = 0 then 0 else 1) := by
  have hcase : es = 0 ∨ es = 1 := by
    have h : es.toNat = 0 ∨ es.toNat = 1 := by omega
    rcases h with h | h
    · left; rw [← UInt64.toNat_inj, h]; rfl
    · right; rw [← UInt64.toNat_inj, h]; rfl
  rcases hcase with rfl | rfl
  · have hm : (1 : UInt64) <<< (0 : UInt64) - 1 = 0 := by decide
    have hz : v &&& (0 : UInt64) = 0 := by
      rw [← UInt64.toNat_inj, UInt64.toNat_and]
      exact Nat.and_zero _
    have hsr : v >>> (0 : UInt64) = v := by
      rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight]
      rfl
    rw [hm, hz, ite_eq_left rfl, hsr, or_and_self, or_zero]
  · have hm : (1 : UInt64) <<< (1 : UInt64) - 1 = 1 := by decide
    rw [hm]
    rcases and_one_eq_zero_or_one v with h | h
    · rw [h, ite_eq_left rfl]
    · rw [h, ite_eq_right (by decide : ¬ (1 : UInt64) = 0)]

/-- Semantics of the `FPR.mul` / `FPR.div` renormalisation step. -/
private theorem toNat_shiftRight_or_and_one (v es : UInt64) (hes : es.toNat ≤ 1) :
    ((v >>> es) ||| (v &&& 1)).toNat = stickyShift v.toNat es.toNat := by
  rw [shiftRight_or_and_one v es hes]
  exact toNat_shiftRight_or_sticky v es (by omega)

/-! ### The 25-bit sticky bit inside `FPR.mul` -/

/-- Adding the low-`k` all-ones mask to a value known to fit in `k` bits carries into bit `k`
exactly when the value is nonzero. `UInt32` version. -/
private theorem uint32_add_mask_shiftRight_of_lt (v k : UInt32) (hk : k.toNat < 32)
    (hv : v.toNat < 2 ^ k.toNat) :
    (v + ((1 : UInt32) <<< k - 1)) >>> k = if v = 0 then 0 else 1 := by
  have h1 : (1 : UInt32).toNat = 1 := by decide
  have hlt : 2 ^ k.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) hk
  have hone : ((1 : UInt32) <<< k).toNat = 2 ^ k.toNat := by
    rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, h1, one_mul,
      Nat.mod_eq_of_lt hlt]
  have hpos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  have hM : ((1 : UInt32) <<< k - 1).toNat = 2 ^ k.toNat - 1 := by
    rw [UInt32.toNat_sub, hone, h1]
    omega
  have hkle : (2 : ℕ) ^ k.toNat ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h31 : (2 : ℕ) ^ 31 * 2 = 2 ^ 32 := by norm_num
  have hsum : (v + ((1 : UInt32) <<< k - 1)).toNat = v.toNat + (2 ^ k.toNat - 1) := by
    rw [UInt32.toNat_add, hM]
    exact Nat.mod_eq_of_lt (by omega)
  have hviff : v = 0 ↔ v.toNat = 0 := by
    constructor
    · rintro rfl; rfl
    · intro h; rw [← UInt32.toNat_inj, h]; rfl
  by_cases h : v = 0
  · rw [ite_eq_left h, ← UInt32.toNat_inj, UInt32.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hv, ite_eq_left (hviff.mp h)]
    rfl
  · rw [ite_eq_right h, ← UInt32.toNat_inj, UInt32.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hv, ite_eq_right fun hc => h (hviff.mpr hc)]
    rfl

/-- The 25-bit sticky bit `FPR.mul` folds into the product: the low `25`-bit limbs `z0` and
`z1'` contribute a carry into bit `25` exactly when one of them is nonzero. -/
private theorem masked_or_add_shiftRight_25 (a b : UInt32) :
    (((a &&& 0x01FFFFFF) ||| (b &&& 0x01FFFFFF)) + 0x01FFFFFF) >>> 25
      = if (a &&& 0x01FFFFFF) ||| (b &&& 0x01FFFFFF) = 0 then 0 else 1 := by
  have hmask : (1 : UInt32) <<< (25 : UInt32) - 1 = 0x01FFFFFF := by decide
  have hMn : (0x01FFFFFF : UInt32).toNat = 2 ^ 25 - 1 := by decide
  have hbound : ∀ x : UInt32, (x &&& 0x01FFFFFF).toNat < 2 ^ 25 := by
    intro x
    rw [UInt32.toNat_and, hMn, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hv : ((a &&& 0x01FFFFFF) ||| (b &&& 0x01FFFFFF)).toNat < 2 ^ (25 : UInt32).toNat := by
    rw [show (25 : UInt32).toNat = 25 from by decide, UInt32.toNat_or]
    exact Nat.or_lt_two_pow (hbound a) (hbound b)
  have h := uint32_add_mask_shiftRight_of_lt _ 25 (by decide) hv
  rwa [hmask] at h

/-- `FPR.add` alignment step, semantic form. -/
private theorem toNat_fpr_ursh_or_fold (yu : UInt64) (n : UInt32) :
    (fpr_ursh (yu ||| ((yu &&& (fpr_ulsh 1 (n &&& 63) - 1)) + (fpr_ulsh 1 (n &&& 63) - 1)))
        (n &&& 63)).toNat
      = stickyShift yu.toNat (n &&& 63).toNat :=
  toNat_or_fold_shiftRight_toUInt64_and_63 yu n

/-! ### `UInt32` numeral evaluation for the leading-zero search

The shift amounts and mask widths appearing in `FPR.lzcnt_nonzero` are `UInt32` numerals; these
evaluate them so that `omega` sees genuine literals. -/

private theorem toNat_lit0 : (0 : UInt32).toNat = 0 := by decide

private theorem toNat_lit1 : (1 : UInt32).toNat = 1 := by decide

private theorem toNat_lit2 : (2 : UInt32).toNat = 2 := by decide

private theorem toNat_lit4 : (4 : UInt32).toNat = 4 := by decide

private theorem toNat_lit8 : (8 : UInt32).toNat = 8 := by decide

private theorem toNat_lit16 : (16 : UInt32).toNat = 16 := by decide

/-! ### High-bit masks

Each step of `FPR.lzcnt_nonzero` tests a prefix of its working word against a mask whose set bits
are exactly the top `32 - k` positions, i.e. the numeral `2 ^ 32 - 2 ^ k`. The lemmas here turn
those tests into the arithmetic statement `v.toNat < 2 ^ k`. -/

/-- The bits of the top-`(32 - k)` mask `2 ^ 32 - 2 ^ k` are exactly the positions in `[k, 32)`. -/
private theorem testBit_highMask {k : ℕ} (hk : k ≤ 32) (i : ℕ) :
    (2 ^ 32 - 2 ^ k).testBit i = (decide (k ≤ i) && decide (i < 32)) := by
  have hrw : 2 ^ 32 - 2 ^ k = (2 ^ (32 - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← pow_add]
    congr 2
    omega
  rw [hrw, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i k with h | h
  · simp [Nat.not_le.mpr h]
  · simp only [ge_iff_le, h, decide_true, Bool.true_and, decide_eq_decide]
    omega

/-- Masking a 32-bit natural number with `2 ^ 32 - 2 ^ k` clears its low `k` bits. -/
private theorem and_highMask_eq_shift {n k : ℕ} (hn : n < 2 ^ 32) (hk : k ≤ 32) :
    n &&& (2 ^ 32 - 2 ^ k) = n >>> k <<< k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_highMask hk, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge i k with h | h
  · simp [Nat.not_le.mpr h]
  · rw [show k + (i - k) = i from by omega]
    rcases Nat.lt_or_ge i 32 with h2 | h2
    · simp [h, h2]
    · have hb : n.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) h2))
      simp [h, hb]

/-- A 32-bit natural number has no bits at or above position `k` exactly when it is below
`2 ^ k`. -/
private theorem and_highMask_eq_zero_iff {n k : ℕ} (hn : n < 2 ^ 32) (hk : k ≤ 32) :
    n &&& (2 ^ 32 - 2 ^ k) = 0 ↔ n < 2 ^ k := by
  rw [and_highMask_eq_shift hn hk, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact (Nat.div_eq_zero_iff.mp h).resolve_left (Nat.two_pow_pos k).ne'
    · exact absurd h (Nat.two_pow_pos k).ne'
  · intro h
    exact Or.inl (Nat.div_eq_of_lt h)

/-- The `UInt32` form of `and_highMask_eq_zero_iff`, matching the shape of the mask tests inside
`FPR.lzcnt_nonzero`. -/
private theorem uint32_and_highMask_eq_zero_iff (v : UInt32) {k : ℕ} (hk : k ≤ 32)
    {M : UInt32} (hM : M.toNat = 2 ^ 32 - 2 ^ k) :
    (v &&& M = 0) ↔ v.toNat < 2 ^ k := by
  rw [← UInt32.toNat_inj, UInt32.toNat_and, hM, toNat_lit0]
  exact and_highMask_eq_zero_iff (UInt32.toNat_lt v) hk

/-- The step-1 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask16 (v : UInt32) : (v &&& 4294901760 = 0) ↔ v.toNat < 2 ^ 16 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-2 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask24 (v : UInt32) : (v &&& 4278190080 = 0) ↔ v.toNat < 2 ^ 24 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-3 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask28 (v : UInt32) : (v &&& 4026531840 = 0) ↔ v.toNat < 2 ^ 28 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-4 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask30 (v : UInt32) : (v &&& 3221225472 = 0) ↔ v.toNat < 2 ^ 30 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-5 (top-bit) test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask31 (v : UInt32) : (v &&& 2147483648 = 0) ↔ v.toNat < 2 ^ 31 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-1 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl16 (v : UInt32) : (v <<< 16).toNat = v.toNat * 2 ^ 16 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit16, Nat.shiftLeft_eq]

/-- The step-2 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl8 (v : UInt32) : (v <<< 8).toNat = v.toNat * 2 ^ 8 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit8, Nat.shiftLeft_eq]

/-- The step-3 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl4 (v : UInt32) : (v <<< 4).toNat = v.toNat * 2 ^ 4 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit4, Nat.shiftLeft_eq]

/-- The step-4 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl2 (v : UInt32) : (v <<< 2).toNat = v.toNat * 2 ^ 2 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit2, Nat.shiftLeft_eq]

/-! ### 32-bit leading-zero count -/

/-- `FPR.lzcnt_nonzero` never returns more than `31`: each of its five steps contributes at most
its own shift width, and `16 + 8 + 4 + 2 + 1 = 31`. -/
private theorem lzcnt_nonzero_toNat_le (x : UInt32) : (lzcnt_nonzero x).toNat ≤ 31 := by
  simp only [lzcnt_nonzero, Id.run]
  dsimp only [pure, Id.instMonad]
  split_ifs <;>
    norm_num [UInt32.toNat_add, toNat_lit0, toNat_lit1, toNat_lit2, toNat_lit4, toNat_lit8,
      toNat_lit16]

/-- `FPR.lzcnt_nonzero x` is the number of leading zero bits of a nonzero 32-bit word `x`: it is
the unique `c` with `2 ^ (31 - c) ≤ x < 2 ^ (32 - c)`. Proved by running the five-step binary
search symbolically (`split_ifs`), each branch then being linear arithmetic over the mask and
shift translations above. -/
private theorem lzcnt_nonzero_spec (x : UInt32) (hx : x ≠ 0) :
    2 ^ (31 - (lzcnt_nonzero x).toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (32 - (lzcnt_nonzero x).toNat) := by
  have hxN : x.toNat ≠ 0 := fun h0 => hx (UInt32.toNat_inj.mp (by simpa using h0))
  have hxlt : x.toNat < 2 ^ 32 := UInt32.toNat_lt x
  simp only [lzcnt_nonzero, Id.run]
  dsimp only [pure, Id.instMonad]
  simp only [beq_iff_eq, and_mask16, and_mask24, and_mask28, and_mask30, and_mask31,
    toNat_shl16, toNat_shl8, toNat_shl4, toNat_shl2]
  split_ifs <;>
    (norm_num [UInt32.toNat_add, toNat_lit0, toNat_lit1, toNat_lit2, toNat_lit4, toNat_lit8,
      toNat_lit16]; omega)

/-! ### 64-bit leading-zero count -/

/-- The high half `(x >>> 32).toUInt32` of a `UInt64` is its quotient by `2 ^ 32`. -/
private theorem toUInt32_shiftRight32_toNat (x : UInt64) :
    (x >>> 32).toUInt32.toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  norm_num [Nat.shiftRight_eq_div_pow]
  have hb : (0 : ℕ) < 2 ^ 32 := by positivity
  have hlt : x.toNat / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul hb]
    calc x.toNat < 2 ^ 64 := UInt64.toNat_lt x
      _ = 2 ^ 32 * 2 ^ 32 := by norm_num
  exact hlt

/-- The "is it nonzero" idiom `y ||| (0 - y)` of `FPR.lzcnt64_nonzero`: a nonzero word or'd with
its two's-complement negation always has its top bit set, since one of the two summands exceeds
`2 ^ 31`. -/
private theorem or_neg_shiftRight_31 (y : UInt32) (hy : y ≠ 0) :
    (y ||| ((0 : UInt32) - y)) >>> 31 = 1 := by
  have hyN : y.toNat ≠ 0 := fun h0 => hy (UInt32.toNat_inj.mp (by simpa using h0))
  have hylt : y.toNat < 2 ^ 32 := UInt32.toNat_lt y
  rw [← UInt32.toNat_inj, UInt32.toNat_shiftRight, UInt32.toNat_or, UInt32.toNat_sub, toNat_lit0,
    toNat_lit1, show (31 : UInt32).toNat % 32 = 31 from by decide,
    show (2 ^ 32 - y.toNat + 0) % 2 ^ 32 = 2 ^ 32 - y.toNat from Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_or_distrib, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rcases Nat.lt_or_ge y.toNat (2 ^ 31) with h | h
  · rw [show y.toNat / 2 ^ 31 = 0 from by omega,
      show (2 ^ 32 - y.toNat) / 2 ^ 31 = 1 from by omega]
    decide
  · rw [show y.toNat / 2 ^ 31 = 1 from by omega]
    rcases Nat.lt_or_ge (2 ^ 32 - y.toNat) (2 ^ 31) with h2 | h2
    · rw [show (2 ^ 32 - y.toNat) / 2 ^ 31 = 0 from by omega]; decide
    · rw [show (2 ^ 32 - y.toNat) / 2 ^ 31 = 1 from by omega]; decide

/-- When the high half is nonzero, `FPR.lzcnt64_nonzero` selects it and adds no offset: its
conditional mask `m` collapses to `0`. -/
private theorem lzcnt64_nonzero_eq_high (x : UInt64) (h : (x >>> 32).toUInt32 ≠ 0) :
    lzcnt64_nonzero x = lzcnt_nonzero (x >>> 32).toUInt32 := by
  have hm : ~~~(tbmask ((x >>> 32).toUInt32 ||| ((0 : UInt32) - (x >>> 32).toUInt32))) = 0 := by
    unfold tbmask
    rw [or_neg_shiftRight_31 _ h]
    decide
  simp only [lzcnt64_nonzero, hm]
  simp

/-- When the high half is zero, `FPR.lzcnt64_nonzero` counts in the low half and adds `32`: its
conditional mask `m` collapses to all-ones. -/
private theorem lzcnt64_nonzero_eq_low (x : UInt64) (h : (x >>> 32).toUInt32 = 0) :
    lzcnt64_nonzero x = lzcnt_nonzero x.toUInt32 + 32 := by
  have hm : ~~~(tbmask ((x >>> 32).toUInt32 ||| ((0 : UInt32) - (x >>> 32).toUInt32)))
      = 4294967295 := by
    rw [h]; unfold tbmask; decide
  have hand : x.toUInt32 &&& 4294967295 = x.toUInt32 := by
    rw [← UInt32.toNat_inj, UInt32.toNat_and,
      show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (UInt32.toNat_lt x.toUInt32)
  simp only [lzcnt64_nonzero, hm, hand,
    show ((4294967295 : UInt32) &&& 32) = 32 from by decide]
  rw [h, UInt32.zero_or]

/-- `FPR.lzcnt64_nonzero` never returns more than `63`. -/
private theorem lzcnt64_nonzero_toNat_le (x : UInt64) : (lzcnt64_nonzero x).toNat ≤ 63 := by
  have h32 : (32 : UInt32).toNat = 32 := by decide
  by_cases h : (x >>> 32).toUInt32 = 0
  · rw [lzcnt64_nonzero_eq_low x h, UInt32.toNat_add, h32]
    have := lzcnt_nonzero_toNat_le x.toUInt32
    omega
  · rw [lzcnt64_nonzero_eq_high x h]
    exact le_trans (lzcnt_nonzero_toNat_le _) (by norm_num)

/-- `FPR.lzcnt64_nonzero x` is the number of leading zero bits of a nonzero 64-bit word `x`:
`2 ^ (63 - c) ≤ x < 2 ^ (64 - c)`. Both halves of the `UInt32`/`UInt64` dispatch reduce to
`lzcnt_nonzero_spec` on the selected half. -/
private theorem lzcnt64_nonzero_spec (x : UInt64) (hx : x ≠ 0) :
    2 ^ (63 - (lzcnt64_nonzero x).toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (64 - (lzcnt64_nonzero x).toNat) := by
  have hxN : x.toNat ≠ 0 := fun h0 => hx (UInt64.toNat_inj.mp (by simpa using h0))
  have hhi := toUInt32_shiftRight32_toNat x
  have h32 : (32 : UInt32).toNat = 32 := by decide
  by_cases h : (x >>> 32).toUInt32 = 0
  · have hdiv : x.toNat / 2 ^ 32 = 0 := by rw [← hhi, h]; decide
    have hlt32 : x.toNat < 2 ^ 32 :=
      (Nat.div_eq_zero_iff.mp hdiv).resolve_left (by norm_num)
    have hlow : x.toUInt32.toNat = x.toNat := by
      rw [UInt64.toNat_toUInt32]; exact Nat.mod_eq_of_lt hlt32
    have hne : x.toUInt32 ≠ 0 := by
      intro h0
      rw [h0] at hlow
      exact hxN (by simpa using hlow.symm)
    obtain ⟨hl, hh⟩ := lzcnt_nonzero_spec x.toUInt32 hne
    rw [hlow] at hl hh
    have hc := lzcnt_nonzero_toNat_le x.toUInt32
    rw [lzcnt64_nonzero_eq_low x h, UInt32.toNat_add, h32,
      Nat.mod_eq_of_lt (show (lzcnt_nonzero x.toUInt32).toNat + 32 < 2 ^ 32 from by omega),
      show 63 - ((lzcnt_nonzero x.toUInt32).toNat + 32)
        = 31 - (lzcnt_nonzero x.toUInt32).toNat from by omega,
      show 64 - ((lzcnt_nonzero x.toUInt32).toNat + 32)
        = 32 - (lzcnt_nonzero x.toUInt32).toNat from by omega]
    exact ⟨hl, hh⟩
  · rw [lzcnt64_nonzero_eq_high x h]
    have hc := lzcnt_nonzero_toNat_le (x >>> 32).toUInt32
    obtain ⟨hl, hh⟩ := lzcnt_nonzero_spec (x >>> 32).toUInt32 h
    rw [hhi] at hl hh
    have hdm : x.toNat / 2 ^ 32 * 2 ^ 32 + x.toNat % 2 ^ 32 = x.toNat := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hmodlt : x.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
    have p1 : 2 ^ (31 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) * 2 ^ 32
        = 2 ^ (63 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) := by
      rw [← pow_add]; congr 1; omega
    have p2 : 2 ^ (32 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) * 2 ^ 32
        = 2 ^ (64 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) := by
      rw [← pow_add]; congr 1; omega
    omega

/-- The bracket of `lzcnt64_nonzero_spec` pins the count down: `FPR.lzcnt64_nonzero x` is the
*unique* `c` with `2 ^ (63 - c) ≤ x < 2 ^ (64 - c)`. No explicit `c ≤ 63` hypothesis is needed:
for `c ≥ 64` the two `Nat`-truncated exponents `63 - c` and `64 - c` both collapse to `0`, so the
hypotheses would demand `1 ≤ x.toNat < 1`, which is unsatisfiable. -/
private theorem lzcnt64_nonzero_unique (x : UInt64) (c : ℕ)
    (h1 : 2 ^ (63 - c) ≤ x.toNat) (h2 : x.toNat < 2 ^ (64 - c)) :
    (lzcnt64_nonzero x).toNat = c := by
  by_cases hc : c ≤ 63
  · have hx : x ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp only [show (0 : UInt64).toNat = 0 from by decide] at h1
      exact absurd h1 (by simp)
    have hd := lzcnt64_nonzero_toNat_le x
    obtain ⟨hl, hh⟩ := lzcnt64_nonzero_spec x hx
    by_contra hne
    rcases Nat.lt_or_ge (lzcnt64_nonzero x).toNat c with hlt | hge
    · have : (2 : ℕ) ^ (64 - c) ≤ 2 ^ (63 - (lzcnt64_nonzero x).toNat) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : (2 : ℕ) ^ (64 - (lzcnt64_nonzero x).toNat) ≤ 2 ^ (63 - c) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · exfalso
    have h63 : 63 - c = 0 := by omega
    have h64 : 64 - c = 0 := by omega
    rw [h63] at h1
    rw [h64] at h2
    omega

/-! ### The `||| 1` guard and the normalising shift

`FPR.norm64` — and its inlined copies in `FPR.scaled` and `FPR.add` — call
`lzcnt64_nonzero (m ||| 1)` rather than `lzcnt64_nonzero m`, so that the count is defined even for
`m = 0`. For nonzero `m` the guard is invisible: setting the low bit cannot change which power of
two brackets the value. -/

/-- The `||| 1` guard makes the argument of the leading-zero count unconditionally nonzero. -/
private theorem or_one_ne_zero (m : UInt64) : m ||| 1 ≠ 0 := by
  intro h
  have h1 : (1 : UInt64) ≤ m ||| 1 := UInt64.right_le_or
  rw [h] at h1
  exact absurd h1 (by decide)

/-- The `||| 1` guard never decreases the value. -/
private theorem le_or_one_toNat (m : UInt64) : m.toNat ≤ (m ||| 1).toNat :=
  UInt64.le_iff_toNat_le.mp UInt64.left_le_or

/-- The `||| 1` guard is invisible above bit `0`. -/
private theorem or_one_shiftRight_one (m : UInt64) : (m ||| 1) >>> 1 = m >>> 1 := by
  rw [UInt64.shiftRight_or, show ((1 : UInt64) >>> 1) = 0 from by decide, UInt64.or_zero]

/-- Setting the low bit cannot push a nonzero word across a power-of-two boundary from below:
`m ||| 1` and `m` have the same leading power of two. -/
private theorem two_pow_le_of_or_one {m : UInt64} {k : ℕ} (hm : m ≠ 0)
    (h : 2 ^ k ≤ (m ||| 1).toNat) : 2 ^ k ≤ m.toNat := by
  have hmN : m.toNat ≠ 0 := fun h0 => hm (UInt64.toNat_inj.mp (by simpa using h0))
  match k with
  | 0 => simpa using Nat.one_le_iff_ne_zero.mpr hmN
  | (j + 1) =>
    have hdiv : (m ||| 1).toNat / 2 = m.toNat / 2 := by
      have hs := congrArg UInt64.toNat (or_one_shiftRight_one m)
      rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight] at hs
      simpa [Nat.shiftRight_eq_div_pow] using hs
    have h1 : 2 ^ (j + 1) / 2 ≤ (m ||| 1).toNat / 2 := Nat.div_le_div_right h
    rw [hdiv, pow_succ] at h1
    have h4 : m.toNat / 2 * 2 ≤ m.toNat := Nat.div_mul_le_self _ _
    have hp : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    omega

/-- The guarded count `lzcnt64_nonzero (m ||| 1)` used by `FPR.norm64`, `FPR.scaled` and `FPR.add`
brackets `m` itself whenever `m` is nonzero. -/
private theorem lzcnt64_nonzero_or_one_spec (m : UInt64) (hm : m ≠ 0) :
    2 ^ (63 - (lzcnt64_nonzero (m ||| 1)).toNat) ≤ m.toNat ∧
      m.toNat < 2 ^ (64 - (lzcnt64_nonzero (m ||| 1)).toNat) := by
  obtain ⟨hl, hh⟩ := lzcnt64_nonzero_spec (m ||| 1) (or_one_ne_zero m)
  exact ⟨two_pow_le_of_or_one hm hl, lt_of_le_of_lt (le_or_one_toNat m) hh⟩

/-- `FPR.fpr_ulsh` is a left shift by a sub-word amount, i.e. multiplication by a power of two
modulo `2 ^ 64`. -/
private theorem toNat_fpr_ulsh (m : UInt64) (c : UInt32) (hc : c.toNat < 64) :
    (fpr_ulsh m c).toNat = m.toNat * 2 ^ c.toNat % 2 ^ 64 := by
  unfold fpr_ulsh
  rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt hc, Nat.shiftLeft_eq]

/-- The normalising shift loses no bits: for nonzero `m`, `fpr_ulsh m (lzcnt64_nonzero (m ||| 1))`
is exactly `m * 2 ^ c`, with no wraparound. This is the "value-preserving in the
significand/exponent pair" half of the renormalisation step. -/
private theorem fpr_ulsh_lzcnt64_toNat (m : UInt64) (hm : m ≠ 0) :
    (fpr_ulsh m (lzcnt64_nonzero (m ||| 1))).toNat
      = m.toNat * 2 ^ (lzcnt64_nonzero (m ||| 1)).toNat := by
  have hc := lzcnt64_nonzero_toNat_le (m ||| 1)
  obtain ⟨hl, hh⟩ := lzcnt64_nonzero_or_one_spec m hm
  rw [toNat_fpr_ulsh m _ (by omega)]
  apply Nat.mod_eq_of_lt
  have hpos : 0 < 2 ^ (lzcnt64_nonzero (m ||| 1)).toNat := Nat.two_pow_pos _
  have hkey := mul_lt_mul_of_pos_right hh hpos
  rwa [← pow_add, show 64 - (lzcnt64_nonzero (m ||| 1)).toNat
      + (lzcnt64_nonzero (m ||| 1)).toNat = 64 from by omega] at hkey

/-- The normalising shift left-aligns: for nonzero `m`, the shifted significand
`fpr_ulsh m (lzcnt64_nonzero (m ||| 1))` has its top (bit 63) set. -/
private theorem fpr_ulsh_lzcnt64_top_bit (m : UInt64) (hm : m ≠ 0) :
    2 ^ 63 ≤ (fpr_ulsh m (lzcnt64_nonzero (m ||| 1))).toNat := by
  have hc := lzcnt64_nonzero_toNat_le (m ||| 1)
  obtain ⟨hl, hh⟩ := lzcnt64_nonzero_or_one_spec m hm
  rw [fpr_ulsh_lzcnt64_toNat m hm]
  have hkey := Nat.mul_le_mul hl (Nat.le_refl (2 ^ (lzcnt64_nonzero (m ||| 1)).toNat))
  rwa [← pow_add, show 63 - (lzcnt64_nonzero (m ||| 1)).toNat
      + (lzcnt64_nonzero (m ||| 1)).toNat = 63 from by omega] at hkey

/-! ### The `FPR.add` / `FPR.scaled` exponent decrement

`FPR.add`'s `ex'' := ex' - c_add.toInt32` (with `c_add := lzcnt64_nonzero (zu ||| 1)`) and
`FPR.scaled`'s `sc' := sc - c_sc.toInt32` (with `c_sc := lzcnt64_nonzero (m ||| 1)`) both inline
this same exponent decrement rather than routing through `FPR.norm64`; the lemma below is stated
directly in that inlined shape. -/

/-- Reinterpreting a small `UInt32` as an `Int32` preserves its value. -/
theorem toInt_toInt32_of_lt {y : UInt32} (hy : y.toNat < 2 ^ 31) :
    y.toInt32.toInt = (y.toNat : ℤ) := by
  unfold Int32.toInt
  rw [UInt32.toBitVec_toInt32,
    BitVec.toInt_eq_toNat_of_lt (by simp only [UInt32.toNat_toBitVec]; omega),
    UInt32.toNat_toBitVec]

/-- The exponent decrement `e - (lzcnt64_nonzero (m ||| 1)).toInt32` computed by `FPR.add` and
`FPR.scaled` is exactly the shift amount subtracted as an integer, with no `Int32` wraparound. The
hypothesis rules out underflow, which cannot occur for the exponents `FPR.scaled` / `FPR.add`
actually pass (they live near `±1100`, while the bound only excludes `e < -2 ^ 31 + 63`). -/
private theorem toInt_sub_lzcnt64_nonzero_or_one_toInt32 (m : UInt64) (e : Int32)
    (hnf : -(2 ^ 31 : ℤ) ≤ e.toInt - ((lzcnt64_nonzero (m ||| 1)).toNat : ℤ)) :
    (e - (lzcnt64_nonzero (m ||| 1)).toInt32).toInt
      = e.toInt - ((lzcnt64_nonzero (m ||| 1)).toNat : ℤ) := by
  have hc := lzcnt64_nonzero_toNat_le (m ||| 1)
  rw [Int32.toInt_sub, toInt_toInt32_of_lt (by omega)]
  refine Int.bmod_eq_of_le_mul_two ?_ ?_
  · have h := Int32.le_toInt e
    push_cast
    omega
  · have h := Int32.toInt_lt e
    push_cast
    omega

/-! ### Round-to-nearest, ties-to-even on `ℕ`

Both `FPR.make` and `FPR.make_z` finish by discarding the low two bits of a working significand
`m` and adding a correction bit read out of the constant table `0xC8`:

```
cc := ((0xC8 : UInt64) >>> (m.toUInt32 &&& 7).toUInt64) &&& 1
...  + (m >>> 2) + cc
```

The three low bits of `m` are (kept LSB, round bit, sticky bit), and `0xC8 = 0b11001000` has bits
`3`, `6`, `7` set, so `cc = 1` exactly for `m &&& 7 ∈ {3, 6, 7}`. -/

/-- Round `n / 4` to the nearest natural number, breaking exact ties (`n % 4 = 2`) toward
the even quotient. This is IEEE-754's default rounding direction specialized to a two-bit
discard: `n % 4` is the pair (round bit, sticky bit) and `n / 4 % 2` is the kept LSB. -/
private def roundQuarterTiesEven (n : ℕ) : ℕ :=
  n / 4 + (if 2 < n % 4 ∨ (n % 4 = 2 ∧ n / 4 % 2 = 1) then 1 else 0)

/-- `roundQuarterTiesEven n` is a nearest integer to `n / 4`: scaled back up by `4` it is
within `2` of `n` from above. -/
private theorem four_mul_roundQuarterTiesEven_le (n : ℕ) :
    4 * roundQuarterTiesEven n ≤ n + 2 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- `roundQuarterTiesEven n` is a nearest integer to `n / 4`: scaled back up by `4` it is
within `2` of `n` from below. -/
private theorem le_four_mul_roundQuarterTiesEven (n : ℕ) :
    n ≤ 4 * roundQuarterTiesEven n + 2 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- Rounding never moves the quotient down. -/
private theorem div_four_le_roundQuarterTiesEven (n : ℕ) : n / 4 ≤ roundQuarterTiesEven n := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- Rounding moves the quotient up by at most one. -/
private theorem roundQuarterTiesEven_le_div_four_succ (n : ℕ) :
    roundQuarterTiesEven n ≤ n / 4 + 1 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- Rounding is exact when the two discarded bits are zero. -/
private theorem roundQuarterTiesEven_of_mod_four_eq_zero (n : ℕ) (h : n % 4 = 0) :
    roundQuarterTiesEven n = n / 4 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- A normalized 55-bit working significand rounds to a 53-bit significand, possibly
carrying out to the round power `2 ^ 53` (the case that bumps the exponent field). -/
private theorem roundQuarterTiesEven_mem_of_normalized (n : ℕ) (h1 : 2 ^ 54 ≤ n) (h2 : n < 2 ^ 55) :
    2 ^ 52 ≤ roundQuarterTiesEven n ∧ roundQuarterTiesEven n ≤ 2 ^ 53 := by
  refine ⟨le_trans ?_ (div_four_le_roundQuarterTiesEven n),
    le_trans (roundQuarterTiesEven_le_div_four_succ n) ?_⟩ <;> omega

/-- The real-number content of the two nearest-integer bounds: rounding `n / 4` moves it by
at most half a unit. -/
private theorem abs_roundQuarterTiesEven_sub_div_four_le (n : ℕ) :
    |(roundQuarterTiesEven n : ℝ) - (n : ℝ) / 4| ≤ 1 / 2 := by
  have h1 := four_mul_roundQuarterTiesEven_le n
  have h2 := le_four_mul_roundQuarterTiesEven n
  have h1' : (4 : ℝ) * (roundQuarterTiesEven n : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ 4 * (roundQuarterTiesEven n : ℝ) + 2 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-! ### The `0xC8` rounding-table lookup -/

/-- The `0xC8` rounding-table lookup used by `FPR.make` and `FPR.make_z`: the low three bits
of the working significand `m` index the constant `0xC8 = 0b11001000`. -/
private def roundTableBit (m : UInt64) : UInt64 :=
  ((0xC8 : UInt64) >>> (m.toUInt32 &&& 7).toUInt64) &&& 1

private theorem nat_and_seven (x : ℕ) : x &&& 7 = x % 8 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x 3

/-- The table index `(m.toUInt32 &&& 7).toUInt64` is exactly the low three bits of `m`,
the truncation to `UInt32` notwithstanding. -/
private theorem toNat_tableIndex (m : UInt64) :
    (m.toUInt32 &&& 7).toUInt64.toNat = m.toNat % 8 := by
  rw [UInt32.toNat_toUInt64]
  simp only [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt32.reduceToNat]
  rw [nat_and_seven]
  exact Nat.mod_mod_of_dvd _ (by norm_num)

/-- The eight-entry rounding table, read off `0xC8 = 0b11001000`: the correction bit is `1`
exactly on the low-three-bit patterns `3`, `6`, `7`. -/
private theorem toNat_roundTableBit_eq_ite_mod_eight (m : UInt64) :
    (roundTableBit m).toNat =
      if m.toNat % 8 = 3 ∨ m.toNat % 8 = 6 ∨ m.toNat % 8 = 7 then 1 else 0 := by
  rw [roundTableBit, UInt64.toNat_and, UInt64.toNat_shiftRight, toNat_tableIndex,
    Nat.mod_eq_of_lt (by omega : m.toNat % 8 < 64)]
  have h8 : m.toNat % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize m.toNat % 8 = k at h8 ⊢
  interval_cases k <;> decide

/-- The rounding table restated in IEEE terms: the correction bit is `1` exactly when the
discarded two bits `m % 4` exceed a half, or form an exact half whose kept LSB is odd. -/
private theorem toNat_roundTableBit (m : UInt64) :
    (roundTableBit m).toNat =
      if 2 < m.toNat % 4 ∨ (m.toNat % 4 = 2 ∧ m.toNat / 4 % 2 = 1) then 1 else 0 := by
  rw [toNat_roundTableBit_eq_ite_mod_eight]
  split_ifs <;> omega

private theorem toNat_shiftRight_two (m : UInt64) : (m >>> 2).toNat = m.toNat / 4 := by
  have h2 : (2 : UInt64).toNat = 2 := rfl
  rw [UInt64.toNat_shiftRight, h2]
  norm_num [Nat.shiftRight_eq_div_pow]

/-- The `0xC8` rounding table implements round-to-nearest, ties-to-even: discarding the
low two bits of the working significand `m` and adding the table bit yields exactly the
nearest integer to `m / 4`, with exact halves resolved toward an even result. -/
private theorem toNat_shiftRight_two_add_roundTableBit (m : UInt64) :
    ((m >>> 2) + roundTableBit m).toNat = roundQuarterTiesEven m.toNat := by
  have hm : m.toNat < 2 ^ 64 := m.toNat_lt_size
  rw [UInt64.toNat_add, toNat_shiftRight_two, toNat_roundTableBit]
  unfold roundQuarterTiesEven
  split_ifs <;> omega

/-- The rounded significand of a `UInt64` never overflows into the exponent field's carry
region: it is at most `2 ^ 62`. -/
private theorem roundQuarterTiesEven_toNat_le (m : UInt64) :
    roundQuarterTiesEven m.toNat ≤ 2 ^ 62 := by
  have hm : m.toNat < 2 ^ 64 := m.toNat_lt_size
  have := roundQuarterTiesEven_le_div_four_succ m.toNat
  omega

/-- Injecting the rounded significand back into `UInt64` is faithful. -/
private theorem toNat_ofNat_roundQuarterTiesEven (m : UInt64) :
    (UInt64.ofNat (roundQuarterTiesEven m.toNat)).toNat = roundQuarterTiesEven m.toNat := by
  have := roundQuarterTiesEven_toNat_le m
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- The `UInt64`-level form: `(m >>> 2) + cc` is the injection of the rounded quotient. -/
private theorem shiftRight_two_add_roundTableBit (m : UInt64) :
    (m >>> 2) + roundTableBit m = UInt64.ofNat (roundQuarterTiesEven m.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_shiftRight_two_add_roundTableBit, toNat_ofNat_roundQuarterTiesEven]

/-! ### The final assembly `FPR.make` / `FPR.make_z`

The three fields are combined with **plain `UInt64` addition**, not with `|||`. The summand
`(m >>> 2) + cc` lies in `[2 ^ 52, 2 ^ 53]`, i.e. it is the *full* significand including the
implicit leading bit, so its top bit always carries into the exponent slot: the stored exponent
field is `e + 1077`, not `e + 1076`. When round-to-nearest pushes the significand all the way to
`2 ^ 53` the same carry fires a second time, incrementing the exponent field once more and leaving
a zero mantissa — exactly "increment the exponent and halve the significand". `toRealBits_make`
states both cases uniformly.

Every field-range side condition is an explicit hypothesis: `s.toNat ≤ 1`,
`2 ^ 54 ≤ m.toNat < 2 ^ 55` (the normalized-significand invariant a caller establishes with
`fpr_ulsh_lzcnt64_top_bit`), and an interval on `e.toInt` keeping the packed exponent field
strictly between the subnormal marker `0` and the Inf/NaN marker `2047`. -/

/-- `FPR.make` in terms of the rounding-table bit, verbatim in the shape of the kernel's body. -/
private theorem make_eq_add_roundTableBit (s : UInt64) (e : Int32) (m : UInt64) :
    make s e m =
      s <<< 63 + (e + 1076).toUInt32.toUInt64 <<< 52 + (m >>> 2) + roundTableBit m := rfl

/-- `FPR.make_z` in terms of the rounding-table bit, verbatim in the shape of the kernel's
body. -/
private theorem make_z_eq_add_roundTableBit (s : UInt64) (e : Int32) (m : UInt64) :
    make_z s e m =
      s <<< 63 + ((e + 1076).toUInt32 &&& ((0 : UInt32) - (m >>> 54).toUInt32)).toUInt64 <<< 52
        + (m >>> 2) + roundTableBit m := rfl

/-- `FPR.make` assembles the sign and exponent fields and adds the round-to-nearest,
ties-to-even rounding of `m / 4`. -/
private theorem make_eq_roundQuarterTiesEven (s : UInt64) (e : Int32) (m : UInt64) :
    make s e m =
      s <<< 63 + (e + 1076).toUInt32.toUInt64 <<< 52
        + UInt64.ofNat (roundQuarterTiesEven m.toNat) := by
  rw [make_eq_add_roundTableBit, UInt64.add_assoc, shiftRight_two_add_roundTableBit]

/-- `FPR.make_z` assembles the sign and (zero-collapsing) exponent fields and adds the
round-to-nearest, ties-to-even rounding of `m / 4`. -/
private theorem make_z_eq_roundQuarterTiesEven (s : UInt64) (e : Int32) (m : UInt64) :
    make_z s e m =
      s <<< 63 + ((e + 1076).toUInt32 &&& ((0 : UInt32) - (m >>> 54).toUInt32)).toUInt64 <<< 52
        + UInt64.ofNat (roundQuarterTiesEven m.toNat) := by
  rw [make_z_eq_add_roundTableBit, UInt64.add_assoc, shiftRight_two_add_roundTableBit]

/-- The exponent word `(e + 1076).toUInt32.toUInt64` computes the biased exponent `e + 1076` on
the nose, provided no `Int32` wraparound can occur. The stated interval is the one under which
`FPR.make`'s packed exponent field stays inside the finite range. -/
private theorem FPR.toNat_biasedExponentWord (e : Int32) (h1 : -1076 ≤ e.toInt)
    (h2 : e.toInt ≤ 969) :
    (e + 1076).toUInt32.toUInt64.toNat = (e.toInt + 1076).toNat := by
  have h1076 : (1076 : Int32).toInt = 1076 := by decide
  have hadd : (e + 1076).toInt = e.toInt + 1076 := by
    rw [Int32.toInt_add, h1076, Int.bmod_eq_emod_of_lt (by omega)]
    omega
  have hnn : (0 : Int32) ≤ e + 1076 := by
    rw [Int32.le_iff_toInt_le, hadd, show (0 : Int32).toInt = 0 from by decide]
    omega
  rw [UInt32.toNat_toUInt64, Int32.toNat_toUInt32_of_le hnn, ← Int32.toNat_toInt, hadd]

/-- The word `FPR.make` builds, as a natural number: the three field contributions are simply
*added*, with no wraparound anywhere. The hypotheses are exactly what rules the wraparound out —
a single sign bit, an exponent word below `2046`, and a significand `m` below `2 ^ 55` (so
`m >>> 2 < 2 ^ 53`). Note that the significand contribution is *not* pre-masked into the low 52
bits: it exceeds `2 ^ 52`, and the excess carries into the exponent field. -/
private theorem FPR.toNat_make (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm : m.toNat < 2 ^ 55) :
    (make s e m).toNat =
      s.toNat * 2 ^ 63 + (e.toInt + 1076).toNat * 2 ^ 52 + roundQuarterTiesEven m.toNat := by
  have hA : (s <<< 63 : UInt64).toNat = s.toNat * 2 ^ 63 := by
    rw [UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  have hE : (e + 1076).toUInt32.toUInt64.toNat = (e.toInt + 1076).toNat :=
    FPR.toNat_biasedExponentWord e he1 he2
  have hEle : (e.toInt + 1076).toNat ≤ 2045 := by omega
  have hB : ((e + 1076).toUInt32.toUInt64 <<< 52 : UInt64).toNat =
      (e.toInt + 1076).toNat * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow, hE]
    omega
  have hR : roundQuarterTiesEven m.toNat ≤ 2 ^ 53 := by
    have := roundQuarterTiesEven_le_div_four_succ m.toNat
    omega
  rw [make_eq_roundQuarterTiesEven, UInt64.toNat_add, UInt64.toNat_add, hA, hB,
    toNat_ofNat_roundQuarterTiesEven]
  omega

/-- Decode round-trip for `FPR.make`, ordinary case: the rounded significand stays below `2 ^ 53`.
The sign bit is returned unchanged, the mantissa field is the significand with its implicit leading
bit stripped, and the exponent field is `e + 1077` — one more than the word `(e + 1076)` that was
shifted into place, because the significand's leading bit carried into it. -/
private theorem FPR.decode_make_of_no_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : roundQuarterTiesEven m.toNat < 2 ^ 53) :
    FPR.decode (make s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 1,
        mantissa := roundQuarterTiesEven m.toNat - 2 ^ 52 } := by
  have hb := (roundQuarterTiesEven_mem_of_normalized m.toNat hm1 hm2).1
  have hE : (e.toInt + 1076).toNat ≤ 2045 := by omega
  unfold FPR.decode
  rw [FPR.toNat_make s e m hs he1 he2 hm2]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, FPR.Bits.mk.injEq,
    decide_eq_decide]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Decode round-trip for `FPR.make`, rounding-carry case: rounding pushed the significand to
`2 ^ 53`, one bit too wide for the mantissa field. Because the fields are combined with plain
addition, the overflow carries into the exponent slot all by itself, producing exponent field
`e + 1078` (one more than the ordinary `e + 1077`) and mantissa `0`. That is precisely "increment
the exponent and halve the significand", so no explicit renormalization step is needed. -/
private theorem FPR.decode_make_of_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm2 : m.toNat < 2 ^ 55)
    (hc : roundQuarterTiesEven m.toNat = 2 ^ 53) :
    FPR.decode (make s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 2,
        mantissa := 0 } := by
  have hE : (e.toInt + 1076).toNat ≤ 2045 := by omega
  unfold FPR.decode
  rw [FPR.toNat_make s e m hs he1 he2 hm2]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, FPR.Bits.mk.injEq,
    decide_eq_decide]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Denotation of `FPR.make`, stated uniformly across the rounding carry: the word always denotes
`± roundQuarterTiesEven m * 2 ^ (e + 2)`, whether or not the significand carried out of the
mantissa field. In the carry case the exponent field is one larger and the mantissa is zero, and
the two changes cancel exactly — this is the statement that the self-normalizing carry does the
right thing. The hypothesis `e.toInt ≤ 968` keeps the exponent field below the Inf/NaN marker
`2047` even after the carry, and `-1076 ≤ e.toInt` keeps it above the subnormal marker `0`. -/
private theorem toRealBits_make (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 968)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    toRealBits (make s e m) =
      (if s.toNat = 1 then (-1 : ℝ) else 1) * (roundQuarterTiesEven m.toNat : ℝ) *
        (2 : ℝ) ^ (e.toInt + 2) := by
  obtain ⟨hlo, hhi⟩ := roundQuarterTiesEven_mem_of_normalized m.toNat hm1 hm2
  have hE : ((e.toInt + 1076).toNat : ℤ) = e.toInt + 1076 := Int.toNat_of_nonneg (by omega)
  have hEle : (e.toInt + 1076).toNat ≤ 2044 := by omega
  rcases lt_or_eq_of_le hhi with hcase | hcase
  · rw [toRealBits, FPR.decode_make_of_no_carry s e m hs he1 (by omega) hm1 hm2 hcase]
    unfold FPR.Bits.toReal
    simp only [decide_eq_true_eq]
    rw [ite_eq_right (by omega : ¬ (e.toInt + 1076).toNat + 1 = 0),
      ite_eq_right (by omega : ¬ (e.toInt + 1076).toNat + 1 = 2047)]
    have hcast : (((roundQuarterTiesEven m.toNat - 2 ^ 52 : ℕ)) : ℝ) =
        (roundQuarterTiesEven m.toNat : ℝ) - 2 ^ 52 := by
      rw [Nat.cast_sub hlo]; norm_num
    have hexp : (((e.toInt + 1076).toNat + 1 : ℕ) : ℤ) - 1023 = e.toInt + 54 := by
      push_cast [hE]; ring
    rw [hcast, hexp,
      show (2 : ℝ) ^ (e.toInt + 54) = (2 : ℝ) ^ (e.toInt + 2) * 2 ^ (52 : ℕ) from by
        rw [show e.toInt + 54 = (e.toInt + 2) + (52 : ℤ) from by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num]
    field_simp
    ring
  · rw [toRealBits, FPR.decode_make_of_carry s e m hs he1 (by omega) hm2 hcase]
    unfold FPR.Bits.toReal
    simp only [decide_eq_true_eq]
    rw [ite_eq_right (by omega : ¬ (e.toInt + 1076).toNat + 2 = 0),
      ite_eq_right (by omega : ¬ (e.toInt + 1076).toNat + 2 = 2047)]
    have hexp : (((e.toInt + 1076).toNat + 2 : ℕ) : ℤ) - 1023 = e.toInt + 55 := by
      push_cast [hE]; ring
    rw [hexp, hcase]
    push_cast
    rw [show (2 : ℝ) ^ (e.toInt + 55) = (2 : ℝ) ^ (e.toInt + 2) * 2 ^ (53 : ℕ) from by
      rw [show e.toInt + 55 = (e.toInt + 2) + (53 : ℤ) from by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num]
    split_ifs <;> norm_num <;> ring

/-- `FPR.make` is the correctly-rounded encoder of `± m * 2 ^ e`: it denotes that value up to
relative error `2 ^ (-53)`. This packages `abs_roundQuarterTiesEven_sub_div_four_le` (rounding
moves the significand by at most half a unit) together with `toRealBits_make` (the packing,
including its self-normalizing carry, is exact), and is the final-assembly half of the
per-operation `2 ^ (-52)` relative-error bounds.

This route is direct, phrased in the pre-rounding pair `(m, e)` that `FPR.make` consumes, rather
than through the general-theory `FPR.ulpOfExponent` / `FPR.ulpOfExponent_le_two_pow_neg52_mul_abs`
(which bound the spacing between adjacent representable values at a *decoded* exponent field).
The two routes agree in substance — in the no-carry case, `FPR.ulpOfExponent` at the decoded
output's exponent field `(e.toInt + 1076).toNat + 1` works out to the same scale factor
`2 ^ (e.toInt + 2)` that `toRealBits_make` produces — but formally connecting them would need that
equality re-derived alongside a case split on the rounding carry, for no shorter a proof than the
direct route already gives. -/
private theorem abs_toRealBits_make_sub_le (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 968)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    |toRealBits (make s e m) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| ≤
      (2 : ℝ) ^ (-(53 : ℤ)) *
        |(if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| := by
  rw [toRealBits_make s e m hs he1 he2 hm1 hm2]
  have hpe : (0 : ℝ) < (2 : ℝ) ^ e.toInt := zpow_pos (by norm_num) _
  have hsg1 : |(if s.toNat = 1 then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> norm_num
  have hpow : (2 : ℝ) ^ (e.toInt + 2) = (2 : ℝ) ^ e.toInt * 4 := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  have hσ := abs_roundQuarterTiesEven_sub_div_four_le m.toNat
  have hm : (2 : ℝ) ^ (54 : ℕ) ≤ (m.toNat : ℝ) := by exact_mod_cast hm1
  have hc : (2 : ℝ) ^ (-(53 : ℤ)) * (2 : ℝ) ^ (54 : ℕ) = 2 := by
    rw [← zpow_natCast (2 : ℝ) 54, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (-(53 : ℤ)) := zpow_pos (by norm_num) _
  rw [hpow,
    show (if s.toNat = 1 then (-1 : ℝ) else 1) * (roundQuarterTiesEven m.toNat : ℝ) *
          ((2 : ℝ) ^ e.toInt * 4) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt =
      (if s.toNat = 1 then (-1 : ℝ) else 1) * (2 : ℝ) ^ e.toInt *
        (4 * ((roundQuarterTiesEven m.toNat : ℝ) - (m.toNat : ℝ) / 4)) from by ring]
  simp only [abs_mul, hsg1, one_mul, abs_of_pos hpe,
    abs_of_nonneg (show (0 : ℝ) ≤ (m.toNat : ℝ) by positivity),
    show |(4 : ℝ)| = 4 from by norm_num]
  have h1 : (2 : ℝ) ^ e.toInt * (4 * |(roundQuarterTiesEven m.toNat : ℝ) - (m.toNat : ℝ) / 4|) ≤
      (2 : ℝ) ^ e.toInt * 2 := by
    have : (4 : ℝ) * |(roundQuarterTiesEven m.toNat : ℝ) - (m.toNat : ℝ) / 4| ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_left this (le_of_lt hpe)
  have h2 : (2 : ℝ) ^ e.toInt * 2 ≤
      (2 : ℝ) ^ (-(53 : ℤ)) * ((m.toNat : ℝ) * (2 : ℝ) ^ e.toInt) := by
    have hstep : (2 : ℝ) ^ (-(53 : ℤ)) * (2 : ℝ) ^ (54 : ℕ) ≤
        (2 : ℝ) ^ (-(53 : ℤ)) * (m.toNat : ℝ) := mul_le_mul_of_nonneg_left hm (le_of_lt hcpos)
    rw [hc] at hstep
    nlinarith
  exact h1.trans h2

/-- On a normalized significand `FPR.make_z` is `FPR.make`. The extra masking in `make_z` keys on
`m >>> 54`, i.e. on the *significand* being small, not on the exponent underflowing; the hypothesis
`2 ^ 54 ≤ m.toNat` is exactly the regime where that mask is all-ones and the two functions agree,
and no assumption on `e` is needed. -/
private theorem FPR.make_z_eq_make (s : UInt64) (e : Int32) (m : UInt64)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    make_z s e m = make s e m := by
  have hsh : (m >>> 54 : UInt64) = 1 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  have hmask : ((0 : UInt32) - (m >>> 54).toUInt32) = 4294967295 := by
    rw [hsh]; decide
  unfold make make_z
  simp only [hmask]
  have hand : ∀ x : UInt32, x &&& 4294967295 = x := by
    intro x
    have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
    rw [← UInt32.toNat_inj, UInt32.toNat_and]
    rw [show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hand]

/-- The packed result of `FPR.make` is normal, on a normalized significand inside the exponent
window.

This is the shared final step of every closure proof. `FPR.decode_make_of_no_carry` puts the
biased exponent at `(e + 1076) + 1`, which the window `-1076 ≤ e ≤ 969` places inside
`[1, 2046]`. A rounding carry writes `(e + 1076) + 2` instead, which would reach the non-finite
marker `2047` at the top of the window — so each caller must supply the fact that its own
pipeline cannot carry there. -/
private theorem FPR.isNormal_make (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : e.toInt = 969 → roundQuarterTiesEven m.toNat < 2 ^ 53) :
    FPR.IsNormal (make s e m) := by
  unfold FPR.IsNormal FPR.Bits.IsNormal
  have hround := roundQuarterTiesEven_mem_of_normalized _ hm1 hm2
  rcases lt_or_ge (roundQuarterTiesEven m.toNat) (2 ^ 53) with hno | hcar
  · rw [FPR.decode_make_of_no_carry s e m hs he1 he2 hm1 hm2 hno]
    simp only
    omega
  · have hceq : roundQuarterTiesEven m.toNat = 2 ^ 53 := by omega
    have h968 : e.toInt ≤ 968 := by
      by_contra hc
      exact absurd (hnc (by omega)) (by omega)
    rw [FPR.decode_make_of_carry s e m hs he1 he2 hm2 hceq]
    simp only
    omega

/-- Decode round-trip for `FPR.make_z`, ordinary case. -/
private theorem FPR.decode_make_z_of_no_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : roundQuarterTiesEven m.toNat < 2 ^ 53) :
    FPR.decode (make_z s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 1,
        mantissa := roundQuarterTiesEven m.toNat - 2 ^ 52 } := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact FPR.decode_make_of_no_carry s e m hs he1 he2 hm1 hm2 hnc

/-- Decode round-trip for `FPR.make_z`, rounding-carry case. -/
private theorem FPR.decode_make_z_of_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hc : roundQuarterTiesEven m.toNat = 2 ^ 53) :
    FPR.decode (make_z s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 2,
        mantissa := 0 } := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact FPR.decode_make_of_carry s e m hs he1 he2 hm2 hc

/-- `FPR.make_z` denotes `± m * 2 ^ e` up to relative error `2 ^ (-53)` on a normalized
significand. -/
private theorem abs_toRealBits_make_z_sub_le (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 968)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    |toRealBits (make_z s e m) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| ≤
      (2 : ℝ) ^ (-(53 : ℤ)) *
        |(if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact abs_toRealBits_make_sub_le s e m hs he1 he2 hm1 hm2

/-! ### The `m = 0` branch of `FPR.make_z`

The denotation lemmas above all require `2 ^ 54 ≤ m.toNat`, the normalized-significand range a
caller establishes with `fpr_ulsh_lzcnt64_top_bit` — which excludes exactly the collapsed case
`m = 0` that `FPR.make_z`'s extra `&&& ((0 : UInt32) - (m >>> 54).toUInt32)` mask exists to
handle (exact cancellation in `FPR.add`, or a zero operand in `FPR.mul` / `FPR.div`). On `m = 0`
that mask is `(0 : UInt32) - 0 = 0`, so it clears the exponent field outright regardless of what
`e` was computed, and the rounding fold of `m >>> 2` is `0` too: `FPR.make_z s e 0` is exactly
IEEE-754's signed-zero bit pattern, denoting `0`. This is the fact `or_fold_shiftRight_eq_zero_iff`
/ `stickyShift_eq_zero_iff` exist to feed: a caller who has shown a working significand's
pre-fold value was `0` (via those two) lands here for the resulting `FPR.make_z` call's
denotation. -/

/-- `FPR.make_z` collapses to the signed-zero bit pattern `s <<< 63` on a zero significand: the
mask `(0 : UInt32) - (m >>> 54).toUInt32` is `0` when `m = 0`, clearing the exponent field, and
`m >>> 2 = 0` together with `roundTableBit 0 = 0` clears the mantissa field. -/
private theorem make_z_of_zero (s : UInt64) (e : Int32) : make_z s e 0 = s <<< 63 := by
  rw [make_z_eq_roundQuarterTiesEven]
  have h0 : ((0 : UInt64) >>> 54).toUInt32 = 0 := by decide
  have hr : roundQuarterTiesEven (0 : UInt64).toNat = 0 := by decide
  rw [h0, hr]
  simp

/-- Decode of `FPR.make_z` on a zero significand: the sign bit is returned unchanged, and both
the exponent and mantissa fields are `0` — IEEE-754's signed-zero bit pattern — independently of
`e`. -/
private theorem FPR.decode_make_z_of_zero (s : UInt64) (e : Int32) (hs : s.toNat ≤ 1) :
    FPR.decode (make_z s e 0) =
      { sign := decide (s.toNat = 1), exponent := 0, mantissa := 0 } := by
  rw [make_z_of_zero]
  have hA : (s <<< 63 : UInt64).toNat = s.toNat * 2 ^ 63 := by
    rw [UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  unfold FPR.decode
  rw [hA]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, FPR.Bits.mk.injEq,
    decide_eq_decide]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- `FPR.make_z` denotes exactly `0` on a zero significand, for any sign `s` and any exponent
`e`: the collapsed-significand counterpart to `abs_toRealBits_make_z_sub_le`'s normalized-range
relative-error bound. -/
private theorem toRealBits_make_z_of_zero (s : UInt64) (e : Int32) (hs : s.toNat ≤ 1) :
    toRealBits (make_z s e 0) = 0 := by
  unfold toRealBits
  rw [FPR.decode_make_z_of_zero s e hs]
  unfold FPR.Bits.toReal
  norm_num

/-! ### Sanity witnesses -/

/-- The eight rounded quotients for the eight low-bit patterns of the working significand:
`0.00, 0.25, 0.50, 0.75, 1.00, 1.25, 1.50, 1.75` round to `0, 0, 0, 1, 1, 1, 2, 2`. -/
example : (List.range 8).map roundQuarterTiesEven = [0, 0, 0, 1, 1, 1, 2, 2] := by decide

/-- The eight table entries of `0xC8 = 0b11001000`. -/
example :
    (List.range 8).map (fun i => (roundTableBit (UInt64.ofNat i)).toNat) =
      [0, 0, 0, 1, 0, 0, 1, 1] := by decide

end

end Falcon.Concrete.FPRBridge
