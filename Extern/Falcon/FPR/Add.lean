/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPR.AddPipeline
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPR.AddPipeline

/-!
# Correct rounding of `FPR.add` and `FPR.sub`

The error analysis of the `FPR.add` pipeline named in `Extern.Falcon.FPR.AddPipeline`: the
signed denotation of the two aligned operands, the alignment error, the rounding fold, the error
budget and the exact-cancellation branch, giving `add_error` / `sub_error` together with the
closure facts `add_isNormalOrZero` / `sub_isNormalOrZero`.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## (IV) Signed denotation of the two pipeline operands -/

private theorem addPipeline_sign_x' (a b : FPR) :
    (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1)
      = (if (FPR.decode (addPipeline a b).x').sign then (-1 : ℝ) else 1) := by
  rw [addPipeline_sx_toNat]
  split_ifs <;> simp_all

private theorem addPipeline_sign_y' (a b : FPR) :
    (if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1)
      = (if (FPR.decode (addPipeline a b).y').sign then (-1 : ℝ) else 1) := by
  rw [addPipeline_sy_toNat]
  split_ifs <;> simp_all

private theorem addPipeline_toReal_x'_eq (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    toReal (addPipeline a b).x' =
      (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        ((addPipeline a b).xu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  obtain ⟨h0, h2047⟩ := addPipeline_x'_isNormal a b ha hb
  rw [addPipeline_sign_x', addPipeline_xu_toNat, addPipeline_ex'_toInt, addPipeline_ex_eq_exponent]
  change (FPR.decode (addPipeline a b).x').toReal = _
  rw [toReal_eq_significand_mul_two_zpow h0 h2047]
  push_cast
  rw [show (((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1078)
      = (((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1075) + (-3 : ℤ) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

private theorem addPipeline_ey_toInt_eq (a b : FPR) :
    ((FPR.decode (addPipeline a b).y').exponent : ℤ) - 1078
      = (addPipeline a b).ex'.toInt - ((addPipeline a b).n.toNat : ℤ) := by
  have hn := addPipeline_n_toNat a b
  have hle := addPipeline_ey_le_ex a b
  have hex' := addPipeline_ex'_toInt a b
  rw [← addPipeline_ey_eq_exponent, hex', hn]
  omega

private theorem addPipeline_toReal_y'_eq (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    toReal (addPipeline a b).y' =
      (if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  obtain ⟨h0, h2047⟩ := addPipeline_y'_isNormal a b ha hb
  rw [addPipeline_sign_y', addPipeline_yuRaw_toNat]
  change (FPR.decode (addPipeline a b).y').toReal = _
  rw [toReal_eq_significand_mul_two_zpow h0 h2047]
  push_cast
  rw [show (((FPR.decode (addPipeline a b).y').exponent : ℤ) - 1075)
      = ((((FPR.decode (addPipeline a b).y').exponent : ℤ) - 1078)) + (3 : ℤ) by ring,
    addPipeline_ey_toInt_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  field_simp
  ring

/-! ## (V) The alignment error -/

private theorem stickyShift_of_dvd (v k : ℕ) (h : v % 2 ^ k = 0) : stickyShift v k = v / 2 ^ k := by
  unfold stickyShift
  rw [ite_eq_left h, Nat.or_zero, Nat.shiftRight_eq_div_pow]

private theorem addPipeline_align_lt (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    |((addPipeline a b).yu.toNat : ℝ)
        - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| < 1 := by
  by_cases hn : (addPipeline a b).n.toNat < 60
  · obtain ⟨h1, h2⟩ := addPipeline_yu_real_bracket_yuRaw a b hn
    rw [abs_lt]
    constructor <;> linarith
  · have hz : (addPipeline a b).yu = 0 := addPipeline_yu_eq_zero a b (by omega)
    have hyu : ((addPipeline a b).yu.toNat : ℝ) = 0 := by rw [hz]; norm_num
    have hlt : (addPipeline a b).yu_.toNat < 2 ^ (addPipeline a b).n.toNat := by
      have h56 := (addPipeline_yuRaw_mem a b ha hb).2
      have : (2 : ℕ) ^ 56 ≤ 2 ^ (addPipeline a b).n.toNat :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hltR : ((addPipeline a b).yu_.toNat : ℝ) < 2 ^ (addPipeline a b).n.toNat := by
      exact_mod_cast hlt
    have hpos : (0 : ℝ) < 2 ^ (addPipeline a b).n.toNat := by positivity
    rw [hyu, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    rw [div_lt_one hpos]
    exact hltR

private theorem addPipeline_align_exact (a b : FPR) (h : (addPipeline a b).n.toNat ≤ 3) :
    ((addPipeline a b).yu.toNat : ℝ)
      = ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat := by
  have hk : ((addPipeline a b).n &&& 63).toNat = (addPipeline a b).n.toNat :=
    toNat_and_63_of_lt (by omega)
  have hv : (addPipeline a b).yu'.toNat = (addPipeline a b).yu_.toNat := by
    rw [addPipeline_yu'_eq_yuRaw a b (by omega)]
  have hdvd : 2 ^ (addPipeline a b).n.toNat ∣ (addPipeline a b).yu_.toNat := by
    rw [addPipeline_yuRaw_toNat]
    have h8 : (2 : ℕ) ^ (addPipeline a b).n.toNat ∣ 8 := by
      have := pow_dvd_pow 2 h
      rwa [show (2 : ℕ) ^ 3 = 8 from by norm_num] at this
    exact h8.trans (dvd_mul_right 8 _)
  have hnat : (addPipeline a b).yu.toNat
      = (addPipeline a b).yu_.toNat / 2 ^ (addPipeline a b).n.toNat := by
    rw [addPipeline_yu_toNat, hk, hv]
    exact stickyShift_of_dvd _ _ (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  rw [hnat, Nat.cast_div hdvd (by positivity)]
  norm_num

private theorem addPipeline_abs_toReal_le (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b) :
    |toReal (addPipeline a b).y'| ≤ |toReal (addPipeline a b).x'| := by
  by_contra hc
  push Not at hc
  have hkey := (FPR.Bits.abs_toReal_lt_iff_magKey_lt (FPR.decode (addPipeline a b).x')
    (FPR.decode (addPipeline a b).y') (FPR.decode_mantissa_lt _) (FPR.decode_mantissa_lt _)
    (addPipeline_x'_isNormal a b ha hb).2 (addPipeline_y'_isNormal a b ha hb).2).mp hc
  exact absurd (addPipeline_swap_cases a b).2 (by omega)

/-! ## (VI) The combined significand's value -/

private theorem addPipeline_abs_toReal_y'_eq (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b) :
    |toReal (addPipeline a b).y'| =
      (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  rw [addPipeline_toReal_y'_eq a b ha hb, abs_mul, abs_mul,
    show |(if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1)| = 1 from by
      split_ifs <;> norm_num,
    abs_of_nonneg (show (0 : ℝ) ≤ ((addPipeline a b).yu_.toNat : ℝ)
      / 2 ^ (addPipeline a b).n.toNat by positivity),
    abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt from
      zpow_pos (by norm_num) _), one_mul]

private theorem addPipeline_Yprime_le_xu (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat
      ≤ ((addPipeline a b).xu.toNat : ℝ) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have h := addPipeline_abs_toReal_le a b ha hb
  rw [addPipeline_abs_toReal_y'_eq a b ha hb,
    addPipeline_abs_toReal_x'_eq a b (addPipeline_x'_isNormal a b ha hb).1
      (addPipeline_x'_isNormal a b ha hb).2] at h
  exact le_of_mul_le_mul_right (by linarith) hp

private theorem addPipeline_yu_le_xu (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (addPipeline a b).yu.toNat ≤ (addPipeline a b).xu.toNat := by
  have h1 := addPipeline_align_lt a b ha hb
  have h2 := addPipeline_Yprime_le_xu a b ha hb
  rw [abs_lt] at h1
  have : ((addPipeline a b).yu.toNat : ℝ) < ((addPipeline a b).xu.toNat : ℝ) + 1 := by linarith
  have hcast : ((addPipeline a b).yu.toNat : ℝ) < (((addPipeline a b).xu.toNat + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have := Nat.cast_lt (α := ℝ).mp hcast
  omega

private theorem addPipeline_sigma_rel (a b : FPR) :
    (if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1)
      = (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
        (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) := by
  rcases addPipeline_sx_eq_zero_or_one a b with hx | hx <;>
    rcases addPipeline_sy_eq_zero_or_one a b with hy | hy <;> rw [hx, hy] <;>
      simp only [toNat_lit0, toNat_lit1, show ((0 : UInt32) = 1) = False from by simp,
        show ((1 : UInt32) = 0) = False from by simp] <;> norm_num

private theorem addPipeline_zu_real (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    ((addPipeline a b).zu.toNat : ℝ)
      = ((addPipeline a b).xu.toNat : ℝ)
        + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
          ((addPipeline a b).yu.toNat : ℝ) := by
  have hle := addPipeline_yu_le_xu a b ha hb
  have hxu := (addPipeline_xu_mem a b ha hb).2
  by_cases hs : (addPipeline a b).sx = (addPipeline a b).sy
  · rw [ite_eq_left hs, addPipeline_zu_eq_add_of_sx_eq_sy a b hs, UInt64.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega)]
    push_cast
    ring
  · rw [ite_eq_right hs, addPipeline_zu_toNat_eq_of_sx_ne_sy a b hs hle, Nat.cast_sub hle]
    ring

private theorem addPipeline_S_eq (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    toReal a + toReal b =
      (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).xu.toNat : ℝ)
          + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
            (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)) *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  rw [← addPipeline_sum_eq a b, addPipeline_toReal_x'_eq a b ha hb,
    addPipeline_toReal_y'_eq a b ha hb, addPipeline_sigma_rel a b]
  ring

/-! ## (VII) Exponent bounds and the rounding fold -/

private theorem addPipeline_ex'_le (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (addPipeline a b).ex'.toInt ≤ 968 := by
  have h1 := addPipeline_ex'_toInt a b
  have h2 := addPipeline_ex_lt a b
  have h3 : (addPipeline a b).ex.toNat ≠ 2047 := by
    rw [addPipeline_ex_eq_exponent]; exact (addPipeline_x'_isNormal a b ha hb).2
  omega

private theorem addPipeline_ex'_ge (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    ((addPipeline a b).n.toNat : ℤ) - 1077 ≤ (addPipeline a b).ex'.toInt := by
  have h1 := addPipeline_ex'_toInt a b
  have h2 := addPipeline_n_toNat a b
  have h3 := addPipeline_ey_le_ex a b
  have h4 : (addPipeline a b).ey.toNat ≠ 0 := by
    rw [addPipeline_ey_eq_exponent]; exact (addPipeline_y'_isNormal a b ha hb).1
  omega

private theorem addPipeline_ex'_ge' (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (-1077 : ℤ) ≤ (addPipeline a b).ex'.toInt := by
  have := addPipeline_ex'_ge a b ha hb
  omega

private theorem addPipeline_zu''_sticky (a b : FPR) :
    (addPipeline a b).zu''.toNat = stickyShift (addPipeline a b).zu'.toNat 9 := by
  rw [addPipeline_zu'', toNat_or_fold_shiftRight_nine]

private theorem addPipeline_zu'_ge (a b : FPR) (h : (addPipeline a b).zu ≠ 0) :
    2 ^ 63 ≤ (addPipeline a b).zu'.toNat := by
  rw [addPipeline_zu', addPipeline_c]
  exact fpr_ulsh_lzcnt64_top_bit _ h

/-- The nine-bit rounding fold moves the working value by less than `2 ^ 9` ulps at the
post-renormalisation scale. -/
private theorem addPipeline_fold_abs_lt (a b : FPR) :
    |((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ) - ((addPipeline a b).zu'.toNat : ℝ)|
      < 2 ^ (9 : ℕ) := by
  have h1 := stickyShift_mul_lt (addPipeline a b).zu'.toNat 9
  have h2 := lt_stickyShift_mul_add (addPipeline a b).zu'.toNat 9
  rw [← addPipeline_zu''_sticky] at h1 h2
  have h1' : ((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ)
      < ((addPipeline a b).zu'.toNat : ℝ) + 2 ^ (9 : ℕ) := by exact_mod_cast h1
  have h2' : ((addPipeline a b).zu'.toNat : ℝ)
      < ((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ) + 2 ^ (9 : ℕ) := by exact_mod_cast h2
  rw [abs_lt]
  constructor <;> linarith

/-- The exponent identity `ex''' = ex'' + 9`, as plain integers. -/
private theorem addPipeline_ex'''_eq_ex''_add (a b : FPR) :
    (addPipeline a b).ex'''.toInt = (addPipeline a b).ex''.toInt + 9 := by
  rw [addPipeline_ex'''_toInt, addPipeline_ex''_toInt]

/-- The rounding fold's contribution to the error, relative to the pre-fold working value. -/
private theorem addPipeline_fold_error (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt) :
    |((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt|
      ≤ (2 : ℝ) ^ (-(54 : ℤ)) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt) := by
  have hren := addPipeline_renorm_value_preserving a b hzu hb31
  have hq : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex''.toInt := zpow_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt * 2 ^ (9 : ℕ) := by
    rw [addPipeline_ex'''_eq_ex''_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [← hren, hsplit,
    show ((addPipeline a b).zu''.toNat : ℝ) *
        ((2 : ℝ) ^ (addPipeline a b).ex''.toInt * 2 ^ (9 : ℕ))
        - ((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt *
        (((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ)
          - ((addPipeline a b).zu'.toNat : ℝ)) from by ring,
    abs_mul, abs_of_pos hq]
  have hf := addPipeline_fold_abs_lt a b
  have hge : (2 : ℝ) ^ (63 : ℕ) ≤ ((addPipeline a b).zu'.toNat : ℝ) := by
    exact_mod_cast addPipeline_zu'_ge a b hzu
  have hc : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (63 : ℕ) = 2 ^ (9 : ℕ) := by
    rw [← zpow_natCast (2 : ℝ) 63, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
  have hstep : (2 : ℝ) ^ (9 : ℕ) ≤ (2 : ℝ) ^ (-(54 : ℤ)) * ((addPipeline a b).zu'.toNat : ℝ) := by
    have := mul_le_mul_of_nonneg_left hge hcpos.le
    rw [hc] at this
    linarith
  calc (2 : ℝ) ^ (addPipeline a b).ex''.toInt *
        |((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ) - ((addPipeline a b).zu'.toNat : ℝ)|
      ≤ (2 : ℝ) ^ (addPipeline a b).ex''.toInt * (2 : ℝ) ^ (9 : ℕ) :=
        mul_le_mul_of_nonneg_left hf.le hq.le
    _ ≤ (2 : ℝ) ^ (-(54 : ℤ)) *
        (((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt) := by
        nlinarith

/-! ## (VIII) The pre-rounding working value -/

private theorem addPipeline_abs_sigma (a b : FPR) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1)| = 1 := by
  split_ifs <;> norm_num

private theorem addPipeline_abs_sigma_tau (a b : FPR) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1)| = 1 := by
  rw [abs_mul, addPipeline_abs_sigma]
  split_ifs <;> norm_num

private theorem addPipeline_p_ge (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (2 : ℝ) ^ (-(1077 : ℤ)) ≤ (2 : ℝ) ^ (addPipeline a b).ex'.toInt :=
  zpow_le_zpow_right₀ (by norm_num) (addPipeline_ex'_ge' a b ha hb)

/-- The pre-rounding working value `± zu * 2 ^ ex'` is within relative `(2/3) * 2 ^ (-54)` of the
exact sum, and its magnitude stays at or above the smallest normal magnitude. The three branches
are: matching signs (no cancellation), differing signs with an exponent gap of at most `3` (where
the `× 8` scaling of the significands makes the alignment shift exact, so the working value is the
exact sum), and differing signs with a larger gap (where cancellation is bounded away by the
leading bits of the two significands). -/
private theorem addPipeline_pre_round (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hmin : FPR.minNormalReal ≤ |toReal a + toReal b|) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)|
      ≤ 2 / 3 * (2 : ℝ) ^ (-(54 : ℤ)) * |toReal a + toReal b|
    ∧ FPR.minNormalReal ≤
        ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have hS := addPipeline_S_eq a b ha hb
  have hzr := addPipeline_zu_real a b ha hb
  have hal := addPipeline_align_lt a b ha hb
  have hxm := addPipeline_xu_mem a b ha hb
  have hym := addPipeline_yuRaw_mem a b ha hb
  have hYple := addPipeline_Yprime_le_xu a b ha hb
  have hYpnn : (0 : ℝ) ≤ ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat := by
    positivity
  have hYvnn : (0 : ℝ) ≤ ((addPipeline a b).yu.toNat : ℝ) := by positivity
  have hX55 : (2 : ℝ) ^ (55 : ℕ) ≤ ((addPipeline a b).xu.toNat : ℝ) := by exact_mod_cast hxm.1
  have hpge := addPipeline_p_ge a b ha hb
  -- the two abs computations
  have hdiff : (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)
      = ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1)) *
        ((((addPipeline a b).yu.toNat : ℝ)
            - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
          (2 : ℝ) ^ (addPipeline a b).ex'.toInt) := by
    rw [hzr, hS]; ring
  have habsdiff : |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)|
      = |((addPipeline a b).yu.toNat : ℝ)
          - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
    rw [hdiff, abs_mul, addPipeline_abs_sigma_tau, one_mul, abs_mul, abs_of_pos hp]
  have habsS : |toReal a + toReal b|
      = |((addPipeline a b).xu.toNat : ℝ)
          + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
            (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)| *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
    rw [hS, abs_mul, abs_mul, addPipeline_abs_sigma, one_mul, abs_of_pos hp]
  have hc55 : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (55 : ℕ) = 2 := by
    rw [mul_comm, two_pow_mul_zpow]; norm_num
  have hc52 : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (52 : ℕ) = 1 / 4 := by
    rw [mul_comm, two_pow_mul_zpow]; norm_num
  have hmn : FPR.minNormalReal = (2 : ℝ) ^ (-(1022 : ℤ)) := rfl
  by_cases hs : (addPipeline a b).sx = (addPipeline a b).sy
  · -- matching signs: no cancellation
    rw [ite_eq_left hs] at habsS hzr
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((addPipeline a b).xu.toNat : ℝ)
      + 1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat))] at habsS
    rw [abs_lt] at hal
    constructor
    · rw [habsdiff, habsS]
      have hbig : (1 : ℝ) ≤ 2 / 3 * (2 : ℝ) ^ (-(54 : ℤ)) *
          (((addPipeline a b).xu.toNat : ℝ)
            + 1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)) := by
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
        nlinarith [hc55]
      have hsmall : |((addPipeline a b).yu.toNat : ℝ)
          - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      nlinarith
    · rw [hzr, hmn]
      have : (2 : ℝ) ^ (-(1022 : ℤ)) = (2 : ℝ) ^ (55 : ℕ) * (2 : ℝ) ^ (-(1077 : ℤ)) := by
        rw [two_pow_mul_zpow]; norm_num
      rw [this]
      nlinarith
  · -- differing signs: cancellation
    rw [ite_eq_right hs] at habsS hzr
    have hYleX : (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)
        ≤ ((addPipeline a b).xu.toNat : ℝ) := hYple
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((addPipeline a b).xu.toNat : ℝ)
      + -1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat))] at habsS
    by_cases hn : (addPipeline a b).n.toNat ≤ 3
    · -- exact alignment: the working value *is* the exact sum
      have hex := addPipeline_align_exact a b hn
      constructor
      · rw [habsdiff, hex, sub_self, abs_zero, zero_mul]
        have : (0 : ℝ) ≤ |toReal a + toReal b| := abs_nonneg _
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
        nlinarith
      · rw [hzr, hex]
        rw [habsS] at hmin
        linarith
    · -- gap of at least 4: cancellation bounded away
      push Not at hn
      have hYplt : (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)
          < (2 : ℝ) ^ (52 : ℕ) := by
        have hpn : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).n.toNat := by positivity
        rw [div_lt_iff₀ hpn]
        have h1 : ((addPipeline a b).yu_.toNat : ℝ) < (2 : ℝ) ^ (56 : ℕ) := by exact_mod_cast hym.2
        have h2 : (2 : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (addPipeline a b).n.toNat := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
        nlinarith
      rw [abs_lt] at hal
      constructor
      · rw [habsdiff, habsS]
        have hbig : (1 : ℝ) ≤ 2 / 3 * (2 : ℝ) ^ (-(54 : ℤ)) *
            (((addPipeline a b).xu.toNat : ℝ)
              + -1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)) := by
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
          nlinarith [hc55, hc52]
        have hsmall : |((addPipeline a b).yu.toNat : ℝ)
            - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        nlinarith
      · rw [hzr, hmn]
        have hpge4 : (2 : ℝ) ^ (-(1073 : ℤ)) ≤ (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
          refine zpow_le_zpow_right₀ (by norm_num) ?_
          have := addPipeline_ex'_ge a b ha hb
          omega
        have hkey : (2 : ℝ) ^ (54 : ℕ) ≤ ((addPipeline a b).xu.toNat : ℝ)
            + -1 * ((addPipeline a b).yu.toNat : ℝ) := by
          have h55 : (2 : ℝ) ^ (55 : ℕ) = 2 * (2 : ℝ) ^ (54 : ℕ) := by norm_num
          have h52 : (2 : ℝ) ^ (52 : ℕ) = (2 : ℝ) ^ (54 : ℕ) / 4 := by norm_num
          have h54 : (1 : ℝ) ≤ (2 : ℝ) ^ (54 : ℕ) := by norm_num
          nlinarith
        have hlow : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ (2 : ℝ) ^ (54 : ℕ) * (2 : ℝ) ^ (-(1073 : ℤ)) := by
          rw [two_pow_mul_zpow]
          exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
        have hpos54 : (0 : ℝ) < (2 : ℝ) ^ (54 : ℕ) := by positivity
        calc (2 : ℝ) ^ (-(1022 : ℤ))
            ≤ (2 : ℝ) ^ (54 : ℕ) * (2 : ℝ) ^ (-(1073 : ℤ)) := hlow
          _ ≤ (2 : ℝ) ^ (54 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt :=
              mul_le_mul_of_nonneg_left hpge4 hpos54.le
          _ ≤ (((addPipeline a b).xu.toNat : ℝ) + -1 * ((addPipeline a b).yu.toNat : ℝ)) *
                (2 : ℝ) ^ (addPipeline a b).ex'.toInt :=
              mul_le_mul_of_nonneg_right hkey hp.le

/-! ## (IX) Absolute error forms and the exponent window -/

/-- The alignment error, in absolute terms: the pre-rounding working value is within one ulp at
the working scale `2 ^ ex'` of the exact sum, unconditionally. -/
private theorem addPipeline_pre_round_abs (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)|
      ≤ (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have hS := addPipeline_S_eq a b ha hb
  have hzr := addPipeline_zu_real a b ha hb
  have hal := addPipeline_align_lt a b ha hb
  have hdiff : (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)
      = ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1)) *
        ((((addPipeline a b).yu.toNat : ℝ)
            - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
          (2 : ℝ) ^ (addPipeline a b).ex'.toInt) := by
    rw [hzr, hS]; ring
  rw [hdiff, abs_mul, addPipeline_abs_sigma_tau, one_mul, abs_mul, abs_of_pos hp]
  nlinarith [hal.le]

/-- The rounding fold's contribution, as a difference at the post-renormalisation scale. -/
private theorem addPipeline_fold_diff_eq (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt) :
    ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt *
        (((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ)
          - ((addPipeline a b).zu'.toNat : ℝ)) := by
  have hren := addPipeline_renorm_value_preserving a b hzu hb31
  have hsplit : (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt * 2 ^ (9 : ℕ) := by
    rw [addPipeline_ex'''_eq_ex''_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [← hren, hsplit]
  ring

private theorem addPipeline_fold_abs_error (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt) :
    |((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt|
      ≤ (2 : ℝ) ^ (9 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex''.toInt := zpow_pos (by norm_num) _
  rw [addPipeline_fold_diff_eq a b hzu hb31, abs_mul, abs_of_pos hq]
  have hf := addPipeline_fold_abs_lt a b
  nlinarith [hf.le]

/-- The final exponent handed to the assembly stays inside the window the encoder needs: the
lower end comes from the result not underflowing into the subnormal band, the upper end from it
not overflowing past the largest finite magnitude. -/
private theorem addPipeline_ex'''_window (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt)
    (hlo : FPR.minNormalReal ≤
      ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
    (hhi : ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt
      < (2 : ℝ) ^ (1024 : ℤ)) :
    -1076 ≤ (addPipeline a b).ex'''.toInt ∧ (addPipeline a b).ex'''.toInt ≤ 969 := by
  have hren := addPipeline_renorm_value_preserving a b hzu hb31
  have hq : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex''.toInt := zpow_pos (by norm_num) _
  have h63 : (2 : ℝ) ^ (63 : ℕ) ≤ ((addPipeline a b).zu'.toNat : ℝ) := by
    exact_mod_cast addPipeline_zu'_ge a b hzu
  have h64 : ((addPipeline a b).zu'.toNat : ℝ) < (2 : ℝ) ^ (64 : ℕ) := by
    exact_mod_cast (addPipeline a b).zu'.toNat_lt_size
  rw [← hren] at hlo hhi
  have hup : (2 : ℝ) ^ (((63 : ℕ) : ℤ) + (addPipeline a b).ex''.toInt) < (2 : ℝ) ^ (1024 : ℤ) := by
    rw [← two_pow_mul_zpow]
    have hmul : (2 : ℝ) ^ (63 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt
        ≤ ((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt :=
      mul_le_mul_of_nonneg_right h63 hq.le
    linarith
  have hdown : (2 : ℝ) ^ (-(1022 : ℤ))
      < (2 : ℝ) ^ (((64 : ℕ) : ℤ) + (addPipeline a b).ex''.toInt) := by
    rw [← two_pow_mul_zpow]
    have hmn : FPR.minNormalReal = (2 : ℝ) ^ (-(1022 : ℤ)) := rfl
    rw [hmn] at hlo
    have hmul : ((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt
        < (2 : ℝ) ^ (64 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt :=
      mul_lt_mul_of_pos_right h64 hq
    linarith
  have hup' := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hup
  have hdown' := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hdown
  have hE := addPipeline_ex'''_eq_ex''_add a b
  omega

/-! ## (X) Ruling out overflow at the top exponent -/

private theorem addPipeline_abs_pre_round (a b : FPR) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)|
      = ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  rw [abs_mul, addPipeline_abs_sigma, one_mul, abs_of_nonneg (by positivity)]

/-- Abstract shape of the "no overflow" step: a value within relative `2 / 3 * E` of a quantity
bounded by `P - 2 * Q`, with `E` times that quantity below `Q`, stays below `P`. -/
private theorem lt_top_aux {S B P Q E : ℝ} (hQ : 0 < Q) (hmax : S ≤ P - 2 * Q)
    (hgap : B - S ≤ 2 / 3 * E * S) (hES : E * S ≤ Q) : B < P := by linarith

private theorem two_zpow_pos (m : ℤ) : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) _

private theorem addPipeline_pre_round_lt (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hmin : FPR.minNormalReal ≤ |toReal a + toReal b|)
    (hmax : |toReal a + toReal b| ≤ FPR.maxFiniteReal) :
    ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt
      < (2 : ℝ) ^ (1024 : ℤ) := by
  have h1 := (addPipeline_pre_round a b ha hb hmin).1
  have hgap := abs_sub_abs_le_abs_sub
    ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
      (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt))
    (toReal a + toReal b)
  rw [addPipeline_abs_pre_round] at hgap
  have h971 : (2 : ℝ) ^ (971 : ℤ) = 2 * (2 : ℝ) ^ (970 : ℤ) := by
    rw [show (971 : ℤ) = 970 + 1 from by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hprod : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (1024 : ℤ) = (2 : ℝ) ^ (970 : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [maxFiniteReal_eq, h971] at hmax
  have hSle : |toReal a + toReal b| ≤ (2 : ℝ) ^ (1024 : ℤ) :=
    hmax.trans (sub_le_self _ (by positivity))
  have hES : (2 : ℝ) ^ (-(54 : ℤ)) * |toReal a + toReal b| ≤ (2 : ℝ) ^ (970 : ℤ) := by
    have h := mul_le_mul_of_nonneg_left hSle (two_zpow_pos (-(54 : ℤ))).le
    rwa [hprod] at h
  exact lt_top_aux (two_zpow_pos (970 : ℤ)) hmax (hgap.trans h1) hES

/-- Abstract shape of the "no carry at the top exponent" contradiction. -/
private theorem no_carry_aux {S B W P U : ℝ} (hP : 0 < P) (hWge : (U - 2) * P ≤ W)
    (hfold : W - B ≤ P) (halign : B - S ≤ P / 2) (hmax : S ≤ U * P - 4 * P) : False := by
  linarith

/-- At the very top of the exponent range the final rounding cannot carry out of the mantissa
field: a carry there would force the exact sum past the largest finite magnitude, which the
result-range hypothesis of `add_error` excludes. -/
private theorem addPipeline_no_carry (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt)
    (hmax : |toReal a + toReal b| ≤ FPR.maxFiniteReal)
    (hex : (addPipeline a b).ex'''.toInt = 969) :
    roundQuarterTiesEven (addPipeline a b).zu''.toNat < 2 ^ 53 := by
  by_contra hc
  push Not at hc
  have hmem := addPipeline_zu''_mem a b hzu
  have hhi := (roundQuarterTiesEven_mem_of_normalized (addPipeline a b).zu''.toNat
    hmem.1 hmem.2).2
  have heq : roundQuarterTiesEven (addPipeline a b).zu''.toNat = 2 ^ 53 := by omega
  have h4 := four_mul_roundQuarterTiesEven_le (addPipeline a b).zu''.toNat
  rw [heq] at h4
  have hzuge : (2 : ℝ) ^ (55 : ℕ) - 2 ≤ ((addPipeline a b).zu''.toNat : ℝ) := by
    have hn : (2 : ℕ) ^ 55 ≤ (addPipeline a b).zu''.toNat + 2 := by omega
    have hR : (((2 : ℕ) ^ 55 : ℕ) : ℝ) ≤ (((addPipeline a b).zu''.toNat + 2 : ℕ) : ℝ) := by
      exact_mod_cast hn
    push_cast at hR
    linarith
  have hex2 : (addPipeline a b).ex''.toInt = 960 := by
    have := addPipeline_ex'''_eq_ex''_add a b
    omega
  have hq := two_zpow_pos (969 : ℤ)
  have e1 : (2 : ℝ) ^ (9 : ℕ) * (2 : ℝ) ^ (960 : ℤ) = (2 : ℝ) ^ (969 : ℤ) := by
    rw [two_pow_mul_zpow]; norm_num
  have eA : (2 : ℝ) ^ (55 : ℕ) * (2 : ℝ) ^ (969 : ℤ) = (2 : ℝ) ^ (1024 : ℤ) := by
    rw [two_pow_mul_zpow]; norm_num
  have eB : (4 : ℝ) * (2 : ℝ) ^ (969 : ℤ) = (2 : ℝ) ^ (971 : ℤ) := by
    rw [show (971 : ℤ) = 2 + 969 from by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have e3 : FPR.maxFiniteReal
      = (2 : ℝ) ^ (55 : ℕ) * (2 : ℝ) ^ (969 : ℤ) - 4 * (2 : ℝ) ^ (969 : ℤ) := by
    rw [maxFiniteReal_eq, eA, eB]
  have hexle : (2 : ℝ) ^ (addPipeline a b).ex'.toInt ≤ (2 : ℝ) ^ (969 : ℤ) / 2 := by
    have h968 : (2 : ℝ) ^ (addPipeline a b).ex'.toInt ≤ (2 : ℝ) ^ (968 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (addPipeline_ex'_le a b ha hb)
    have hsplit : (2 : ℝ) ^ (969 : ℤ) = 2 * (2 : ℝ) ^ (968 : ℤ) := by
      rw [show (969 : ℤ) = 968 + 1 from by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [hsplit]
    linarith
  have hfold := addPipeline_fold_abs_error a b hzu hb31
  rw [hex, hex2, e1] at hfold
  have halign := addPipeline_pre_round_abs a b ha hb
  have hgap := abs_sub_abs_le_abs_sub
    ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
      (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt))
    (toReal a + toReal b)
  rw [addPipeline_abs_pre_round] at hgap
  rw [e3] at hmax
  exact no_carry_aux hq (mul_le_mul_of_nonneg_right hzuge hq.le) (abs_le.mp hfold).2
    ((hgap.trans halign).trans hexle) hmax

/-! ## (XI) The error budget -/

private theorem add_error_combine {R W V S δ : ℝ} (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16)
    (h1 : |R - W| ≤ 2 * δ * |W|) (h2 : |W - V| ≤ δ * |V|)
    (h3 : |V - S| ≤ 2 / 3 * δ * |S|) : |R - S| ≤ 4 * δ * |S| := by
  have hSnn : (0 : ℝ) ≤ |S| := abs_nonneg _
  have hVnn : (0 : ℝ) ≤ |V| := abs_nonneg _
  have hV : |V| ≤ |S| + 2 / 3 * δ * |S| := by
    have := abs_sub_abs_le_abs_sub V S
    linarith
  have hW : |W| ≤ |V| + δ * |V| := by
    have := abs_sub_abs_le_abs_sub W V
    linarith
  have htri : |R - S| ≤ |R - W| + |W - V| + |V - S| := by
    calc |R - S| = |(R - W) + (W - V) + (V - S)| := by congr 1; ring
      _ ≤ |R - W| + |W - V| + |V - S| := abs_add_three _ _ _
  have hVS : |V| ≤ (1 + 2 / 3 * δ) * |S| := by linarith
  have hWS : |W| ≤ (1 + δ) * ((1 + 2 / 3 * δ) * |S|) := by
    have h1' : (1 + δ) * |V| ≤ (1 + δ) * ((1 + 2 / 3 * δ) * |S|) :=
      mul_le_mul_of_nonneg_left hVS (by linarith)
    linarith
  have hrem : (0 : ℝ) ≤ 1 / 3 - 4 * δ - 4 / 3 * δ ^ 2 := by nlinarith
  have hkey := mul_nonneg (mul_nonneg hδ.le hSnn) hrem
  have hb1 : 2 * δ * |W| ≤ 2 * δ * ((1 + δ) * ((1 + 2 / 3 * δ) * |S|)) :=
    mul_le_mul_of_nonneg_left hWS (by linarith)
  have hb2 : δ * |V| ≤ δ * ((1 + 2 / 3 * δ) * |S|) :=
    mul_le_mul_of_nonneg_left hVS hδ.le
  nlinarith [hkey, hb1, hb2, htri, h1, h2, h3]

/-! ## (XII) The exact-cancellation branch -/

/-- When the exact sum is `0` the two operands have equal magnitudes and opposite signs, so their
exponent gap is `0`, the alignment shift is the identity, and the combined significand cancels
exactly. -/
private theorem addPipeline_zu_eq_zero_of_sum_eq_zero (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b) (h : toReal a + toReal b = 0) : (addPipeline a b).zu = 0 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have hS := addPipeline_S_eq a b ha hb
  have hxm := addPipeline_xu_mem a b ha hb
  have hym := addPipeline_yuRaw_mem a b ha hb
  have hX55 : (2 : ℝ) ^ (55 : ℕ) ≤ ((addPipeline a b).xu.toNat : ℝ) := by exact_mod_cast hxm.1
  have hYpnn : (0 : ℝ) ≤ ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat := by
    positivity
  have hσne : (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) ≠ 0 := by
    split_ifs <;> norm_num
  have hz : ((addPipeline a b).xu.toNat : ℝ)
      + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
        (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) = 0 := by
    have hzero := hS.symm.trans h
    rcases mul_eq_zero.mp hzero with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hσne
      · exact h''
    · exact absurd h' (ne_of_gt hp)
  by_cases hs : (addPipeline a b).sx = (addPipeline a b).sy
  · rw [ite_eq_left hs] at hz
    exfalso
    have : (0 : ℝ) < (2 : ℝ) ^ (55 : ℕ) := by positivity
    linarith
  · rw [ite_eq_right hs] at hz
    have hpn : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).n.toNat := by positivity
    have hdiv : ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat
        = ((addPipeline a b).xu.toNat : ℝ) := by linarith
    have heq := (div_eq_iff hpn.ne').mp hdiv
    have hy56 : ((addPipeline a b).yu_.toNat : ℝ) < (2 : ℝ) ^ (56 : ℕ) := by exact_mod_cast hym.2
    have h56 : (2 : ℝ) ^ (56 : ℕ) = 2 * (2 : ℝ) ^ (55 : ℕ) := by norm_num
    have h2n : (2 : ℝ) ^ (addPipeline a b).n.toNat < 2 := by nlinarith
    have hn0 : (addPipeline a b).n.toNat = 0 := by
      by_contra hne
      have hge : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ (addPipeline a b).n.toNat :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_one] at hge
      linarith
    have hexact := addPipeline_align_exact a b (by omega)
    have hyx : ((addPipeline a b).yu.toNat : ℝ) = ((addPipeline a b).xu.toNat : ℝ) := by
      rw [hexact, hdiv]
    have hnat : (addPipeline a b).yu.toNat = (addPipeline a b).xu.toNat := by exact_mod_cast hyx
    have huint : (addPipeline a b).yu = (addPipeline a b).xu := UInt64.toNat_inj.mp hnat
    rw [addPipeline_zu_eq_sub_of_sx_ne_sy a b hs, huint]
    simp

/-! ## Per-operation error bounds -/

/-- Relative error bound for `FPR.add`, on normal (non-subnormal, finite) operands whose exact
sum stays in the correctly-rounded binary64 magnitude window (`FPR.InNormalMagnitudeRange`):
neither overflowing past `FPR.maxFiniteReal` nor underflowing into the open subnormal band below
`FPR.minNormalReal`. Both restrictions are load-bearing: two maximal-magnitude normal operands
overflow the exponent field on summation, and two normal operands whose exact difference is
subnormal (e.g. `2^-1022` and its next-representable neighbor) are mis-rounded by the alignment
step, in both cases producing a result unrelated to the true sum. -/
private theorem add_error_of_isNormal (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a + toReal b)) :
    |toReal (FPR.add a b) - (toReal a + toReal b)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a + toReal b| := by
  rcases hr with h0 | ⟨hmin, hmax⟩
  · rw [h0, add_toReal_eq_zero_of_zu_eq_zero' a b
      (addPipeline_zu_eq_zero_of_sum_eq_zero a b ha hb h0)]
    simp
  · obtain ⟨herr, hBmin⟩ := addPipeline_pre_round a b ha hb hmin
    have hmn : FPR.minNormalReal = (2 : ℝ) ^ (-(1022 : ℤ)) := rfl
    have hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt := by
      have := addPipeline_ex'_ge' a b ha hb
      omega
    have hzu : (addPipeline a b).zu ≠ 0 := by
      intro hc
      rw [hc, hmn] at hBmin
      have hz : (((0 : UInt64).toNat : ℝ)) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt = 0 := by
        norm_num
      rw [hz] at hBmin
      exact absurd hBmin (not_le.mpr (two_zpow_pos (-(1022 : ℤ))))
    have hlt := addPipeline_pre_round_lt a b ha hb hmin hmax
    obtain ⟨he1, he2⟩ := addPipeline_ex'''_window a b hzu hb31 hBmin hlt
    have hmem := addPipeline_zu''_mem a b hzu
    have hs : ((addPipeline a b).sx.toUInt64).toNat ≤ 1 := by
      rcases addPipeline_sx_eq_zero_or_one a b with hc | hc <;> rw [hc] <;> decide
    have hδ : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := two_zpow_pos _
    have hδ16 : (2 : ℝ) ^ (-(54 : ℤ)) ≤ 1 / 16 := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-(54 : ℤ)) ≤ -(4 : ℤ))
      rw [show (2 : ℝ) ^ (-(4 : ℤ)) = 1 / 16 from by norm_num] at h
      exact h
    have h52 : (2 : ℝ) ^ (-(52 : ℤ)) = 4 * (2 : ℝ) ^ (-(54 : ℤ)) := by
      rw [show (-(52 : ℤ)) = 2 + -(54 : ℤ) from by norm_num,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have h53 : (2 : ℝ) ^ (-(53 : ℤ)) = 2 * (2 : ℝ) ^ (-(54 : ℤ)) := by
      rw [show (-(53 : ℤ)) = 1 + -(54 : ℤ) from by norm_num,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hbase : toReal (FPR.add a b) =
        toRealBits (make_z ((addPipeline a b).sx.toUInt64) (addPipeline a b).ex'''
          (addPipeline a b).zu'') := by
      unfold toReal
      rw [add_eq_make_z]
    have hasm : |toRealBits (make_z ((addPipeline a b).sx.toUInt64) (addPipeline a b).ex'''
          (addPipeline a b).zu'') -
        (if ((addPipeline a b).sx.toUInt64).toNat = 1 then (-1 : ℝ) else 1) *
          ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt| ≤
        (2 : ℝ) ^ (-(53 : ℤ)) *
          |(if ((addPipeline a b).sx.toUInt64).toNat = 1 then (-1 : ℝ) else 1) *
            ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt| := by
      by_cases hcw : (addPipeline a b).ex'''.toInt ≤ 968
      · exact abs_toRealBits_make_z_sub_le _ _ _ hs he1 hcw hmem.1 hmem.2
      · exact abs_toRealBits_make_z_sub_le_of_no_carry _ _ _ hs he1 he2 hmem.1 hmem.2
          (addPipeline_no_carry a b ha hb hzu hb31 hmax (by omega))
    rw [UInt32.toNat_toUInt64, h53, ← hbase] at hasm
    have hfold : |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)|
      ≤ (2 : ℝ) ^ (-(54 : ℤ)) *
        |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)| := by
      rw [show (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
            ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
          - (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
            (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        = (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
            (((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
              - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        from by ring,
        abs_mul, addPipeline_abs_sigma, one_mul, addPipeline_abs_pre_round]
      exact addPipeline_fold_error a b hzu hb31
    rw [h52]
    exact add_error_combine hδ hδ16 hasm hfold herr

/-- Closure for `FPR.add` on the domain `add_error` covers: the rounded sum is normal, except
under exact cancellation, where it is `±0`.

Cancellation is why this cannot be stated with `FPR.IsNormal` on the right. At `1 + (-1)` both
operands are normal and the exact sum `0` satisfies `FPR.InNormalMagnitudeRange` through its
`r = 0` disjunct, but `FPR.add` returns `+0`, whose exponent field is `0`. The rounding carry is
the other boundary: it raises the packed exponent by two rather than one, and is ruled out at the
top of the window by `addPipeline_no_carry`, so the result never reaches the non-finite marker. -/
private theorem add_isNormalOrZero_of_isNormal (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a + toReal b)) :
    FPR.IsNormalOrZero (FPR.add a b) := by
  have hs : ((addPipeline a b).sx.toUInt64).toNat ≤ 1 := by
    rcases addPipeline_sx_eq_zero_or_one a b with hc | hc <;> rw [hc] <;> decide
  rcases hr with h0 | ⟨hmin, hmax⟩
  · right
    unfold FPR.IsZero FPR.Bits.IsZero
    rw [add_eq_make_z, addPipeline_zu''_eq_zero_of_zu_eq_zero a b
        (addPipeline_zu_eq_zero_of_sum_eq_zero a b ha hb h0),
      FPR.decode_make_z_of_zero _ _ hs]
    exact ⟨rfl, rfl⟩
  · left
    have hmn : FPR.minNormalReal = (2 : ℝ) ^ (-(1022 : ℤ)) := rfl
    obtain ⟨herr, hBmin⟩ := addPipeline_pre_round a b ha hb hmin
    have hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt := by
      have := addPipeline_ex'_ge' a b ha hb
      omega
    have hzu : (addPipeline a b).zu ≠ 0 := by
      intro hc
      rw [hc, hmn] at hBmin
      have hz : (((0 : UInt64).toNat : ℝ)) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt = 0 := by
        norm_num
      rw [hz] at hBmin
      exact absurd hBmin (not_le.mpr (two_zpow_pos (-(1022 : ℤ))))
    have hlt := addPipeline_pre_round_lt a b ha hb hmin hmax
    obtain ⟨he1, he2⟩ := addPipeline_ex'''_window a b hzu hb31 hBmin hlt
    have hmem := addPipeline_zu''_mem a b hzu
    have hround := roundQuarterTiesEven_mem_of_normalized _ hmem.1 hmem.2
    unfold FPR.IsNormal FPR.Bits.IsNormal
    rw [add_eq_make_z]
    rcases lt_or_ge (roundQuarterTiesEven (addPipeline a b).zu''.toNat) (2 ^ 53) with hnc | hcar
    · rw [FPR.decode_make_z_of_no_carry _ _ _ hs he1 he2 hmem.1 hmem.2 hnc]
      simp only
      omega
    · have hceq : roundQuarterTiesEven (addPipeline a b).zu''.toNat = 2 ^ 53 := by omega
      have h968 : (addPipeline a b).ex'''.toInt ≤ 968 := by
        by_contra hcon
        exact absurd (addPipeline_no_carry a b ha hb hzu hb31 hmax (by omega)) (by omega)
      rw [FPR.decode_make_z_of_carry _ _ _ hs he1 he2 hmem.1 hmem.2 hceq]
      simp only
      omega

/-- Negation preserves normality: flipping the sign bit leaves the exponent field alone. -/
theorem FPR.isNormal_neg {b : FPR} (hb : FPR.IsNormal b) : FPR.IsNormal (FPR.neg b) := by
  unfold FPR.IsNormal FPR.Bits.IsNormal at hb ⊢
  rw [decode_neg_exponent]
  exact hb

/-- Negation preserves the closed operand domain: it touches neither the exponent field nor the
significand, so it carries both disjuncts of `FPR.IsNormalOrZero`. -/
theorem FPR.isNormalOrZero_neg {b : FPR} (hb : FPR.IsNormalOrZero b) :
    FPR.IsNormalOrZero (FPR.neg b) := by
  rcases hb with h | h
  · exact Or.inl (FPR.isNormal_neg h)
  · right
    unfold FPR.IsZero FPR.Bits.IsZero at h ⊢
    rw [decode_neg_exponent, decode_neg_mantissa]
    exact h

/-- The cancellation case is real and is now covered: `1 + (-1)` lands in the zero disjunct.
This is the input that refutes the same statement with `FPR.IsNormal` on the right. -/
example : FPR.IsNormalOrZero (FPR.add FPR.one (FPR.neg FPR.one))
    ∧ ¬ FPR.IsNormal (FPR.add FPR.one (FPR.neg FPR.one)) := by
  refine ⟨add_isNormalOrZero_of_isNormal FPR.one (FPR.neg FPR.one) ?_ ?_ ?_, ?_⟩
  · unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode; decide
  · unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode; decide
  · exact Or.inl (by rw [toReal_neg, toReal_one]; ring)
  · unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode; decide

/-- With the smaller operand's significand empty, the aligned addend `yu` vanishes: the raw
packing `yu_` is `8 *` that significand, the flush mask can only clear it further, and
`stickyShift` sends `0` to `0`. -/
private theorem addPipeline_yu_eq_zero_of_significand (a b : FPR)
    (hy : (FPR.decode (addPipeline a b).y').significand = 0) :
    (addPipeline a b).yu = 0 := by
  have hraw : (addPipeline a b).yu_ = 0 := by
    rw [← UInt64.toNat_inj, addPipeline_yuRaw_toNat, hy]; rfl
  have hyu' : (addPipeline a b).yu' = 0 := by
    rw [addPipeline_yu', hraw, UInt64.zero_and]
  rw [← UInt64.toNat_inj, addPipeline_yu_toNat, hyu']
  rw [show ((0 : UInt64).toNat) = 0 from rfl]
  simp [stickyShift]

/-- With the aligned addend gone, the combined significand is exactly the leading operand's. -/
private theorem addPipeline_zu_eq_xu (a b : FPR)
    (hy : (FPR.decode (addPipeline a b).y').significand = 0) :
    (addPipeline a b).zu = (addPipeline a b).xu := by
  rw [addPipeline_zu, addPipeline_yu_eq_zero_of_significand a b hy]
  simp

/-- The renormalising shift count is exactly `8` when the combined significand is the leading
operand's own packing: `xu = 8 * significand` sits in `[2 ^ 55, 2 ^ 56)`, and the `||| 1` guard
cannot leave that window because `xu` is a multiple of `8`. -/
private theorem addPipeline_c_eq_eight (a b : FPR)
    (hx : FPR.IsNormal (addPipeline a b).x')
    (hy : (FPR.decode (addPipeline a b).y').significand = 0) :
    (addPipeline a b).c.toNat = 8 := by
  obtain ⟨hs1, hs2⟩ := significand_mem_of_isNormal hx.1 (FPR.decode_mantissa_lt _)
  have hxu : (addPipeline a b).xu.toNat = 8 * (FPR.decode (addPipeline a b).x').significand :=
    addPipeline_xu_toNat a b
  have hzu : (addPipeline a b).zu.toNat = (addPipeline a b).xu.toNat := by
    rw [addPipeline_zu_eq_xu a b hy]
  have hor : ((addPipeline a b).zu ||| 1).toNat = (addPipeline a b).zu.toNat ||| 1 :=
    UInt64.toNat_or _ _
  have hval : (addPipeline a b).zu.toNat ||| 1
      = 2 * ((addPipeline a b).zu.toNat / 2) + 1 := or_one_eq _
  rw [addPipeline_c]
  refine lzcnt64_nonzero_unique _ 8 ?_ ?_ <;> rw [hor, hval] <;> omega

/-- The rounded significand handed to `FPR.make_z` is exactly `4 *` the leading operand's
significand: the renormalising shift by `8` leaves the low eleven bits clear, so the nine-bit
sticky fold is an exact division. -/
private theorem addPipeline_zu''_eq (a b : FPR)
    (hx : FPR.IsNormal (addPipeline a b).x')
    (hy : (FPR.decode (addPipeline a b).y').significand = 0) :
    (addPipeline a b).zu''.toNat = 4 * (FPR.decode (addPipeline a b).x').significand := by
  obtain ⟨hs1, hs2⟩ := significand_mem_of_isNormal hx.1 (FPR.decode_mantissa_lt _)
  have hxu : (addPipeline a b).xu.toNat = 8 * (FPR.decode (addPipeline a b).x').significand :=
    addPipeline_xu_toNat a b
  have hzu : (addPipeline a b).zu = (addPipeline a b).xu := addPipeline_zu_eq_xu a b hy
  have hzune : (addPipeline a b).zu ≠ 0 := by
    intro h0
    rw [h0] at hzu
    rw [← hzu] at hxu
    simp only [show ((0 : UInt64).toNat) = 0 from rfl] at hxu
    omega
  have hzu' : (addPipeline a b).zu'.toNat = (addPipeline a b).zu.toNat * 2 ^ 8 := by
    rw [addPipeline_zu', addPipeline_c, fpr_ulsh_lzcnt64_toNat _ hzune, ← addPipeline_c,
      addPipeline_c_eq_eight a b hx hy]
  rw [addPipeline_zu'', toNat_or_fold_shiftRight_nine, stickyShift_eq, hzu', hzu, hxu]
  have hmod : 8 * (FPR.decode (addPipeline a b).x').significand * 2 ^ 8 % 2 ^ (9 + 1) = 0 := by
    omega
  rw [hmod, ite_eq_left rfl]
  omega

/-- The packed exponent handed to `FPR.make_z`, as a plain integer. -/
private theorem addPipeline_ex3_eq (a b : FPR)
    (hx : FPR.IsNormal (addPipeline a b).x')
    (hy : (FPR.decode (addPipeline a b).y').significand = 0) :
    (addPipeline a b).ex'''.toInt
      = ((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1077 := by
  rw [addPipeline_ex'''_toInt, addPipeline_ex'_toInt, addPipeline_c_eq_eight a b hx hy,
    addPipeline_ex_eq_exponent]
  ring

/-- **`FPR.add` is exact when one operand is a zero encoding.** With the trailing operand's
significand empty, nothing is aligned in, nothing is rounded off, and the pipeline reassembles
the leading operand unchanged: `zu` is `xu`, the renormalising count is `8`, and the nine-bit
sticky fold divides exactly. Stated on `x'` so that it covers both argument orders at once —
`addPipeline_swap_cases` identifies `x'` with whichever operand carries the larger magnitude. -/
private theorem add_decode_eq_of_significand_eq_zero (a b : FPR)
    (hx : FPR.IsNormal (addPipeline a b).x')
    (hy : (FPR.decode (addPipeline a b).y').significand = 0) :
    FPR.decode (FPR.add a b) = FPR.decode (addPipeline a b).x' := by
  obtain ⟨hs1, hs2⟩ := significand_mem_of_isNormal hx.1 (FPR.decode_mantissa_lt _)
  have hexp1 : 1 ≤ (FPR.decode (addPipeline a b).x').exponent :=
    Nat.one_le_iff_ne_zero.mpr hx.1
  have hexp2 : (FPR.decode (addPipeline a b).x').exponent ≤ 2046 := by
    have := FPR.decode_exponent_lt (addPipeline a b).x'
    have := hx.2
    omega
  have hzu'' := addPipeline_zu''_eq a b hx hy
  have hex3 := addPipeline_ex3_eq a b hx hy
  have hsign : ((addPipeline a b).sx.toUInt64).toNat
      = if (FPR.decode (addPipeline a b).x').sign then 1 else 0 := by
    rw [UInt32.toNat_toUInt64]
    exact addPipeline_sx_toNat a b
  have hround : roundQuarterTiesEven (addPipeline a b).zu''.toNat
      = (FPR.decode (addPipeline a b).x').significand := by
    rw [hzu'', roundQuarterTiesEven_of_mod_four_eq_zero _ (by omega)]
    omega
  rw [add_eq_make_z,
    FPR.decode_make_z_of_no_carry _ _ _ (by rw [hsign]; split_ifs <;> omega)
      (by rw [hex3]; omega) (by rw [hex3]; omega) (by omega) (by omega)
      (by rw [hround]; omega)]
  have hmant : (FPR.decode (addPipeline a b).x').significand - 2 ^ 52
      = (FPR.decode (addPipeline a b).x').mantissa := by
    unfold FPR.Bits.significand
    rw [ite_eq_right hx.1]
    omega
  have hsg : decide ((addPipeline a b).sx.toUInt64.toNat = 1)
      = (FPR.decode (addPipeline a b).x').sign := by
    rcases Bool.eq_false_or_eq_true (FPR.decode (addPipeline a b).x').sign with hb | hb <;>
      rw [hb] at hsign ⊢ <;> simp [hsign]
  have hexf : (((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1077 + 1076).toNat + 1
      = (FPR.decode (addPipeline a b).x').exponent := by omega
  rw [hex3, hround, hmant, hsg, hexf]

/-- A zero encoding never leads `FPR.add`'s magnitude comparison against a normal operand, so the
pipeline's ordered pair is `(a, b)` when only `b` is zero. -/
private theorem addPipeline_no_swap_of_isZero_right (a b : FPR)
    (ha : FPR.IsNormal a) (hb : FPR.IsZero b) :
    (addPipeline a b).x' = a ∧ (addPipeline a b).y' = b := by
  obtain ⟨hcases, hmag⟩ := addPipeline_swap_cases a b
  rcases hcases with h | h
  · exact h
  · exfalso
    rw [h.1, h.2] at hmag
    have := two_pow_le_magKey_of_isNormal ha
    rw [magKey_eq_zero_of_isZero hb] at hmag
    omega

/-- The mirror of `addPipeline_no_swap_of_isZero_right`: the pipeline swaps, so `x'` is `b`. -/
private theorem addPipeline_swap_of_isZero_left (a b : FPR)
    (ha : FPR.IsZero a) (hb : FPR.IsNormal b) :
    (addPipeline a b).x' = b ∧ (addPipeline a b).y' = a := by
  obtain ⟨hcases, hmag⟩ := addPipeline_swap_cases a b
  rcases hcases with h | h
  · exfalso
    rw [h.1, h.2] at hmag
    have := two_pow_le_magKey_of_isNormal hb
    rw [magKey_eq_zero_of_isZero ha] at hmag
    omega
  · exact h

/-- Adding a zero encoding on the right is exact, at the level of decoded fields. -/
private theorem add_decode_of_isZero_right (a b : FPR)
    (ha : FPR.IsNormal a) (hb : FPR.IsZero b) :
    FPR.decode (FPR.add a b) = FPR.decode a := by
  obtain ⟨hx, hy⟩ := addPipeline_no_swap_of_isZero_right a b ha hb
  have h := add_decode_eq_of_significand_eq_zero a b (by rw [hx]; exact ha)
    (by rw [hy]; exact significand_eq_zero_of_isZero hb)
  rw [h, hx]

/-- Adding a zero encoding on the left is exact, at the level of decoded fields. -/
private theorem add_decode_of_isZero_left (a b : FPR)
    (ha : FPR.IsZero a) (hb : FPR.IsNormal b) :
    FPR.decode (FPR.add a b) = FPR.decode b := by
  obtain ⟨hx, hy⟩ := addPipeline_swap_of_isZero_left a b ha hb
  have h := add_decode_eq_of_significand_eq_zero a b (by rw [hx]; exact hb)
    (by rw [hy]; exact significand_eq_zero_of_isZero ha)
  rw [h, hx]

/-- Both operands zero: the combined significand is empty. -/
private theorem addPipeline_zu_eq_zero_of_isZero (a b : FPR)
    (ha : FPR.IsZero a) (hb : FPR.IsZero b) : (addPipeline a b).zu = 0 := by
  have hy : (FPR.decode (addPipeline a b).y').significand = 0 := by
    rcases (addPipeline_swap_cases a b).1 with h | h
    · rw [h.2]; exact significand_eq_zero_of_isZero hb
    · rw [h.2]; exact significand_eq_zero_of_isZero ha
  have hx : (FPR.decode (addPipeline a b).x').significand = 0 := by
    rcases (addPipeline_swap_cases a b).1 with h | h
    · rw [h.1]; exact significand_eq_zero_of_isZero ha
    · rw [h.1]; exact significand_eq_zero_of_isZero hb
  rw [addPipeline_zu_eq_xu a b hy, ← UInt64.toNat_inj, addPipeline_xu_toNat, hx]
  rfl

/-- Both operands zero: the sum is a zero encoding. -/
private theorem add_isZero_of_isZero (a b : FPR) (ha : FPR.IsZero a) (hb : FPR.IsZero b) :
    FPR.IsZero (FPR.add a b) := by
  have hzu := addPipeline_zu_eq_zero_of_isZero a b ha hb
  unfold FPR.IsZero FPR.Bits.IsZero
  rw [add_eq_make_z, addPipeline_zu''_eq_zero_of_zu_eq_zero a b hzu,
    FPR.decode_make_z_of_zero _ _
      (by rcases addPipeline_sx_eq_zero_or_one a b with hc | hc <;> rw [hc] <;> decide)]
  exact ⟨rfl, rfl⟩

theorem add_error (a b : FPR) (ha : FPR.IsNormalOrZero a) (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a + toReal b)) :
    |toReal (FPR.add a b) - (toReal a + toReal b)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a + toReal b| := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact add_error_of_isNormal a b ha hb hr
    · rw [toReal_eq_of_decode_eq (add_decode_of_isZero_right a b ha hb),
        toReal_eq_zero_of_isZero hb, add_zero, sub_self, abs_zero]
      positivity
  · rcases hb with hb | hb
    · rw [toReal_eq_of_decode_eq (add_decode_of_isZero_left a b ha hb),
        toReal_eq_zero_of_isZero ha, zero_add, sub_self, abs_zero]
      positivity
    · rw [add_toReal_eq_zero_of_zu_eq_zero' a b (addPipeline_zu_eq_zero_of_isZero a b ha hb),
        toReal_eq_zero_of_isZero ha, toReal_eq_zero_of_isZero hb]
      simp

theorem add_isNormalOrZero (a b : FPR) (ha : FPR.IsNormalOrZero a)
    (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a + toReal b)) :
    FPR.IsNormalOrZero (FPR.add a b) := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact add_isNormalOrZero_of_isNormal a b ha hb hr
    · exact Or.inl (by unfold FPR.IsNormal; rw [add_decode_of_isZero_right a b ha hb]; exact ha)
  · rcases hb with hb | hb
    · exact Or.inl (by unfold FPR.IsNormal; rw [add_decode_of_isZero_left a b ha hb]; exact hb)
    · exact Or.inr (add_isZero_of_isZero a b ha hb)

theorem sub_error (a b : FPR) (ha : FPR.IsNormalOrZero a) (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a - toReal b)) :
    |toReal (FPR.sub a b) - (toReal a - toReal b)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a - toReal b| := by
  have hsum : toReal a + toReal (FPR.neg b) = toReal a - toReal b := by
    rw [toReal_neg]; ring
  have h := add_error a (FPR.neg b) ha (FPR.isNormalOrZero_neg hb) (by rw [hsum]; exact hr)
  rw [hsum] at h
  exact h

theorem sub_isNormalOrZero (a b : FPR) (ha : FPR.IsNormalOrZero a) (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a - toReal b)) :
    FPR.IsNormalOrZero (FPR.sub a b) := by
  have hsum : toReal a + toReal (FPR.neg b) = toReal a - toReal b := by
    rw [toReal_neg]; ring
  exact add_isNormalOrZero a (FPR.neg b) ha (FPR.isNormalOrZero_neg hb) (by rw [hsum]; exact hr)

/-- Every operand in the closure domain denotes a value inside the correctly-rounded magnitude
window. This is what keeps `FPR.InNormalMagnitudeRange` from being vacuously restrictive: a value
the format can hold is a result the format can round to. Both ends are exactly attained — the
lower by `2 ^ (-1022)` and the upper by `FPR.maxFiniteReal` itself. -/
theorem FPR.inNormalMagnitudeRange_toReal_of_isNormalOrZero {a : FPR}
    (h : FPR.IsNormalOrZero a) : FPR.InNormalMagnitudeRange (toReal a) := by
  rcases h with h | h
  · right
    obtain ⟨hs1, hs2⟩ := significand_mem_of_isNormal h.1 (FPR.decode_mantissa_lt a)
    have he : 1 ≤ (FPR.decode a).exponent := Nat.one_le_iff_ne_zero.mpr h.1
    have he2 : (FPR.decode a).exponent ≤ 2046 := by
      have := FPR.decode_exponent_lt a; have := h.2; omega
    have habs : |toReal a| = ((FPR.decode a).significand : ℝ)
        * (2 : ℝ) ^ (((FPR.decode a).exponent : ℤ) - 1075) :=
      abs_toReal_eq_significand_mul_two_zpow h.1 h.2
    have hlo : (2 : ℝ) ^ (-(1074 : ℤ)) ≤ (2 : ℝ) ^ (((FPR.decode a).exponent : ℤ) - 1075) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hhi : (2 : ℝ) ^ (((FPR.decode a).exponent : ℤ) - 1075) ≤ (2 : ℝ) ^ (971 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hsl : (2 : ℝ) ^ (52 : ℕ) ≤ ((FPR.decode a).significand : ℝ) := by exact_mod_cast hs1
    have hsh : ((FPR.decode a).significand : ℝ) ≤ (2 : ℝ) ^ (53 : ℕ) - 1 := by
      have : (FPR.decode a).significand ≤ 2 ^ 53 - 1 := by omega
      have := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at this
      linarith
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (((FPR.decode a).exponent : ℤ) - 1075) :=
      zpow_pos (by norm_num) _
    have hmin : FPR.minNormalReal = (2 : ℝ) ^ (52 : ℕ) * (2 : ℝ) ^ (-(1074 : ℤ)) := by
      unfold FPR.minNormalReal
      rw [← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have h1024 : (2 : ℝ) * (2 : ℝ) ^ (1023 : ℤ) = (2 : ℝ) ^ (1024 : ℤ) := by
      rw [show (1024 : ℤ) = 1 + 1023 from by norm_num,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hmax : FPR.maxFiniteReal = ((2 : ℝ) ^ (53 : ℕ) - 1) * (2 : ℝ) ^ (971 : ℤ) := by
      unfold FPR.maxFiniteReal
      rw [← zpow_natCast (2 : ℝ) 53, sub_mul, sub_mul,
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h1024]
      norm_num
    rw [habs, hmin, hmax]
    constructor
    · exact mul_le_mul hsl hlo (by positivity) (by positivity)
    · exact mul_le_mul hsh hhi (le_of_lt hpos) (by norm_num)
  · exact Or.inl (toReal_eq_zero_of_isZero h)

end

end Falcon.Concrete.FPRBridge
