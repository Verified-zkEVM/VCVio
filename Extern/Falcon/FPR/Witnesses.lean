/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPR.Add
import all Extern.Falcon.FPR.Mul
import all Extern.Falcon.FPR.Div
import all Extern.Falcon.FPR.Sqrt
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPR.Add
public import Extern.Falcon.FPR.Mul
public import Extern.Falcon.FPR.Div
public import Extern.Falcon.FPR.Sqrt

/-!
# Non-vacuity witnesses for the FPR error bounds

Concrete operands showing that the hypotheses of `add_error`, `sub_error`, `mul_error`,
`div_error` and `sqrt_error` admit ordinary values, including exact zeros.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## Non-vacuity witnesses for the per-operation error bounds

Concrete instances showing the domain hypotheses of `add_error`, `mul_error`, `div_error` and
`sqrt_error` are jointly satisfiable by ordinary values, not merely by a degenerate operand such
as zero. The last two witnesses go the other way, and show that the widening is not cosmetic:
`FPR.zero` satisfies `FPR.IsNormalOrZero` and not `FPR.IsNormal`, so it is admitted by the
statements above and by no narrower reading of them. -/

/-- `toReal` is nonnegative whenever the sign bit is unset, uniformly across the
subnormal/normal/non-finite case split of `FPR.Bits.toReal`. -/
theorem FPR.Bits.toReal_nonneg_of_sign_false {b : FPR.Bits} (h : b.sign = false) :
    0 ≤ b.toReal := by
  unfold FPR.Bits.toReal
  simp only [h, Bool.false_eq_true, ite_false]
  split_ifs <;> positivity

private theorem decode_two : FPR.decode FPR.two = ⟨false, 1024, 0⟩ := by
  unfold FPR.decode FPR.two; decide

/-- `toReal` of the `FPR` constant `2`. -/
theorem toReal_two : toReal FPR.two = 2 := by
  unfold toReal toRealBits
  rw [decode_two]
  simp [FPR.Bits.toReal]

/-- The bit pattern of the binary64 value `1.5`. -/
private def onePointFive : FPR := (0x3FF8000000000000 : UInt64)

private theorem decode_onePointFive :
    FPR.decode onePointFive = ⟨false, 1023, 2 ^ 51⟩ := by
  unfold FPR.decode onePointFive; decide

private theorem toReal_onePointFive : toReal onePointFive = 1.5 := by
  unfold toReal toRealBits
  rw [decode_onePointFive]
  norm_num [FPR.Bits.toReal]

/-- The bit pattern of the binary64 value `2.25`. -/
private def twoPointTwoFive : FPR := (0x4002000000000000 : UInt64)

private theorem decode_twoPointTwoFive :
    FPR.decode twoPointTwoFive = ⟨false, 1024, 2 ^ 49⟩ := by
  unfold FPR.decode twoPointTwoFive; decide

private theorem toReal_twoPointTwoFive : toReal twoPointTwoFive = 2.25 := by
  unfold toReal toRealBits
  rw [decode_twoPointTwoFive]
  norm_num [FPR.Bits.toReal]

private theorem FPR.minNormalReal_le_two_pow {k : ℤ} (hk : -1022 ≤ k) :
    FPR.minNormalReal ≤ (2 : ℝ) ^ k :=
  zpow_le_zpow_right₀ (by norm_num) hk

private theorem FPR.two_pow_le_maxFiniteReal {k : ℤ} (hk : k ≤ 1023) :
    (2 : ℝ) ^ k ≤ FPR.maxFiniteReal := by
  unfold FPR.maxFiniteReal
  have h1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (1023 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hk
  have h2 : (2 : ℝ) ^ (-(52 : ℤ)) ≤ (1 : ℝ) := by
    calc (2 : ℝ) ^ (-(52 : ℤ)) ≤ (2 : ℝ) ^ (0 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 := by norm_num
  have h3 : (1 : ℝ) ≤ 2 - (2 : ℝ) ^ (-(52 : ℤ)) := by linarith
  calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (1023 : ℤ) := h1
    _ = 1 * (2 : ℝ) ^ (1023 : ℤ) := (one_mul _).symm
    _ ≤ (2 - (2 : ℝ) ^ (-(52 : ℤ))) * (2 : ℝ) ^ (1023 : ℤ) :=
        mul_le_mul_of_nonneg_right h3 (le_of_lt (zpow_pos (by norm_num) _))

/-- Any positive real bracketed between two powers of two with exponents inside `[-1022, 1023]`
lands in `FPR.InNormalMagnitudeRange`: the reusable step behind the concrete witnesses below. -/
private theorem FPR.in_normal_range_of_pos_le {r : ℝ} {k1 k2 : ℤ}
    (hk1 : -1022 ≤ k1) (hk2 : k2 ≤ 1023)
    (hr0 : (2 : ℝ) ^ k1 ≤ r) (hr1 : r ≤ (2 : ℝ) ^ k2) :
    FPR.InNormalMagnitudeRange r := by
  right
  have hpos : 0 < r := lt_of_lt_of_le (zpow_pos (by norm_num) _) hr0
  rw [abs_of_pos hpos]
  exact ⟨(FPR.minNormalReal_le_two_pow hk1).trans hr0,
    hr1.trans (FPR.two_pow_le_maxFiniteReal hk2)⟩

private theorem isNormal_one : FPR.IsNormal FPR.one := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.one; decide

private theorem isNormal_two : FPR.IsNormal FPR.two := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.two; decide

private theorem isNormal_onePointFive : FPR.IsNormal onePointFive := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode onePointFive; decide

private theorem isNormal_twoPointTwoFive : FPR.IsNormal twoPointTwoFive := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode twoPointTwoFive; decide

private theorem isNormal_q : FPR.IsNormal FPR.q := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.q; decide

private theorem decode_q_sign_false : (FPR.decode FPR.q).sign = false := by
  unfold FPR.decode FPR.q; decide

/-- `add_error` is not vacuous: `1.0 + 1.0` is an ordinary witness satisfying every hypothesis. -/
example : FPR.IsNormalOrZero FPR.one ∧ FPR.IsNormalOrZero FPR.one ∧
    FPR.InNormalMagnitudeRange (toReal FPR.one + toReal FPR.one) := by
  refine ⟨Or.inl isNormal_one, Or.inl isNormal_one, ?_⟩
  rw [toReal_one]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `add_error` is not vacuous: `1.5 + 2.25` is a second, non-round-number witness. -/
example : FPR.IsNormalOrZero onePointFive ∧ FPR.IsNormalOrZero twoPointTwoFive ∧
    FPR.InNormalMagnitudeRange (toReal onePointFive + toReal twoPointTwoFive) := by
  refine ⟨Or.inl isNormal_onePointFive, Or.inl isNormal_twoPointTwoFive, ?_⟩
  rw [toReal_onePointFive, toReal_twoPointTwoFive]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `mul_error` is not vacuous: `2.0 * 2.0` is an ordinary witness. -/
example : FPR.IsNormalOrZero FPR.two ∧ FPR.IsNormalOrZero FPR.two ∧
    FPR.InNormalMagnitudeRange (toReal FPR.two * toReal FPR.two) := by
  refine ⟨Or.inl isNormal_two, Or.inl isNormal_two, ?_⟩
  rw [toReal_two]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `div_error` is not vacuous: `2.0 / 1.0` is an ordinary witness. -/
example : toReal FPR.one ≠ 0 ∧ FPR.IsNormalOrZero FPR.two ∧ FPR.IsNormalOrZero FPR.one ∧
    FPR.InNormalMagnitudeRange (toReal FPR.two / toReal FPR.one) := by
  refine ⟨by rw [toReal_one]; norm_num, Or.inl isNormal_two, Or.inl isNormal_one, ?_⟩
  rw [toReal_two, toReal_one, div_one]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `sqrt_error` is not vacuous: `FPR.q`, the Falcon modulus `12289` used throughout the concrete
NTT/FFT and rounding kernels (`FPR.q` in `LatticeCrypto/Falcon/Concrete/FPR.lean`), is a normal,
nonnegative operand — and, unlike `add_error` / `mul_error` / `div_error`, needs no further
magnitude side condition; see `sqrt_error`'s docstring for why. -/
example : FPR.IsNormalOrZero FPR.q ∧ 0 ≤ toReal FPR.q := by
  refine ⟨Or.inl isNormal_q, ?_⟩
  unfold toReal toRealBits
  exact FPR.Bits.toReal_nonneg_of_sign_false decode_q_sign_false

/-- The widening is not cosmetic: `FPR.zero` is admitted by every statement above and by none of
their `FPR.IsNormal` readings. -/
example : FPR.IsNormalOrZero FPR.zero ∧ ¬ FPR.IsNormal FPR.zero := by
  refine ⟨Or.inr ?_, ?_⟩
  · unfold FPR.IsZero FPR.Bits.IsZero FPR.decode FPR.zero; decide
  · unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.zero; decide

/-- And it is reached: `1.0 + 0` meets `add_error`'s hypotheses with a zero operand, which the
`FPR.IsNormal` reading rejects. -/
example : FPR.IsNormalOrZero FPR.one ∧ FPR.IsNormalOrZero FPR.zero ∧
    FPR.InNormalMagnitudeRange (toReal FPR.one + toReal FPR.zero) := by
  refine ⟨Or.inl isNormal_one, Or.inr ?_, ?_⟩
  · unfold FPR.IsZero FPR.Bits.IsZero FPR.decode FPR.zero; decide
  · rw [toReal_one, toReal_zero, add_zero]
    exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end

end Falcon.Concrete.FPRBridge
