/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr

/-!
# A second-moment bound for counted Bernoulli trials

Write n for the number of trials so far, v for their successes, and p for their common success rate.
The centered count v/p - n has mean-zero increments with variance (1-p)/p.
A quadratic function of the centered count therefore has a fixed expected cost per fresh trial.
-/

public section

namespace OracleComp.BernoulliMoment

/-- Linear credit for the trial count plus a reserve for deviations from its mean. -/
noncomputable def reserve (p α β v n : ℝ) : ℝ := α * n + β * (v / p - n) ^ 2

/-- One Bernoulli trial consumes the same expected credit at every previous count. -/
theorem step {p : ℝ} (hp : p ≠ 0) (α β v n : ℝ) :
    p * reserve p α β (v + 1) (n + 1) + (1 - p) * reserve p α β v (n + 1) =
      reserve p α β v n + (α + β * ((1 - p) / p)) := by
  unfold reserve
  field_simp
  ring

/-- The reserve starts at zero, even if no trials occur. -/
@[simp] theorem initial (p α β : ℝ) : reserve p α β 0 0 = 0 := by
  simp [reserve]

/-- Positive coefficients give a nonnegative reserve on every reachable count. -/
theorem nonneg {p α β v n : ℝ} (ha : 0 ≤ α) (hb : 0 ≤ β) (hn : 0 ≤ n) :
    0 ≤ reserve p α β v n :=
  add_nonneg (mul_nonneg ha hn) (mul_nonneg hb (sq_nonneg _))

/-- A bounded run can pay for the product of its success count and its occupied count.
The scale and its reciprocal trade linear credit against the cost of fluctuations. -/
theorem covers {p v c n q scale invScale : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hv : 0 ≤ v) (hn : 0 ≤ n) (hc : c ≤ n) (hq : n ≤ q)
    (hs : 0 ≤ scale) (hi : 0 ≤ invScale) (recip : invScale * scale = 1) :
    (v / p) * c + (1 - p) * (v / p) ^ 2 ≤
      reserve p ((2 - p + 3 * invScale / 2) * q) (1 - p + 3 * scale / 2) v n := by
  let x := v / p
  let d := x - n
  have hx : 0 ≤ x := div_nonneg hv hp.le
  have d_id : x = n + d := by dsimp [d]; ring
  have young : 2 * n * d ≤ invScale * n ^ 2 + scale * d ^ 2 := by
    have pos := mul_nonneg hi (sq_nonneg (n - scale * d))
    nlinarith [show invScale * (n - scale * d) ^ 2 =
        invScale * n ^ 2 - 2 * n * d + scale * d ^ 2 by
      linear_combination (-2 * n * d + scale * d ^ 2) * recip]
  have cross : (3 - 2 * p) * (n * d) ≤ 3 / 2 * (invScale * n ^ 2 + scale * d ^ 2) := by
    rcases le_total 0 (n * d) with pos | neg
    · nlinarith [mul_nonneg hp.le pos]
    · have left := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 3 - 2 * p) neg
      have right := add_nonneg (mul_nonneg hi (sq_nonneg n)) (mul_nonneg hs (sq_nonneg d))
      linarith
  have coeff : 0 ≤ 2 - p + 3 * invScale / 2 := by linarith
  have budget := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hn) coeff
  change x * c + (1 - p) * x ^ 2 ≤
    ((2 - p + 3 * invScale / 2) * q) * n + (1 - p + 3 * scale / 2) * d ^ 2
  calc
    _ ≤ x * n + (1 - p) * x ^ 2 := by gcongr
    _ = (2 - p) * n ^ 2 + (3 - 2 * p) * (n * d) + (1 - p) * d ^ 2 := by rw [d_id]; ring
    _ ≤ _ := by linarith

end OracleComp.BernoulliMoment
