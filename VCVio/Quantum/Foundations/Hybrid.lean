/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import QuantumFoundations.MatrixMap.Norm

/-!
# Cutoff estimates for square-root hybrid sums

Cauchy–Schwarz bounds the sum of square roots of a sequence supported below a finite cutoff.
Combined with the square-root Minkowski inequality, it aggregates families of challenge-indexed
hybrid estimates before charging their common cutoff. The weights may be extended nonnegative
reals, and no separate summability hypotheses are required.
-/

public section

open scoped ENNReal

namespace Quantum

/-- Cauchy–Schwarz for the square roots of a sequence supported below a finite cutoff. -/
theorem tsum_rpow_inv_two_le_of_cutoff (f : ℕ → ℝ≥0∞) (n : ℕ)
    (hcut : ∀ j, n ≤ j → f j = 0) :
    ∑' j, f j ^ (2⁻¹ : ℝ) ≤ ((n : ℝ≥0∞) * ∑' j, f j) ^ (2⁻¹ : ℝ) := by
  have hz : ∀ j ∉ Finset.range n, f j ^ (2⁻¹ : ℝ) = 0 :=
    fun j hj ↦ by
      rw [hcut j (by simpa using hj), ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz, ENNReal.le_rpow_inv_iff (by norm_num)]
  calc (∑ j ∈ Finset.range n, f j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
      ≤ ((Finset.range n).card : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ∑ j ∈ Finset.range n, (f j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ (by norm_num)
    _ = (n : ℝ≥0∞) * ∑ j ∈ Finset.range n, f j := by
        simp only [Finset.card_range, rpow_inv_two_rpow_two]
        norm_num
    _ ≤ _ := by
        gcongr
        exact ENNReal.sum_le_tsum _

/-- Aggregate square-root hybrid bounds over a family of challenges before applying
Cauchy–Schwarz to their common call cutoff. No finiteness assumption on the challenge type
or summability assumption on the weights is needed. -/
theorem rpow_inv_two_tsum_le_of_le_add_tsum_of_cutoff {Y : Type*}
    (p a : Y → ℝ≥0∞) (m : ℕ → Y → ℝ≥0∞) (n : ℕ)
    (hcut : ∀ j, n ≤ j → ∀ y, m j y = 0)
    (h : ∀ y, p y ^ (2⁻¹ : ℝ) ≤ a y ^ (2⁻¹ : ℝ) +
      ∑' j, m j y ^ (2⁻¹ : ℝ)) :
    (∑' y, p y) ^ (2⁻¹ : ℝ) ≤ (∑' y, a y) ^ (2⁻¹ : ℝ) +
      ((n : ℝ≥0∞) * ∑' j, ∑' y, m j y) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_tsum_le_of_le_add_tsum h).trans (add_le_add le_rfl ?_)
  exact tsum_rpow_inv_two_le_of_cutoff _ n fun j hj ↦ by simp [hcut j hj]

end Quantum
