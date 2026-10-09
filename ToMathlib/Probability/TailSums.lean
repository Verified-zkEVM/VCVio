/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Tail sums for natural-valued observables

The expectation of a measurable natural-valued observable is the sum of its tail measures.
The underlying measure and measurable space are arbitrary.
-/

public section

namespace MeasureTheory

open scoped ENNReal

/-- The integral of a measurable natural-valued observable is the sum of the measures of its
strict upper tails. No finiteness or probability assumption is needed. -/
theorem lintegral_coe_nat_eq_tsum {α : Type*} [MeasurableSpace α]
    {f : α → ℕ} (hf : Measurable f) (μ : Measure α) :
    ∫⁻ a, (f a : ℝ≥0∞) ∂μ = ∑' i : ℕ, μ {a | i < f a} := by
  have hnat (n : ℕ) : (n : ℝ≥0∞) = ∑' i : ℕ, if i < n then 1 else 0 := by
    rw [tsum_eq_sum (s := Finset.range n)]
    · rw [Finset.sum_ite_of_true (fun i hi ↦ Finset.mem_range.mp hi)]
      simp
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp [hi]
  simp_rw [hnat]
  have hs (i : ℕ) : MeasurableSet {a | i < f a} :=
    hf (MeasurableSet.of_discrete : MeasurableSet {n : ℕ | i < n})
  rw [lintegral_tsum (fun i ↦ (measurable_const.ite (hs i) measurable_const).aemeasurable)]
  refine tsum_congr fun i ↦ ?_
  simpa only [Set.indicator, Set.mem_ofPred_eq, lintegral_const, one_mul,
    Measure.restrict_apply_univ] using
    lintegral_indicator (hs i) (fun _ : α ↦ (1 : ℝ≥0∞))

end MeasureTheory
