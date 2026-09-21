/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Finite additive comparisons of nonnegative integrals

AE bounds by finite reference families integrate to the corresponding sum of integrals.
Only the reference functions need AE measurability. The measure need not be finite, and the
conditional allowance need not be measurable.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integrate an AE upper bound by a finite reference sum and an arbitrary allowance. -/
theorem lintegral_le_sum_add_lintegral_of_le_ae (s : Finset ι)
    {f bound : α → ENNReal} {g : ι → α → ENNReal}
    (hg : ∀ i ∈ s, AEMeasurable (g i) μ)
    (h : ∀ᵐ a ∂μ, f a ≤ (∑ i ∈ s, g i a) + bound a) :
    (∫⁻ a, f a ∂μ) ≤ (∑ i ∈ s, ∫⁻ a, g i a ∂μ) + ∫⁻ a, bound a ∂μ := by
  refine (lintegral_mono_ae h).trans_eq ?_
  rw [lintegral_add_left' (Finset.aemeasurable_fun_sum _ hg)]
  congr 1
  exact lintegral_finsetSum' s hg

end MeasureTheory
