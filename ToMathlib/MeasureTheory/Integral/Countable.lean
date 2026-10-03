/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Lebesgue integrals against measures concentrated on countable sets

An integral against a measure concentrated on a countable set is the sum over the whole space of
the singleton masses times the integrand, since the singleton masses vanish off that set. Unlike
`MeasureTheory.lintegral_countable'`, the space itself need not be countable.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {μ : Measure X}
  {s : Set X}

/-- An integral against a measure concentrated on a countable set is the sum over the whole
space of the singleton masses times the integrand. -/
theorem lintegral_eq_tsum_mul_of_ae_mem_countable (hs : s.Countable) (h : ∀ᵐ x ∂μ, x ∈ s)
    (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  have hsum : ∫⁻ x, f x ∂μ = ∑' x : s, f x * μ {(x : X)} := by
    rw [← lintegral_countable f hs, Measure.restrict_eq_self_of_ae_mem h]
  rw [hsum, ← tsum_subtype_eq_of_support_subset (s := s) (f := fun x ↦ μ {x} * f x)]
  · simp only [mul_comm]
  · intro x hx
    by_contra hxs
    refine hx ?_
    simp only
    rw [measure_mono_null (Set.singleton_subset_iff.2 hxs) (ae_iff.1 h), zero_mul]

end MeasureTheory
