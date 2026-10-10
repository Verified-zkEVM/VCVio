/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Lebesgue integrals against measures concentrated on countable sets

An integral against a measure concentrated on a countable set `s` is the sum over `s` of the
integrand weighted by the singleton masses. Since the singleton masses vanish off `s`, it is also
the sum of those weighted terms over the whole space, with no countability assumption on the
space itself.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {μ : Measure X}
  {s : Set X}

/-- Integrals against a measure concentrated on a countable set are sums over that set. -/
theorem lintegral_eq_tsum_of_ae_mem_countable (hs : s.Countable) (h : ∀ᵐ x ∂μ, x ∈ s)
    (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂μ = ∑' x : s, f x * μ {(x : X)} := by
  rw [← lintegral_countable f hs, Measure.restrict_eq_self_of_ae_mem h]

/-- Integrals against a measure concentrated on a countable set are sums of the singleton masses
times the integrand over the whole space. -/
theorem lintegral_eq_tsum_mul_of_ae_mem_countable (hs : s.Countable) (h : ∀ᵐ x ∂μ, x ∈ s)
    (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  rw [lintegral_eq_tsum_of_ae_mem_countable hs h f,
    ← tsum_subtype_eq_of_support_subset (s := s) (f := fun x ↦ μ {x} * f x)]
  · simp only [mul_comm]
  · intro x hx
    by_contra hxs
    refine hx ?_
    simp only
    rw [measure_mono_null (Set.singleton_subset_iff.2 hxs) (ae_iff.1 h), zero_mul]

end MeasureTheory
