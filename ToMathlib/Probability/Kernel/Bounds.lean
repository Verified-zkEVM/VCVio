/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Bounds
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Conditional event comparisons for kernel composition

An AE conditional comparison against finitely many reference events remains valid after a
common measure. Reference kernels may have different output spaces. No probability or finiteness
assumptions are needed, and the integrated conditional allowance need not be measurable.
-/

public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Fintype ι]
    {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]

/-- Integrate an AE conditional comparison against finitely many observed reference kernels. -/
theorem comp_apply_le_sum_add_lintegral_ae
    (κ : Kernel α β) (η : ∀ i, Kernel α (γ i)) (μ : Measure α)
    {event : Set β} (hevent : MeasurableSet event)
    (events : ∀ i, Set (γ i)) (hevents : ∀ i, MeasurableSet (events i))
    (bound : α → ENNReal)
    (h : ∀ᵐ a ∂μ, κ a event ≤ (∑ i, η i a (events i)) + bound a) :
    (κ ∘ₘ μ) event ≤ (∑ i, (η i ∘ₘ μ) (events i)) + ∫⁻ a, bound a ∂μ :=
  Measure.bind_apply_le_sum_add_lintegral_ae μ κ (fun i ↦ η i) κ.aemeasurable
    (fun i ↦ (η i).aemeasurable) hevent events hevents bound h

end ProbabilityTheory.Kernel
