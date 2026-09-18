/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Integral.Quadratic
public import ToMathlib.Probability.Kernel.Subprobability
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Quadratic bounds for conditional independent draws

Two independent draws from the same conditional kernel dominate the square of a single event's
marginal probability. Cauchy–Schwarz applies to the common input measure, including continuous
input spaces and a common draw that may lose mass.
-/

public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Two conditionally independent draws bound the squared marginal event probability. -/
lemma comp_apply_sq_le_prod_comp_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (μ : Measure α) [IsSubprobabilityMeasure μ] {s : Set β} (hs : MeasurableSet s) :
    ((κ ∘ₘ μ) s) ^ 2 ≤ ((κ ×ₖ κ) ∘ₘ μ) (s ×ˢ s) := by
  simp only [Measure.bind_apply hs κ.aemeasurable,
    Measure.bind_apply (hs.prod hs) (κ.prod κ).aemeasurable,
    Kernel.prod_apply_prod, ← sq]
  exact ENNReal.sq_lintegral_le_lintegral_sq (κ.measurable_coe hs).aemeasurable

end ProbabilityTheory.Kernel
