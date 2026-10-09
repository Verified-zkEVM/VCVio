/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.Data.ENNReal.AbsDiff
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Absolute differences of nonnegative integrals

The discrepancy between two nonnegative integrals is bounded by their integrated discrepancy.
Measurability is relative to the integration measure; finite integrals are not required.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ENNReal

/-- Absolute discrepancy is subadditive under integration of AE-measurable observations. -/
theorem absDiff_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ENNReal.absDiff (∫⁻ a, f a ∂μ) (∫⁻ a, g a ∂μ) ≤
      ∫⁻ a, ENNReal.absDiff (f a) (g a) ∂μ := by
  simp only [ENNReal.absDiff]
  rw [lintegral_add_left' (f := fun a ↦ f a - g a) (hf.sub hg)]
  exact add_le_add (lintegral_sub_le' g f hg) (lintegral_sub_le' f g hf)

end ENNReal
