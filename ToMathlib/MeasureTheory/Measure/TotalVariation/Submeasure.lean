/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Variation of a successful-output approximation

When one finite measure is below another, their event total variation is exactly the mass
still missing from the approximation. This applies directly to fuel-bounded returned laws.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- Ordered finite measures differ in event total variation by their missing total mass. -/
theorem etvDist_eq_sub_univ_of_le {μ ν : Measure X} [IsFiniteMeasure μ] (h : μ ≤ ν) :
    μ.etvDist ν = ν Set.univ - μ Set.univ := by
  apply le_antisymm
  · apply iSup_le
    intro s
    rw [ENNReal.absDiff, tsub_eq_zero_of_le (h s), zero_add,
      ← Measure.sub_apply s.2 h, ← Measure.sub_apply MeasurableSet.univ h]
    exact measure_mono (Set.subset_univ _)
  · have hu := absDiff_apply_le_etvDist μ ν MeasurableSet.univ
    simpa only [ENNReal.absDiff, tsub_eq_zero_of_le (h Set.univ), zero_add] using hu

end MeasureTheory.Measure
