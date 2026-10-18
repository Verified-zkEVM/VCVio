/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.MeasureTheory.Measure.Trim
public import ToMathlib.MeasureTheory.Measure.TotalVariation

/-!
# Observable laws and sub-σ-algebras

The σ-algebra pulled back along an observation contains exactly the events visible through
that observation. Equality on this σ-algebra is equality of the observed pushforward laws.
Measurable postprocessing can only decrease the event-supremum total variation distance.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Equality after observation is precisely equality on the observation's σ-algebra. -/
theorem map_eq_iff_trim_comap_eq (μ ν : Measure X) {observe : X → Y}
    (hobserve : Measurable observe) :
    μ.map observe = ν.map observe ↔ μ.trim hobserve.comap_le = ν.trim hobserve.comap_le := by
  constructor
  · intro h
    apply @Measure.ext X (MeasurableSpace.comap observe inferInstance)
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [trim_comap_apply hobserve ht, trim_comap_apply hobserve ht, h]
  · intro h
    rw [← map_trim_comap hobserve, ← map_trim_comap hobserve, h]

/-- A measurable factorization transports equality of observable laws. -/
theorem map_eq_of_factor (μ ν : Measure X) {fine : X → Y} (hfine : Measurable fine)
    {coarse : X → Z} {factor : Y → Z} (hfactor : Measurable factor)
    (hcommute : coarse = factor ∘ fine) (h : μ.map fine = ν.map fine) :
    μ.map coarse = ν.map coarse := by
  rw [hcommute, ← Measure.map_map hfactor hfine, ← Measure.map_map hfactor hfine, h]

/-- Event total variation decreases when a public view is measurably coarsened. -/
theorem etvDist_map_le_of_factor (μ ν : Measure X) {fine : X → Y} (hfine : Measurable fine)
    {coarse : X → Z} {factor : Y → Z} (hfactor : Measurable factor)
    (hcommute : coarse = factor ∘ fine) :
    (μ.map coarse).etvDist (ν.map coarse) ≤ (μ.map fine).etvDist (ν.map fine) := by
  rw [hcommute, ← Measure.map_map hfactor hfine, ← Measure.map_map hfactor hfine]
  exact etvDist_map_le _ _ _ hfactor

end MeasureTheory.Measure
