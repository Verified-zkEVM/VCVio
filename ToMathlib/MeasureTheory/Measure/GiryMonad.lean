/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Pushforward and Giry bind

Measurable pushforwards commute with composition of measure-valued families. A fixed s-finite
measure also gives a measurable family under a jointly measurable parameterized pushforward.
These laws keep the measurable spaces explicit and impose no normalization of the measures.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Pushing a fixed s-finite measure through a jointly measurable parameterized map gives a
measurable family of measures. -/
theorem measurable_map_parameter (μ : Measure β) [SFinite μ]
    {f : α × β → γ} (hf : Measurable f) :
    Measurable fun a ↦ μ.map (fun b ↦ f (a, b)) := by
  have h := (measurable_map f hf).comp (Measurable.map_prodMk_left (ν := μ))
  simpa only [Measure.map_map hf measurable_prodMk_left, Function.comp_def] using h

end MeasureTheory.Measure
