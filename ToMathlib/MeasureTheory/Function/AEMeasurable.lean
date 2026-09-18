/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Almost everywhere measurable functions on countable concentration sets

A function need only be controlled on the portion of its domain seen by the input measure.
On a countable measurable concentration set, every function has a measurable modification.
-/

public section

open MeasureTheory

universe u v

namespace MeasureTheory

/-- Every function is almost everywhere measurable when the input measure concentrates on a
countable set of measurable singleton points. -/
theorem aemeasurable_of_ae_mem_countable {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [Nonempty β]
    {μ : Measure α} {s : Set α} (hs : s.Countable) (hμ : ∀ᵐ a ∂μ, a ∈ s) (f : α → β) :
    AEMeasurable f μ := by
  classical
  let point : β := Classical.choice inferInstance
  let g : α → β := fun a ↦ if a ∈ s then f a else point
  have hg : Measurable g :=
    (show Measurable (fun _ : α ↦ point) from measurable_const).measurable_of_countable_ne
    (hs.mono fun a ha ↦ by
      by_contra h
      exact ha (by simp [g, h]))
  exact ⟨g, hg, hμ.mono fun a ha ↦ by simp [g, ha]⟩

end MeasureTheory
