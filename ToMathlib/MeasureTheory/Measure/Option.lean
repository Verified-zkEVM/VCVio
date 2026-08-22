/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.MeasureTheory.MeasurableSpace.Option
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Discarding the `none` part of an option-valued measure

`Measure.dropNone` turns a measure on `Option α` into the submeasure of successful values on
`α`. It is the effect-preserving boundary needed by `OptionT` and by finite observations of a
possibly nonterminating computation: the `none` mass is discarded instead of being confused with
an ordinary result.

The definition uses the Giry bind. The coproduct measurable structure makes the success/failure
case split measurable without requiring `α` itself to be discrete.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- Keep the mass at `some x` as mass at `x`, and discard the mass at `none`. -/
noncomputable def dropNone (μ : Measure (Option α)) : Measure α :=
  Measure.bind μ fun
    | none => 0
    | some x => Measure.dirac x

/-- The measure family used by `dropNone` is measurable for every measurable result space. -/
theorem measurable_dropNoneKernel : Measurable fun value : Option α =>
    match value with
    | none => 0
    | some x => Measure.dirac x :=
  Option.measurable_elim measurable_const Measure.measurable_dirac

@[simp]
theorem dropNone_zero : dropNone (0 : Measure (Option α)) = 0 := by
  simp [dropNone, Measure.bind_zero_left]

@[simp]
theorem dropNone_dirac_none :
    dropNone (Measure.dirac (none : Option α)) = 0 := by
  rw [dropNone, Measure.dirac_bind measurable_dropNoneKernel]

@[simp]
theorem dropNone_dirac_some (x : α) :
    dropNone (Measure.dirac (some x)) = Measure.dirac x := by
  rw [dropNone, Measure.dirac_bind measurable_dropNoneKernel]

/-- Discarding `none` cannot increase the total mass. -/
theorem dropNone_apply_univ_le (μ : Measure (Option α)) :
    dropNone μ Set.univ ≤ μ Set.univ := by
  rw [dropNone, Measure.bind_apply MeasurableSet.univ measurable_dropNoneKernel.aemeasurable,
    ← lintegral_one]
  apply lintegral_mono
  intro value
  cases value <;> simp

end MeasureTheory.Measure
