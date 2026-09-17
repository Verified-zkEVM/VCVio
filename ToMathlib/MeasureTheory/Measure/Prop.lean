/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Propositional observation measures

The mass of the true proposition under a Dirac measure is the indicator of its proposition.
This normal form evaluates deterministic final events without exposing singleton functions.
-/

public section

namespace MeasureTheory.Measure

open scoped Classical in
/-- A deterministic proposition has true mass exactly when it holds. -/
@[simp high, grind =]
lemma dirac_apply_singleton_true (p : Prop) :
    dirac p {True} = if p then 1 else 0 := by
  simp [Pi.single_apply]

end MeasureTheory.Measure
