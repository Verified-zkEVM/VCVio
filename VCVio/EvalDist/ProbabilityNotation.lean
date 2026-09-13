/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Basic

/-!
# Measure events for computation notation

`Pr{...}[...]` interprets an ordinary Lean `do` computation as the successful-output
measure of its Boolean or propositional result. These equations identify that measure
with an event in the underlying computation when the event is measurable.
-/

public section

open MeasureTheory

universe v

/-- A measurable predicate returned by a computation has the probability of its event. -/
theorem probEventBinding_eq_evalDist {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p : α → Prop)
    (hp : Measurable p) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} := by
  change 𝒟[mx >>= (pure ∘ p)] {True} = _
  rw [← map_eq_bind_pure_comp, evalDist_map mx hp,
    Measure.map_apply hp (measurableSet_singleton True)]
  simp

/-- On a discrete output space every predicate is a measurable event. -/
theorem probEventBinding_eq_evalDist_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} :=
  probEventBinding_eq_evalDist mx p Measurable.of_discrete
