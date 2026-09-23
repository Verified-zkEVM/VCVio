/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Batteries.Control.AlternativeMonad
public import VCVio.EvalDist.Defs.Measure.Failure
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Failure in measure-valued compositions

Failure contributes no successful outputs to a measurable composition. The intermediate
measurable-space choice is internal to these laws, so final observations need no source space.
-/

public section

open MeasureTheory

universe u v

variable {m : Type u → Type v} [AlternativeMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
  {α β : Type u} [MeasurableSpace β]

/-- Binding any continuation after failure has zero successful-output measure. -/
@[simp, grind =]
theorem evalDist_failure_bind (f : α → m β) : 𝒟[(failure : m α) >>= f] = 0 := by
  let : MeasurableSpace α := ⊤
  rw [evalDist_bind_of_discrete, evalDist_failure_eq_zero, Measure.bind_zero_left]

/-- A continuation that always fails has zero successful-output measure. -/
@[simp↓ high, grind norm↓]
theorem evalDist_bind_failure (mx : m α) :
    𝒟[mx >>= fun _ ↦ (failure : m β)] = 0 := by
  let : MeasurableSpace α := ⊤
  simp

/-- No final event succeeds after failure. -/
@[simp↓ high, grind norm↓]
theorem prEvent_failure {m : Type → Type v} [AlternativeMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type} (p : α → Prop) : Pr{let x ← (failure : m α)}[p x] = 0 := by
  simp
