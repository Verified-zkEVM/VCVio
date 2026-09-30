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

/-- Failure has expectation zero. -/
@[simp↓ high, grind norm↓]
theorem wp_failure {m : Type → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type} (g : α → ENNReal) : wp⟦(failure : m α)⟧ g = 0 := by
  let : MeasurableSpace α := ⊤
  rw [MeasureProgramLogic.wp_eq_lintegral _ g Measurable.of_discrete]
  simp

/-- A guard weights the observation by its condition. It applies ahead of `wp_const`, so the
condition of a guard stays the first factor. -/
@[simp high, grind norm]
theorem wp_guard {m : Type → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    (c : Prop) [Decidable c] (g : Unit → ENNReal) :
    wp⟦(guard c : m Unit)⟧ g = propInd c * g () := by
  by_cases hc : c <;> simp [guard, hc]

/-- No event succeeds after failure. -/
theorem prEvent_failure {m : Type → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type} (p : α → Prop) : Pr{let x ← (failure : m α)}[p x] = 0 :=
  wp_failure (m := m) _

/-- `failure` always fails. -/
@[simp, grind =]
theorem prFail_failure {m : Type → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type} : prFail (failure : m α) = 1 := by
  simp [prFail_def]

/-- `guard p` fails exactly when `p` does not hold. -/
@[simp]
theorem prFail_guard {m : Type → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    (p : Prop) [Decidable p] : prFail (guard p : m Unit) = if p then 0 else 1 := by
  by_cases hp : p <;> simp [guard, hp]

