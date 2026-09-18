/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.MeasureTheory.Integral.Quadratic
public import ToMathlib.MeasureTheory.Measure.Option

/-!
# Probability bounds for computation observations

Conditional independent draws bound the squared probability of a single event. The common draw
may lose mass. Observations are made in `Prop`, so intermediate types need no measurable-space
arguments in the public statements.
-/

public section

open MeasureTheory

universe v

/-- Two independent executions after a common draw bound the squared single-execution event. -/
theorem prEvent_bind_sq_le_bind_pair
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} (source : m α) (f : α → m β) (p : β → Prop) :
    Pr{let y ← source >>= f}[p y] ^ 2 ≤
      Pr{let x ← source; let a ← f x; let b ← f x}[p a ∧ p b] := by
  let : MeasurableSpace α := ⊤
  have hpair :
      Pr{let x ← source; let a ← f x; let b ← f x}[p a ∧ p b] =
        ∫⁻ x, Pr{let a ← f x}[p a] ^ 2 ∂𝒟[source] := by
    calc
      _ = Pr{let z ← (source >>= fun x ↦ do
              let a ← f x
              let b ← f x
              return (a, b))}[p z.1 ∧ p z.2] := by
        simp only [bind_assoc, pure_bind]
      _ = _ := by
        rw [prEvent_bind_eq_lintegral_of_discrete]
        simp only [bind_assoc, pure_bind, prEvent_bind_bind_and, sq]
  rw [prEvent_bind_eq_lintegral_of_discrete, hpair]
  exact ENNReal.sq_lintegral_le_lintegral_sq Measurable.of_discrete.aemeasurable

/-- Finite selector events in an optional output have total probability at most the event that
an output is present. Intermediate values need no measurable-space argument. -/
theorem sum_prEvent_option_map_eq_some_le_isSome
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α γ : Type} [Fintype γ] (mx : m (Option α)) (select : α → Option γ) :
    ∑ k : γ, Pr{let r ← mx}[r.map select = some (some k)] ≤ Pr{let r ← mx}[r.isSome] := by
  let : MeasurableSpace α := ⊤
  simpa only [prEvent_eq_evalDist_of_discrete] using
    (Measure.sum_apply_option_map_eq_some_le_isSome 𝒟[mx] select
      fun _ ↦ MeasurableSet.of_discrete)
