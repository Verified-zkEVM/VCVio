/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.OptionT
public import VCVio.EvalDist.ProbabilityBounds
public import ToMathlib.Control.OptionT

/-!
# Events of optional computations

Native successful-output semantics turns a sampled guard into a condition on the sampled value.
The intermediate measurable space is internal to the observation law. Wrapped computations are
observed through their present values, and sequencing a lossless prefix with continuations that
succeed on its reachable outputs preserves probability-one events.
-/

public section

open MeasureTheory

universe v

namespace OptionT

/-- Successful events are the events of present values in the underlying run. -/
theorem prEvent_eq_run {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : OptionT m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = Pr{let value ← mx.run}[value.elim False p] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    OptionT.evalDist_apply]
  congr 1
  ext value
  cases value <;> simp

/-- Lifting into the optional monad preserves the probability of an observed event. -/
@[simp↓ high, grind norm↓]
theorem prEvent_lift {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) :
    Pr{let x ← OptionT.lift mx}[p x] = Pr{let x ← mx}[p x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    OptionT.evalDist_lift]

/-- A guard contributes its condition to the observed event after a lifted draw. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) [DecidablePred p] :
    Pr{let x ← OptionT.lift mx; guard (p x)}[q x] =
      Pr{let x ← mx}[p x ∧ q x] := by
  classical
  let : MeasurableSpace α := ⊤
  have h (x : α) : Pr{let _ ← (guard (p x) : OptionT m Unit)}[q x] =
      if p x ∧ q x then 1 else 0 := by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [guard, hp, hq]
  rw [_root_.evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton True) Measurable.of_discrete.aemeasurable,
    OptionT.evalDist_lift]
  simp_rw [h]
  rw [prEvent_eq_evalDist_of_discrete]
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    lintegral_indicator_one (μ := 𝒟[mx]) (MeasurableSet.of_discrete (s := {x | p x ∧ q x}))

/-- A constant map after a sampled guard contributes its guard to the observed event. -/
@[simp high, grind norm]
theorem prEvent_bind_map_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) [DecidablePred p] :
    𝒟[do let x ← OptionT.lift mx; (fun _ : Unit ↦ q x) <$> guard (p x)] {True} =
      Pr{let x ← mx}[p x ∧ q x] := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using prEvent_bind_guard mx p q

/-- A lifted draw followed by a guard puts its successful event mass at the unit output. -/
@[simp↓ high]
theorem evalDist_lift_bind_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    𝒟[do let x ← OptionT.lift mx; guard (p x)] =
      Pr{let x ← mx}[p x] • Measure.dirac () := by
  apply Measure.ext_of_singleton
  rintro ⟨⟩
  rw [← prEvent_eq_evalDist_singleton]
  simp

/-- A monadic lift followed by a guard puts its successful event mass at the unit output. -/
@[simp↓ high]
theorem evalDist_liftM_bind_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    𝒟[do let x ← (liftM mx : OptionT m α); guard (p x)] =
      Pr{let x ← mx}[p x] • Measure.dirac () :=
  evalDist_lift_bind_guard mx p

/-- A successful event of a wrapped computation is the event of present values that satisfy it
in the underlying computation. -/
theorem prEvent_mk {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m (Option α)) (p : α → Prop) :
    Pr{let x ← OptionT.mk mx}[p x] = Pr{let o ← mx}[o.elim False p] := by
  rw [prEvent_eq_run, OptionT.run_mk]

section sequencing

variable {m : Type → Type v} [Monad m] [LawfulMonad m] {α β : Type}

/-- A wrapped bind is a lifted prefix followed by the wrapped continuations. -/
theorem mk_bind_eq_lift_bind (mx : m α) (f : α → m (Option β)) :
    OptionT.mk (mx >>= f) = (OptionT.lift mx >>= fun a ↦ OptionT.mk (f a) : OptionT m β) := by
  simp [OptionT.ext_iff]

variable [MonadAttach m] [ExactMonadAttach m]

/-- Reachable outputs of a lifted computation are reachable in the computation. -/
theorem mem_support_of_mem_support_lift {mx : m α} {a : α}
    (ha : a ∈ support (OptionT.lift mx)) : a ∈ support mx := by
  rw [MonadAttach.mem_support, MonadAttach.OptionT.canReturn_iff, OptionT.run_lift,
    MonadAttach.mem_support_bind] at ha
  obtain ⟨a', ha', h⟩ := ha
  rw [MonadAttach.mem_support_pure] at h
  exact Option.some_injective _ h ▸ ha'

variable [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- A lossless prefix followed by continuations that each satisfy an event with probability one
on the prefix's reachable outputs satisfies the event with probability one. -/
theorem prEvent_mk_bind_eq_one_of_support (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m (Option β)) (p : β → Prop)
    (h : ∀ a ∈ support mx, Pr{let y ← OptionT.mk (f a)}[p y] = 1) :
    Pr{let y ← OptionT.mk (mx >>= f)}[p y] = 1 := by
  rw [mk_bind_eq_lift_bind]
  refine le_antisymm (prEvent_le_one _ _) ?_
  refine le_prEvent_bind_of_forall_le_of_support (OptionT.lift mx) ?_ _ p ?_
  · rwa [prEvent_lift]
  · exact fun a ha ↦ (h a (mem_support_of_mem_support_lift ha)).ge

/-- An upper bound on the wrapped continuation event over reachable prefixes. -/
theorem prEvent_mk_bind_le_of_forall_le (mx : m α) (f : α → m (Option β)) (q : β → Prop)
    {ε : ENNReal} (h : ∀ a ∈ support mx, Pr{let y ← OptionT.mk (f a)}[q y] ≤ ε) :
    Pr{let y ← OptionT.mk (mx >>= f)}[q y] ≤ ε := by
  rw [mk_bind_eq_lift_bind]
  exact prEvent_bind_le_of_forall_le_of_support (OptionT.lift mx) _ q fun a ha ↦
    h a (mem_support_of_mem_support_lift ha)

end sequencing

end OptionT
