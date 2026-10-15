/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Execution
public import Interop.Cryptol.Model.Domain
public import ToCslib.Order.Admissible

/-!
# Admissible logical relation for lazy values

Defined semantic values have terminating operational witnesses. Lazy fields
are related recursively, and functions preserve the relation on suspended
arguments. Closure under increasing suprema justifies least-fixed-point
induction without assuming that a recursive program terminates.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Lift a relation on outer values to computations and closed expressions. -/
@[expose] def LiftRelation {a : ClosedTy} (R : Value a → RuntimeValue a → Prop)
    (d : Computation a) (e : Expr [] a) : Prop :=
  WithBot.recBotCoe True (Sum.elim
    (fun err => Evaluates e (.error err.value))
    (fun v => ∃ w, Evaluates e (.ok w) ∧ R v w)) d

/-- Related outer values agree on all recursively demanded components. -/
@[expose] def ValueRelation : (a : ClosedTy) → Value a → RuntimeValue a → Prop
  | .var e, _, _ => e.elim
  | .bit, d, .bit b => d.value = b
  | .integer, d, .integer i => d.value = i
  | .unit, _, .unit => True
  | .seq l a, d, .sequence _ body => ∀ i : l.Index,
      LiftRelation (ValueRelation a) (d i)
        (body.substOne (.integer (Length.indexNat i)))
  | .prod a b, d, .pair x y =>
      LiftRelation (ValueRelation a) d.1 x ∧ LiftRelation (ValueRelation b) d.2 y
  | .arrow a b, d, .function body => ∀ x : Computation a, ∀ argument : Expr [] a,
      LiftRelation (ValueRelation a) x argument →
        LiftRelation (ValueRelation b) (ContinuousHom.toOrderHom d x)
          (body.substOne argument)

/-- The logical relation between a semantic computation and a closed program. -/
abbrev Related {a : ClosedTy} (d : Computation a) (e : Expr [] a) : Prop :=
  LiftRelation (ValueRelation a) d e

@[simp] theorem related_bot {a : ClosedTy} (e : Expr [] a) : Related ⊥ e := trivial

@[simp] theorem related_error {a : ClosedTy} (err : EvalError) (e : Expr [] a) :
    Related (.error err) e ↔ Evaluates e (.error err) := Iff.rfl

@[simp] theorem related_value {a : ClosedTy} (v : Value a) (e : Expr [] a) :
    Related (.value v) e ↔ ∃ w, Evaluates e (.ok w) ∧ ValueRelation a v w := Iff.rfl

/-- Operational witnesses in a lifted logical relation are unique. This
allows the same witness to be used throughout an increasing semantic chain. -/
theorem admissible_liftRelation {a : ClosedTy} {R : Value a → RuntimeValue a → Prop}
    (hR : ∀ w, Admissible (fun v => R v w)) (e : Expr [] a) :
    Admissible (fun d => LiftRelation R d e) := by
  apply Admissible.withBot
  apply Admissible.sum (admissible_discrete _)
  intro c hc
  obtain ⟨w, hw, _⟩ := hc 0
  refine ⟨w, hw, hR w c (fun n => ?_)⟩
  obtain ⟨w', hw', hr'⟩ := hc n
  have hww : w = w' := Except.ok.inj (hw.unique hw')
  exact hww ▸ hr'

/-- The value relation is admissible at every simple type, including
continuous functions and infinite sequences. -/
theorem admissible_valueRelation (a : ClosedTy) (w : RuntimeValue a) :
    Admissible (fun v => ValueRelation a v w) := by
  induction a with
  | var e => exact e.elim
  | bit => exact admissible_discrete _
  | integer => exact admissible_discrete _
  | unit => exact admissible_discrete _
  | seq l a ih =>
      cases w with
      | sequence _ body =>
          apply Admissible.forall
          intro i
          exact (admissible_liftRelation ih (body.substOne (.integer (Length.indexNat i)))).comp
            (.ofFun (fun xs : Value (.seq l a) => xs i))
  | prod a b iha ihb =>
      cases w with
      | pair x y =>
          intro c hc
          exact ⟨(admissible_liftRelation iha x).comp (.ofFun Prod.fst) c (fun n => (hc n).1),
            (admissible_liftRelation ihb y).comp (.ofFun Prod.snd) c (fun n => (hc n).2)⟩
  | arrow a b _ ihb =>
      cases w with
      | function body =>
          apply Admissible.forall
          intro x
          apply Admissible.forall
          intro arg
          apply Admissible.forall
          intro _
          exact (admissible_liftRelation ihb (body.substOne arg)).comp
            (.ofFun (fun f : Computation a →𝒄 Computation b => f x))

/-- The computation relation is admissible; recursive approximations may be
related before any terminating result is available. -/
theorem admissible_related {a : ClosedTy} (e : Expr [] a) :
    Admissible (fun d => Related d e) :=
  admissible_liftRelation (admissible_valueRelation a) e

/-- Transfer a logical relation along an operational simulation that retains
each terminating result. -/
theorem Related.mono {a : ClosedTy} {d : Computation a} {e e' : Expr [] a}
    (h : Related d e) (he : ∀ r, Evaluates e r → Evaluates e' r) : Related d e' := by
  induction d using WithBot.recBotCoe with
  | bot => trivial
  | coe v =>
      cases v with
      | inl err => exact he (.error err.value) h
      | inr v =>
          obtain ⟨w, hw, hr⟩ := h
          exact ⟨w, he (.ok w) hw, hr⟩

/-- The same logical relation at an intermediate machine configuration. -/
@[expose] def StateRelated {a : ClosedTy} (d : Computation a) (state : MachineState a) : Prop :=
  WithBot.recBotCoe True (Sum.elim
    (fun err => state.Executes (.error err.value))
    (fun v => ∃ w, state.Executes (.ok w) ∧ ValueRelation a v w)) d

/-- Transfer a state relation along a simulation of its terminating outcomes. -/
theorem StateRelated.mono {a : ClosedTy} {d : Computation a} {state next : MachineState a}
    (h : StateRelated d state) (he : ∀ r, state.Executes r → next.Executes r) :
    StateRelated d next := by
  induction d using WithBot.recBotCoe with
  | bot => trivial
  | coe v =>
      cases v with
      | inl err => exact he (.error err.value) h
      | inr v =>
          obtain ⟨w, hw, hr⟩ := h
          exact ⟨w, he (.ok w) hw, hr⟩

/-- One machine transition can precede a related configuration. -/
theorem StateRelated.prev {a : ClosedTy} {d : Computation a} {state next : MachineState a}
    (h : StateRelated d next) (hs : state.step = .inr next) : StateRelated d state :=
  h.mono (fun _ hr => .next hs hr)

/-- The error state is related to its semantic error. -/
theorem StateRelated.error {a : ClosedTy} (e : EvalError) :
    StateRelated (DomainResult.error e : Computation a) (.error e) :=
  Control.Transition.Executes.done rfl

/-- A returned outer value is related when its components are related. -/
theorem StateRelated.value {a : ClosedTy} {v : Value a} {w : RuntimeValue a}
    (h : ValueRelation a v w) : StateRelated (.value v) (.value w .done) :=
  ⟨w, .done rfl, h⟩

/-- Related evaluation composes with a caller that relates each returned
value to the continuous continuation. Errors propagate through the caller. -/
theorem StateRelated.bind {a b : ClosedTy} {d : Computation a} {e : Expr [] a}
    (f : Value a →𝒄 Computation b) (stack : Stack a b) (hd : Related d e)
    (hk : ∀ v w, ValueRelation a v w → StateRelated (f v) (.value w stack)) :
    StateRelated (DomainResult.bind f d) (.eval e stack) := by
  induction d using WithBot.recBotCoe with
  | bot => trivial
  | coe v =>
      cases v with
      | inl err =>
          exact (hd : e.start.Executes (.error err.value)).attach stack (.done rfl)
      | inr v =>
          obtain ⟨w, hw, hr⟩ := hd
          exact (hk v w hr).mono (fun _ hcont => hw.attach stack hcont)

end Interop.Cryptol
