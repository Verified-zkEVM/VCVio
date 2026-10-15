/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Binding
public import Interop.Cryptol.Model.Execution

/-!
# Soundness of abstract-machine execution

Typed evaluation frames denote continuous demands on a suspended computation.
The meaning of a whole configuration is invariant under machine transitions.
Consequently every finite execution agrees with the compositional domain
semantics, including returned values containing unevaluated components.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- The domain value represented by an operational outer value. -/
@[expose] noncomputable def RuntimeValue.denote {a : ClosedTy} : RuntimeValue a → Value a
  | .bit b => ⟨b⟩
  | .integer i => ⟨i⟩
  | .unit => ⟨()⟩
  | .function body => body.bodyDenote Environment.empty
  | .pair x y => (x.denote Environment.empty, y.denote Environment.empty)
  | .sequence l body => fun i : l.Index =>
      body.denote (Environment.empty.extend (.value ⟨(Length.indexNat i : Int)⟩))

/-- Interpret an operational result, keeping errors separate from values. -/
@[expose] noncomputable def Outcome.denote {a : ClosedTy} : Outcome a → Computation a
  | .ok v => .value v.denote
  | .error e => .error e

/-- Interpret a frame as a continuous demand on a suspended computation. -/
@[expose] noncomputable def Frame.denote {a b : ClosedTy} :
    Frame a b → Computation a →𝒄 Computation b
  | .force next => DomainResult.force.swapArgs (next.denote Environment.empty)
  | .app argument => DomainResult.applyContinuous.swapArgs
      (argument.denote Environment.empty)
  | .fst => DomainResult.bind (.ofFun Prod.fst)
  | .snd => DomainResult.bind (.ofFun Prod.snd)
  | .index i => Semantics.index.swapArgs (i.denote Environment.empty)
  | .indexInto l body => Semantics.index
      (.value (RuntimeValue.sequence l body).denote)
  | .branch x y => Semantics.conditional
      (x.denote Environment.empty, y.denote Environment.empty)
  | .bitNot => DomainResult.bind (DiscreteOrder.continuousMap fun b : Bool => .value ⟨!b⟩)
  | .bitLeft op right => (Semantics.binary (fun a b => .ok (op.eval a b))).swapArgs
      (right.denote Environment.empty)
  | .bitRight op left => Semantics.binary (fun a b => .ok (op.eval a b)) (.value ⟨left⟩)
  | .intLeft op right => (Semantics.binary op.eval).swapArgs (right.denote Environment.empty)
  | .intRight op left => Semantics.binary op.eval (.value ⟨left⟩)
  | .eqLeft right => (Semantics.binary (fun a b : Int => .ok (a == b))).swapArgs
      (right.denote Environment.empty)
  | .eqRight left => Semantics.binary (fun a b : Int => .ok (a == b)) (.value ⟨left⟩)
  | .ltLeft right => (Semantics.binary (fun a b : Int => .ok (decide (a < b)))).swapArgs
      (right.denote Environment.empty)
  | .ltRight left => Semantics.binary (fun a b : Int => .ok (decide (a < b))) (.value ⟨left⟩)

@[simp] theorem Frame.denote_error {a b : ClosedTy} (frame : Frame a b) (e : EvalError) :
    frame.denote (.error e) = .error e := by
  cases frame <;> rfl

/-- Interpret a stack by composing its frame meanings. -/
@[expose] noncomputable def Stack.denote {a b : ClosedTy} :
    Stack a b → Computation a →𝒄 Computation b
  | .done => .id
  | .push frame rest => rest.denote.comp frame.denote

@[simp] theorem Stack.denote_error {a b : ClosedTy} (stack : Stack a b) (e : EvalError) :
    stack.denote (.error e) = .error e := by
  induction stack with
  | done => rfl
  | push frame rest ih =>
      change rest.denote (frame.denote (.error e)) = _
      rw [Frame.denote_error, ih]

/-- Interpret the current suspended expression and all outstanding demands. -/
@[expose] noncomputable def MachineState.denote {r : ClosedTy} : MachineState r → Computation r
  | .eval e stack => stack.denote (e.denote Environment.empty)
  | .value v stack => stack.denote (.value v.denote)
  | .error e => .error e

/-- Resuming a returned value preserves the meaning of its frame and caller. -/
theorem MachineState.denote_resume {a b r : ClosedTy} (frame : Frame a b) (v : RuntimeValue a)
    (rest : Stack b r) :
    (MachineState.resume frame v rest).denote = rest.denote (frame.denote (.value v.denote)) := by
  cases frame <;> cases v
  case indexInto.integer l body i =>
    cases h : l.checkIndex i with
    | none =>
        simp only [resume, h, MachineState.denote, Frame.denote, RuntimeValue.denote]
        rw [Semantics.index_values, h, Stack.denote_error]
    | some j =>
        have hj := l.indexNat_checkIndex i j h
        simp only [resume, h, MachineState.denote, Frame.denote, RuntimeValue.denote]
        simp only [Semantics.index_values, h, Expr.denote_substOne, hj]
        rfl
  case branch.bit yes no b => cases b <;> rfl
  case intRight.integer op left right =>
    cases h : op.eval left right <;>
      simp only [resume, h, MachineState.denote, RuntimeValue.denote]
    all_goals change _ = rest.denote (ofExcept (op.eval left right))
    all_goals simp only [h, ofExcept]
    exact (rest.denote_error _).symm
  all_goals simp only [MachineState.resume, MachineState.denote, RuntimeValue.denote,
    Frame.denote, Stack.denote, ContinuousHom.comp_apply, Expr.denote_substOne]
  all_goals rfl

/-- Every total machine transition preserves the compositional meaning. -/
theorem MachineState.denote_step {r : ClosedTy} (state : MachineState r) :
    state.denote = match state.step with
      | .inl result => result.denote
      | .inr next => next.denote := by
  cases state with
  | error e => rfl
  | value v stack =>
      cases stack with
      | done => rfl
      | push frame rest => exact (denote_resume frame v rest).symm
  | eval e stack =>
      cases e <;> try rfl
      case var v => cases v
      case error e => exact stack.denote_error e
      case letE x body =>
        change stack.denote (body.denote (Environment.empty.extend (x.denote Environment.empty))) =
          stack.denote ((body.substOne x).denote Environment.empty)
        rw [Expr.denote_substOne]
      case fix body =>
        change stack.denote ((Expr.fix body).denote Environment.empty) =
          stack.denote ((body.substOne (.fix body)).denote Environment.empty)
        rw [Expr.denote_substOne]
        exact congrArg stack.denote (Expr.denote_fix body Environment.empty)

/-- Every terminating execution has the same meaning as its returned result. -/
theorem MachineState.Executes.sound {r : ClosedTy} {state : MachineState r} {result : Outcome r}
    (h : state.Executes result) : state.denote = result.denote := by
  induction h with
  | done hs => rw [denote_step, hs]
  | next hs _ ih => rw [denote_step, hs]; exact ih

/-- Soundness for closed expressions, including lazy outer values. -/
theorem Evaluates.sound {a : ClosedTy} {e : Expr [] a} {result : Outcome a}
    (h : Evaluates e result) : e.denote Environment.empty = result.denote :=
  MachineState.Executes.sound h

/-- Returning an outer value or error always contributes information. -/
theorem Outcome.denote_ne_bot {a : ClosedTy} (result : Outcome a) : result.denote ≠ ⊥ := by
  cases result <;> exact WithBot.coe_ne_bot

/-- Bottom cannot be confused with either an error or a returned outer value. -/
theorem not_evaluates_of_denote_bot {a : ClosedTy} {e : Expr [] a}
    (h : e.denote Environment.empty = ⊥) (result : Outcome a) : ¬Evaluates e result := by
  intro heval
  exact result.denote_ne_bot (heval.sound.symm.trans h)

end Interop.Cryptol
