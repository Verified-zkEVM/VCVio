/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Operational

/-!
# Finite execution proofs

Inductive executions coincide with successful finite machine chunks. The
stack composition rule lets proofs evaluate a demanded subexpression and
then resume its caller. Fuel exhaustion remains a residual configuration.
-/

public section

namespace Interop.Cryptol

namespace Stack

/-- Place another stack after the current continuation. -/
@[expose] def append {a b c : ClosedTy} : Stack a b → Stack b c → Stack a c
  | .done, rest => rest
  | .push frame more, rest => .push frame (more.append rest)

end Stack

namespace MachineState

/-- Attach a caller to a whole machine state. -/
@[expose] def attach {a b : ClosedTy} : MachineState a → Stack a b → MachineState b
  | .eval e stack, rest => .eval e (stack.append rest)
  | .value v stack, rest => .value v (stack.append rest)
  | .error e, _ => .error e

/-- Deliver a completed subcomputation to its caller. -/
@[expose] def deliver {a b : ClosedTy} : Outcome a → Stack a b → MachineState b
  | .ok v, stack => .value v stack
  | .error e, _ => .error e

/-- Attach a caller before or after resuming a frame. -/
theorem attach_resume {a b c r : ClosedTy} (frame : Frame a b) (v : RuntimeValue a)
    (stack : Stack b c) (rest : Stack c r) :
    (resume frame v stack).attach rest = resume frame v (stack.append rest) := by
  cases frame <;> cases v <;> simp only [resume] <;> try rfl
  all_goals split <;> rfl

/-- One-step execution commutes with adding a caller. -/
theorem step_attach {a b : ClosedTy} (state : MachineState a) (rest : Stack a b) :
    (state.attach rest).step = match state.step with
      | .inl result => (deliver result rest).step
      | .inr next => .inr (next.attach rest) := by
  cases state with
  | error e => rfl
  | value v stack =>
      cases stack with
      | done => rfl
      | push frame more =>
          change .inr (resume frame v (more.append rest)) =
            Sum.inr ((resume frame v more).attach rest)
          rw [attach_resume]
  | eval e stack =>
      cases e <;> try rfl
      case var v => cases v

/-- A finite derivation of a terminating execution. -/
abbrev Executes {r : ClosedTy} : MachineState r → Outcome r → Prop :=
  Control.Transition.Executes step

/-- Inductive execution and successful finite chunks describe the same runs. -/
theorem executes_iff_terminates {r : ClosedTy} (state : MachineState r) (result : Outcome r) :
    Executes state result ↔ state.Terminates result :=
  Control.Transition.executes_iff_terminates step state result

/-- A deterministic transition function admits at most one terminating result. -/
theorem Executes.unique {r : ClosedTy} {state : MachineState r} {left right : Outcome r}
    (hl : Executes state left) (hr : Executes state right) : left = right :=
  Control.Transition.Executes.unique step hl hr

/-- States with the same next transition have the same terminating outcomes. -/
theorem Executes.of_step_eq {r : ClosedTy} {state state' : MachineState r} {result : Outcome r}
    (h : state.step = state'.step) (hr : Executes state' result) : Executes state result :=
  Control.Transition.Executes.of_step_eq step h hr

/-- Run a subcomputation and then resume its caller. -/
theorem Executes.attach {a b : ClosedTy} {state : MachineState a} {result : Outcome a}
    (h : Executes state result) (rest : Stack a b) {out : Outcome b}
    (hk : Executes (deliver result rest) out) : Executes (state.attach rest) out := by
  induction h with
  | done hs => exact hk.of_step_eq (by rw [step_attach, hs])
  | next hs _ ih => exact .next (by rw [step_attach, hs]) (ih hk)

end MachineState

/-- Term evaluation is the initial machine state's finite execution relation. -/
abbrev Evaluates {a : ClosedTy} (e : Expr [] a) (result : Outcome a) : Prop :=
  MachineState.Executes e.start result

end Interop.Cryptol
