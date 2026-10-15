/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Operational

/-!
# Bounded execution diagnostics

Syntax nodes and call-by-name machine transitions are diagnostic counts, not
Cryptol implementation costs. A stopped run retains its exact residual state.
-/

public section

namespace Interop.Cryptol

/-- Count constructors in a finite syntax tree, excluding literal payload sizes. -/
@[expose] def Expr.nodeCount {N V : Type} {Γ : List (Ty N V)} {a : Ty N V} : Expr Γ a → Nat
  | .var _ | .bit _ | .integer _ | .unit | .error _ => 1
  | .lam e => 1 + e.nodeCount
  | .app f x => 1 + f.nodeCount + x.nodeCount
  | .letE x e => 1 + x.nodeCount + e.nodeCount
  | .force x e => 1 + x.nodeCount + e.nodeCount
  | .pair x y => 1 + x.nodeCount + y.nodeCount
  | .fst x => 1 + x.nodeCount
  | .snd x => 1 + x.nodeCount
  | .generate _ e => 1 + e.nodeCount
  | .index x i => 1 + x.nodeCount + i.nodeCount
  | .ite p x y => 1 + p.nodeCount + x.nodeCount + y.nodeCount
  | .fix e => 1 + e.nodeCount
  | .bitNot x => 1 + x.nodeCount
  | .bitOp _ x y => 1 + x.nodeCount + y.nodeCount
  | .intOp _ x y => 1 + x.nodeCount + y.nodeCount
  | .intEq x y => 1 + x.nodeCount + y.nodeCount
  | .intLt x y => 1 + x.nodeCount + y.nodeCount

/-- Run a bounded chunk, counting transitions from `count`, including the final outcome step. -/
@[expose] def MachineState.runCounted {a : ClosedTy} (fuel : Nat) (state : MachineState a)
    (count : Nat := 0) : Nat × (Outcome a ⊕ MachineState a) :=
  match fuel with
  | 0 => (count, .inr state)
  | fuel + 1 => match state.step with
      | .inl result => (count + 1, .inl result)
      | .inr next => runCounted fuel next (count + 1)

/-- Diagnostic counting does not change the original runner's result or residual. -/
theorem MachineState.runCounted_snd {a : ClosedTy} (fuel : Nat) (state : MachineState a)
    (count : Nat := 0) :
    (runCounted fuel state count).2 = state.run fuel := by
  induction fuel generalizing state count with
  | zero => rfl
  | succ fuel ih =>
      simp only [runCounted, run, Control.Transition.run]
      cases state.step with
      | inl result => rfl
      | inr next => exact ih next (count + 1)

end Interop.Cryptol
