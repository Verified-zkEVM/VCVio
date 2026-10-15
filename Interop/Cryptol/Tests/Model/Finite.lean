/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Contracts
public import Interop.Cryptol.Model.Inspect

/-!
# Ordinary-import finite-fragment and partial-word regressions

The tests exercise higher-order lowering, quantified contract transfer,
zero-width outer errors, partial words and diagnostic residual preservation.
-/

public section

open Interop.Cryptol Interop.Cryptol.Finite

example (k : Nat) (err : EvalError) :
    (Expr.rotateRight k (.error err) : ClosedExpr [] (.seq (.finite 0) .bit)).denote
      Environment.empty = .error err := by
  rw [Expr.rotateRight_zero]
  rfl

example (k : Nat) :
    (MachineState.eval (Expr.rotateLeft k (.error (.user "empty")) :
      ClosedExpr [] (.seq (.finite 0) .bit)) .done).run 3 =
      .inl (.error (.user "empty")) := by
  simp only [Expr.rotateLeft_zero]
  rfl

/-- A word with a defined first bit and an erroneous second bit. -/
@[expose] def partialWord : ClosedExpr [] (.seq (.finite 2) .bit) :=
  .generate (Length.finite 2) (.ite (.intEq (.var .zero) (.integer 0))
    (.bit true) (.error (.user "second bit")))

example : (MachineState.eval
    (Expr.index (.rotateRight 1 partialWord) (.integer 1)) .done).run 100 =
      .inl (.ok (.bit true)) := rfl

example : (MachineState.eval
    (Expr.index (.rotateRight 1 partialWord) (.integer 0)) .done).run 100 =
      .inl (.error (.user "second bit")) := rfl

-- The reference evaluator also returns this bit; Cryptol's normal evaluator
-- instead forces the erroneous word tail of its native concatenation.
example : (MachineState.eval (Expr.index
    (Expr.append (.list [.bit true])
      (.error (.user "tail") : ClosedExpr [] (.seq (.finite 7) .bit)))
    (.integer 0)) .done).run 100 = .inl (.ok (.bit true)) := rfl

/-- A higher-order function binds a word transformer and applies it twice. -/
@[expose] def twice : Term []
    (.arrow (.arrow (.word 8) (.word 8)) (.arrow (.word 8) (.word 8))) :=
  .lam (.lam (.app (.var (.succ .zero)) (.app (.var (.succ .zero)) (.var .zero))))

example (x : BitVec 8) :
    (Term.app twice (.lam (.wordNot (.var .zero)))).evalWord x = x := by
  change ~~~(~~~x) = x
  simp

example (x : BitVec 8) :
    (Expr.app (Term.app twice (.lam (.wordNot (.var .zero)))).lower (.word x)).denote
      Environment.empty = .value (wordValue x) := by
  rw [Term.denote_apply_word]
  change DomainResult.value (wordValue (~~~(~~~x))) = _
  simp

example {n m : Nat} (f : Term [] (.arrow (.word n) (.word m)))
    (pre : BitVec n → Prop) (post : BitVec n → BitVec m → Prop) :
    TotalContract f.lower pre post ↔ ∀ x, pre x → post x (f.evalWord x) :=
  f.totalContract_iff f.evalWord (fun _ => rfl) pre post

example {a : ClosedTy} (fuel count : Nat) (state : MachineState a) :
    (state.runCounted fuel count).2 = state.run fuel := by
  exact state.runCounted_snd fuel count
