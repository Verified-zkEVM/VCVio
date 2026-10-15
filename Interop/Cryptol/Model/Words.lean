/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Combinators
public import Interop.Cryptol.Model.Adequacy

/-!
# Word literal correctness

The semantic sequence corresponding to a Lean bitvector uses `getMsbD`.
The compiler for finite word descriptions preserves every bit at every width,
including zero. Arithmetic and permutation macros expand into the same core;
their executable boundary cases are checked by the differential corpus.
-/

public section

namespace Interop.Cryptol

/-- Selecting an in-range suspended list element preserves its meaning. -/
theorem Expr.denote_select {Γ : List ClosedTy} {a : ClosedTy} (xs : List (Expr Γ a))
    (η : Environment Γ) (j : Nat) (hj : j < xs.length) (i : Expr Γ .integer)
    (hi : i.denote η = .value ⟨(j : Int)⟩) :
    (Expr.select xs i).denote η = xs[j].denote η := by
  induction xs generalizing j i with
  | nil => simp at hj
  | cons x xs ih =>
      cases j with
      | zero =>
          change Semantics.conditional _ (Semantics.binary
            (fun a b : Int => .ok (a == b)) (i.denote η) (.value ⟨0⟩)) = x.denote η
          rw [hi]
          rfl
      | succ j =>
          have hj' : j < xs.length := by simpa using hj
          change Semantics.conditional _ (Semantics.binary
            (fun a b : Int => .ok (a == b)) (i.denote η) (.value ⟨0⟩)) = xs[j].denote η
          rw [hi, Semantics.binary_values]
          have hz : (((j + 1 : Nat) : Int) == 0) = false := by
            simp only [beq_eq_false_iff_ne]
            omega
          simp only [ofExcept, hz]
          change (Expr.select xs (.intOp .sub i (.integer 1))).denote η = _
          apply ih j hj'
          change Semantics.binary IntOp.sub.eval (i.denote η) (.value ⟨1⟩) = _
          rw [hi, Semantics.binary_values]
          simp [IntOp.eval, ofExcept]

/-- Interpret a bitvector as a fully defined, big-endian lazy sequence. -/
@[expose] def wordValue {n : Nat} (bits : BitVec n) : Value (.seq (.finite n) .bit) :=
  fun i : Fin n => .value ⟨bits.getMsbD i.val⟩

/-- Word literal compilation preserves every bit at every finite width. -/
theorem Expr.denote_word {Γ : List ClosedTy} {n : Nat} (bits : BitVec n)
    (η : Environment Γ) : (Expr.word bits : Expr Γ (.seq (.finite n) .bit)).denote η =
      .value (wordValue bits) := by
  apply congrArg DomainResult.value
  funext i
  change (Expr.select ((List.finRange n).map fun j => Expr.bit (bits.getMsbD j.val))
    (.var .zero)).denote (η.extend (.value ⟨(i.val : Int)⟩)) = _
  rw [Expr.denote_select _ _ i.val (by simp) _ rfl]
  simp [wordValue, Expr.denote]

/-- Fully defined words are represented injectively in the sequence domain. -/
theorem wordValue_injective {n : Nat} : Function.Injective (@wordValue n) := by
  intro x y h
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have he := congrFun h (⟨i, hi⟩ : Fin n)
  exact DiscreteOrder.mk.inj (Sum.inr.inj (WithBot.coe_inj.mp he))

end Interop.Cryptol
