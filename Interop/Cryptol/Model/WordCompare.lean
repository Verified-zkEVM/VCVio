/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.WordSemantics

/-!
# Lexicographic comparisons of partial words

Comparison demands both outer words, then visits bits from most significant
to least significant. A first differing bit determines the answer without
demanding the remaining suffix. This demand rule differs from converting
both complete words to integers before comparison.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- The six Cryptol comparison predicates on an ordering result. -/
inductive CompareOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Accept the specified ordering outcomes. -/
@[expose] def CompareOp.accept : CompareOp → Ordering → Bool
  | .eq, o => o == .eq
  | .ne, o => o != .eq
  | .lt, o => o == .lt
  | .le, o => o != .gt
  | .gt, o => o == .gt
  | .ge, o => o != .lt

namespace Semantics

/-- A lexicographic comparison step, with a suspended suffix result. -/
@[expose] noncomputable def compareStep (op : CompareOp) : Computation .bit →𝒄
    (Computation .bit →𝒄 (Computation .bit →𝒄 Computation .bit)) :=
  .ofFun (fun tail => .ofFun (fun x => .ofFun (fun y =>
    DomainResult.bind (DiscreteOrder.continuousMap (fun o : Ordering =>
      if o = .eq then tail else DomainResult.value ⟨op.accept o⟩))
      (binary (fun a b : Bool => .ok (compare a b)) x y))))

/-- Core conditionals implement the same demand order as a lexicographic step. -/
theorem compareStep_eq (op : CompareOp) (tail x y : Computation .bit) :
    conditional (conditional (a := .bit) (.value ⟨op.accept .gt⟩, .value ⟨op.accept .lt⟩) x, tail)
      (binary (fun a b => .ok (BitOp.xor.eval a b)) x y) = compareStep op tail x y := by
  induction x using DomainResult.inductionOn with
  | bot => rfl
  | error e => rfl
  | value x =>
      obtain ⟨x⟩ := x
      induction y using DomainResult.inductionOn with
      | bot => rfl
      | error e => rfl
      | value y =>
          obtain ⟨y⟩ := y
          cases x <;> cases y <;> rfl

/-- Compare a list of positions in order, stopping at its first unequal bit. -/
@[expose] noncomputable def compareBits (op : CompareOp) (n : Nat) : List (Fin n) →
    Computation (wordTy n) →𝒄 (Computation (wordTy n) →𝒄 Computation .bit)
  | [] => .const (.const (.value ⟨op.accept .eq⟩))
  | i :: is => .ofFun (fun x => .ofFun (fun y =>
      compareStep op (compareBits op n is x y) (indexAt x i.val) (indexAt y i.val)))

/-- Direct reference word comparison, including outer demands at width zero. -/
@[expose] noncomputable def wordCompare (op : CompareOp) (n : Nat) :
    Computation (wordTy n) →𝒄 (Computation (wordTy n) →𝒄 Computation .bit) :=
  .ofFun (fun x => .ofFun (fun y => DomainResult.force x (DomainResult.force y
    (compareBits op n (List.finRange n) x y))))

end Semantics

namespace Expr

variable {Γ : List ClosedTy} {n : Nat}

/-- Finite core expansion of a prefix-sensitive comparison. -/
@[expose] def compareBits (op : CompareOp) (x y : Expr Γ (wordTy n)) :
    List (Fin n) → Expr Γ .bit
  | [] => .bit (op.accept .eq)
  | i :: is => .ite (.bitOp .xor (.index x (.integer i.val)) (.index y (.integer i.val)))
      (.ite (.index x (.integer i.val)) (.bit (op.accept .gt)) (.bit (op.accept .lt)))
      (compareBits op x y is)

/-- Comparison first demands the outer operands in left-to-right order. -/
@[expose] def wordCompare (op : CompareOp) (x y : Expr Γ (wordTy n)) : Expr Γ .bit :=
  .force x (.force y (compareBits op x y (List.finRange n)))

theorem denote_compareBits (op : CompareOp) (x y : Expr Γ (wordTy n))
    (is : List (Fin n)) (η : Environment Γ) :
    (compareBits op x y is).denote η = Semantics.compareBits op n is (x.denote η) (y.denote η) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      change Semantics.conditional (Semantics.conditional (a := .bit)
        (.value ⟨op.accept .gt⟩, .value ⟨op.accept .lt⟩)
          (Semantics.indexAt (x.denote η) i.val), (compareBits op x y is).denote η) _ = _
      rw [ih]
      exact Semantics.compareStep_eq _ _ _ _

/-- Lowering preserves comparison on arbitrary partial words. -/
theorem denote_wordCompare (op : CompareOp) (x y : Expr Γ (wordTy n)) (η : Environment Γ) :
    (wordCompare op x y).denote η = Semantics.wordCompare op n (x.denote η) (y.denote η) := by
  change DomainResult.force (x.denote η) (DomainResult.force (y.denote η) _) = _
  rw [denote_compareBits]
  rfl

end Expr

end Interop.Cryptol
