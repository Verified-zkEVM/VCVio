/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Aggregate

/-!
# Structural lifting of Cryptol ring operations

Integer and finite-word arithmetic are the leaves of structural ring instances.
Sequences, tuple/record spines, and function codomains lift these operations.
Division and remainder are deliberately absent: Cryptol's `Integral` class has
no structural aggregate instances. Finite words wrap at their declared width.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- The binary operations belonging to Cryptol's Ring class. -/
inductive RingOp where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- Ring operators use the corresponding integer operation at scalar leaves. -/
@[expose] def RingOp.integer : RingOp → IntOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- Structural evidence for a closed Ring instance. -/
inductive RingType : ClosedTy → Type where
  | integer : RingType .integer
  | word (width : Nat) : RingType (wordTy width)
  | unit : RingType .unit
  | seq {a : ClosedTy} (length : Length) (element : RingType a) : RingType (.seq length a)
  | prod {a b : ClosedTy} (left : RingType a) (right : RingType b) : RingType (.prod a b)
  | arrow (a : ClosedTy) {b : ClosedTy} (result : RingType b) : RingType (.arrow a b)

/-- Lower a ring operation using the checked instance structure. -/
@[expose] def RingType.binary {Γ : List ClosedTy} {a : ClosedTy} (op : RingOp) :
    RingType a → Expr Γ a → Expr Γ a → Expr Γ a
  | .integer, x, y => .intOp op.integer x y
  | .word _, x, y => .wordOp op.integer x y
  | .unit, x, y => .force x (.force y .unit)
  | .seq n h, x, y => .force x (.force y (.generate n
      (h.binary op (.index x.weaken (.var .zero)) (.index y.weaken (.var .zero)))))
  | .prod h k, x, y => .force x (.force y
      (.pair (h.binary op (.fst x) (.fst y)) (k.binary op (.snd x) (.snd y))))
  | .arrow _ h, x, y => .lam (h.binary op
      (.app x.weaken (.var .zero)) (.app y.weaken (.var .zero)))

/-- Direct reference semantics, with lazy element operations and delayed functions. -/
@[expose] noncomputable def RingType.binarySem {a : ClosedTy} (op : RingOp) :
    RingType a → Computation a →𝒄 (Computation a →𝒄 Computation a)
  | .integer => Semantics.binary op.integer.eval
  | .word n => Semantics.wordArithmetic n op.integer
  | .unit => .ofFun (fun x => .ofFun (fun y =>
      DomainResult.force x (DomainResult.force y (.value ⟨()⟩))))
  | .seq n h => .ofFun (fun x => .ofFun (fun y =>
      DomainResult.force x (DomainResult.force y (DomainResult.valueContinuous
        (fun i : n.Index => h.binarySem op
          (Semantics.indexAt x (Length.indexNat i))
          (Semantics.indexAt y (Length.indexNat i)))))))
  | .prod h k => .ofFun (fun x => .ofFun (fun y =>
      DomainResult.force x (DomainResult.force y (DomainResult.valueContinuous
        (h.binarySem op (DomainResult.bind (.ofFun Prod.fst) x)
          (DomainResult.bind (.ofFun Prod.fst) y),
         k.binarySem op (DomainResult.bind (.ofFun Prod.snd) x)
          (DomainResult.bind (.ofFun Prod.snd) y))))))
  | .arrow _ h => .ofFun (fun x => .ofFun (fun y =>
      DomainResult.valueContinuous (.ofFun (fun z =>
        h.binarySem op (DomainResult.applyContinuous x z)
          (DomainResult.applyContinuous y z)))))

/-- Structural ring lowering preserves the denotation of arbitrary partial operands. -/
theorem RingType.denote_binary {Γ : List ClosedTy} {a : ClosedTy} (h : RingType a)
    (op : RingOp) (x y : Expr Γ a) (ρ : Environment Γ) :
    (h.binary op x y).denote ρ = h.binarySem op (x.denote ρ) (y.denote ρ) := by
  induction h generalizing Γ with
  | integer => rfl
  | word n => exact Expr.denote_wordArithmetic_sem op.integer x y ρ
  | unit => rfl
  | seq n h ih =>
      simp only [binary, Expr.denote_force, Expr.denote_generate, ih,
        Expr.denote_index, Expr.denote_weaken, Expr.denote_var]
      rfl
  | prod h k ih ik =>
      simp only [binary, Expr.denote_force, Expr.denote_pair, ih, ik]
      rfl
  | arrow a h ih =>
      apply Expr.denote_lam_eq
      intro z
      simp only [ih, Expr.denote_app, Expr.denote_weaken, Expr.denote_var]
      rfl

end Interop.Cryptol
