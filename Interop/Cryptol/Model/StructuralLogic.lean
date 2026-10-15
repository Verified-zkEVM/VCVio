/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Aggregate

/-!
# Structural lifting of Cryptol logic

Logic instances carry their structure as evidence. Sequence and product
operations demand the outer operands in source order, even for empty shapes;
function instances delay both demands until application. Products represent
tuple and record spines after checking their source labels and field types.
The preservation equations apply to arbitrary partial operands.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Evidence that a closed core type supports structural Boolean operations. -/
inductive LogicType : ClosedTy → Type where
  | bit : LogicType .bit
  | unit : LogicType .unit
  | seq {a : ClosedTy} (length : Length) (element : LogicType a) : LogicType (.seq length a)
  | prod {a b : ClosedTy} (left : LogicType a) (right : LogicType b) : LogicType (.prod a b)
  | arrow (a : ClosedTy) {b : ClosedTy} (result : LogicType b) : LogicType (.arrow a b)

/-- Lower a structural binary operation into the typed lazy core. -/
@[expose] def LogicType.binary {Γ : List ClosedTy} {a : ClosedTy} (op : BitOp) :
    LogicType a → Expr Γ a → Expr Γ a → Expr Γ a
  | .bit, x, y => .bitOp op x y
  | .unit, x, y => .force x (.force y .unit)
  | .seq n h, x, y => .force x (.force y (.generate n
      (h.binary op (.index x.weaken (.var .zero)) (.index y.weaken (.var .zero)))))
  | .prod h k, x, y => .force x (.force y
      (.pair (h.binary op (.fst x) (.fst y)) (k.binary op (.snd x) (.snd y))))
  | .arrow _ h, x, y => .lam (.force x.weaken (.force y.weaken (h.binary op
      (.app x.weaken (.var .zero)) (.app y.weaken (.var .zero)))))

/-- Direct continuous semantics of structural Boolean operations. -/
@[expose] noncomputable def LogicType.binarySem {a : ClosedTy} (op : BitOp) :
    LogicType a → Computation a →𝒄 (Computation a →𝒄 Computation a)
  | .bit => Semantics.binary (fun x y => .ok (op.eval x y))
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
      DomainResult.valueContinuous (.ofFun (fun z => DomainResult.force x (DomainResult.force y
        (h.binarySem op (DomainResult.applyContinuous x z)
          (DomainResult.applyContinuous y z)))))))

/-- Structural lifting preserves demands, errors, divergence, and successful values. -/
theorem LogicType.denote_binary {Γ : List ClosedTy} {a : ClosedTy} (h : LogicType a)
    (op : BitOp) (x y : Expr Γ a) (ρ : Environment Γ) :
    (h.binary op x y).denote ρ = h.binarySem op (x.denote ρ) (y.denote ρ) := by
  induction h generalizing Γ with
  | bit => rfl
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
      simp only [Expr.denote_force, ih, Expr.denote_app, Expr.denote_weaken, Expr.denote_var]
      rfl

/-- Lower complement; function application remains suspended at nested function results. -/
@[expose] def LogicType.complement {Γ : List ClosedTy} {a : ClosedTy} :
    LogicType a → Expr Γ a → Expr Γ a
  | .bit, x => .bitNot x
  | .unit, x => .force x .unit
  | .seq n h, x => .force x (.generate n
      (h.complement (.index x.weaken (.var .zero))))
  | .prod h k, x => .force x (.pair (h.complement (.fst x)) (k.complement (.snd x)))
  | .arrow _ h, x => .lam (h.complement (.app x.weaken (.var .zero)))

/-- Direct continuous interpretation of structural complement. -/
@[expose] noncomputable def LogicType.complementSem {a : ClosedTy} :
    LogicType a → Computation a →𝒄 Computation a
  | .bit => Semantics.bitNot
  | .unit => .ofFun (fun x => DomainResult.force x (.value ⟨()⟩))
  | .seq n h => .ofFun (fun x => DomainResult.force x (DomainResult.valueContinuous
      (fun i : n.Index => h.complementSem (Semantics.indexAt x (Length.indexNat i)))))
  | .prod h k => .ofFun (fun x => DomainResult.force x (DomainResult.valueContinuous
      (h.complementSem (DomainResult.bind (.ofFun Prod.fst) x),
       k.complementSem (DomainResult.bind (.ofFun Prod.snd) x))))
  | .arrow _ h => .ofFun (fun x => DomainResult.valueContinuous
      (.ofFun (fun z => h.complementSem (DomainResult.applyContinuous x z))))

/-- Complement lowering preserves the meaning of every partial operand. -/
theorem LogicType.denote_complement {Γ : List ClosedTy} {a : ClosedTy} (h : LogicType a)
    (x : Expr Γ a) (ρ : Environment Γ) :
    (h.complement x).denote ρ = h.complementSem (x.denote ρ) := by
  induction h generalizing Γ with
  | bit => rfl
  | unit => rfl
  | seq n h ih =>
      simp only [complement, Expr.denote_force, Expr.denote_generate, ih,
        Expr.denote_index, Expr.denote_weaken, Expr.denote_var]
      rfl
  | prod h k ih ik =>
      simp only [complement, Expr.denote_force, Expr.denote_pair, ih, ik]
      rfl
  | arrow a h ih =>
      apply Expr.denote_lam_eq
      intro z
      simp only [ih, Expr.denote_app, Expr.denote_weaken, Expr.denote_var]
      rfl

end Interop.Cryptol
