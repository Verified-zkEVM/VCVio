/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Domain
public import Interop.Cryptol.Model.Primitives

/-!
# Compositional domain semantics

Every expression denotes a continuous function of its environment. Recursive
bindings use the least fixed point in their result domain. This definition
does not run the abstract machine or take a supremum over its execution fuel.
Integer division follows Cryptol's truncation toward zero.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Interpret a total primitive result in its lifted discrete domain. -/
@[expose] def ofExcept {α : Type} : Except EvalError α → DomainResult EvalError (DiscreteOrder α)
  | .ok x => .value ⟨x⟩
  | .error e => .error e

namespace Semantics

/-- Strictly lift a binary operation on discrete values. -/
@[expose] noncomputable def binary {α β γ : Type} (f : α → β → Except EvalError γ) :
    DomainResult EvalError (DiscreteOrder α) →𝒄
      (DomainResult EvalError (DiscreteOrder β) →𝒄
        DomainResult EvalError (DiscreteOrder γ)) :=
  DomainResult.bind₂ (DiscreteOrder.continuousMap fun a =>
    DiscreteOrder.continuousMap fun b => ofExcept (f a b))

/-- Demand the condition and only the chosen branch. -/
@[expose] noncomputable def conditional {a : ClosedTy} :
    (Computation a × Computation a) →𝒄 (Computation .bit →𝒄 Computation a) :=
  DomainResult.bindContinuous.comp
    ((DiscreteOrder.continuousMap fun b : Bool =>
      if b then (ContinuousHom.ofFun Prod.fst :
        (Computation a × Computation a) →𝒄 Computation a)
      else ContinuousHom.ofFun Prod.snd).swapArgs)

/-- Select one element after demanding the sequence constructor and the
index, with explicit checks for negative and out-of-bounds indices. -/
@[expose] noncomputable def index {l : Length} {a : ClosedTy} :
    Computation (.seq l a) →𝒄 (Computation .integer →𝒄 Computation a) :=
  DomainResult.bind₂ ((DiscreteOrder.continuousMap fun i : Int =>
    match l.checkIndex i with
    | none => ContinuousHom.const (DomainResult.error (EvalError.invalidIndex i))
    | some j => ContinuousHom.ofFun (fun xs : Value (.seq l a) => xs j)).swapArgs)

@[simp] theorem binary_values {α β γ : Type} (f : α → β → Except EvalError γ) (a : α) (b : β) :
    binary f (.value ⟨a⟩) (.value ⟨b⟩) = ofExcept (f a b) := rfl

/-- Case analysis on a demanded bit is a strict bind with a discrete branch selector. -/
theorem conditional_eq_bind {a : ClosedTy} (x y : Computation a) (p : Computation .bit) :
    conditional (x, y) p = DomainResult.bind
      (DiscreteOrder.continuousMap (fun b : Bool => if b then x else y)) p := by
  apply congrArg (fun f : Value .bit →𝒄 Computation a => DomainResult.bind f p)
  ext b
  obtain ⟨b⟩ := b
  cases b <;> rfl

/-- Once the sequence constructor is available, indexing demands only the index
and the selected element. -/
theorem index_value_eq_bind {l : Length} {a : ClosedTy} (xs : Value (.seq l a))
    (i : Computation .integer) : index (.value xs) i = DomainResult.bind
      (DiscreteOrder.continuousMap (fun n : Int => match l.checkIndex n with
        | none => .error (.invalidIndex n)
        | some j => xs j)) i := by
  apply congrArg (fun f : Value .integer →𝒄 Computation a => DomainResult.bind f i)
  ext n
  change (match l.checkIndex n.value with
    | none => ContinuousHom.const (DomainResult.error (EvalError.invalidIndex n.value))
    | some j => ContinuousHom.ofFun (fun ys : Value (.seq l a) => ys j)) xs = _
  change _ = (match l.checkIndex n.value with
    | none => DomainResult.error (EvalError.invalidIndex n.value)
    | some j => xs j)
  cases l.checkIndex n.value <;> rfl

@[simp] theorem index_values {l : Length} {a : ClosedTy} (xs : Value (.seq l a)) (i : Int) :
    index (.value xs) (.value ⟨i⟩) = match l.checkIndex i with
      | none => .error (.invalidIndex i)
      | some j => xs j := by
  change (match l.checkIndex i with
    | none => ContinuousHom.const (DomainResult.error (EvalError.invalidIndex i))
    | some j => ContinuousHom.ofFun (fun ys : Value (.seq l a) => ys j)) xs = _
  cases l.checkIndex i <;> rfl

end Semantics

/-- Compositional semantics of the typed core. -/
@[expose] noncomputable def Expr.denote {Γ : List ClosedTy} {a : ClosedTy} :
    Expr Γ a → Environment Γ →𝒄 Computation a
  | .var x => .ofFun (fun ρ => ρ _ x)
  | .bit x => .const (.value ⟨x⟩)
  | .integer x => .const (.value ⟨x⟩)
  | .unit => .const (.value ⟨()⟩)
  | .error e => .const (.error e)
  | .lam e => DomainResult.valueContinuous.comp
      (ContinuousHom.curry (e.denote.comp Environment.extendContinuous))
  | .app f x => .ofFun (fun ρ => DomainResult.applyContinuous (f.denote ρ) (x.denote ρ))
  | .letE x e => .ofFun (fun ρ =>
      e.denote (Environment.extendContinuous (ρ, x.denote ρ)))
  | .force x e => .ofFun (fun ρ => DomainResult.force (x.denote ρ) (e.denote ρ))
  | .pair x y => .ofFun (fun ρ => DomainResult.valueContinuous (x.denote ρ, y.denote ρ))
  | .fst x => (DomainResult.bind (.ofFun Prod.fst)).comp x.denote
  | .snd x => (DomainResult.bind (.ofFun Prod.snd)).comp x.denote
  | .generate l e => .ofFun (fun ρ => DomainResult.valueContinuous (fun i : l.Index =>
      e.denote (Environment.extendContinuous
        (ρ, DomainResult.value ⟨(Length.indexNat i : Int)⟩))))
  | .index xs i => .ofFun (fun ρ => Semantics.index (xs.denote ρ) (i.denote ρ))
  | .ite p x y => .ofFun (fun ρ =>
      Semantics.conditional (x.denote ρ, y.denote ρ) (p.denote ρ))
  | .fix e => ContinuousHom.fixContinuous.comp
      (ContinuousHom.curry (e.denote.comp Environment.extendContinuous))
  | .bitNot x => (DomainResult.bind (DiscreteOrder.continuousMap
      (fun b : Bool => DomainResult.value ⟨!b⟩))).comp x.denote
  | .bitOp op x y => .ofFun (fun ρ =>
      Semantics.binary (fun a b => .ok (op.eval a b)) (x.denote ρ) (y.denote ρ))
  | .intOp op x y => .ofFun (fun ρ => Semantics.binary op.eval (x.denote ρ) (y.denote ρ))
  | .intEq x y => .ofFun (fun ρ =>
      Semantics.binary (fun a b : Int => .ok (a == b)) (x.denote ρ) (y.denote ρ))
  | .intLt x y => .ofFun (fun ρ =>
      Semantics.binary (fun a b : Int => .ok (decide (a < b))) (x.denote ρ) (y.denote ρ))

end Interop.Cryptol
