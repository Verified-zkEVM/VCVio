/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Binding

/-!
# Public equations for compositional proofs

These equations expose evaluation demands without opening the representation
of partial results or continuous functions. Recursive unfolding is explicit.
-/

public section

namespace Interop.Cryptol

/-- A successful discrete operation returns its complete value. -/
@[simp] theorem ofExcept_ok {α : Type} (x : α) :
    ofExcept (.ok x) = DomainResult.value ⟨x⟩ := rfl

/-- An unsuccessful discrete operation retains its exact error. -/
@[simp] theorem ofExcept_error {α : Type} (e : EvalError) :
    ofExcept (α := α) (.error e) = DomainResult.error e := rfl

end Interop.Cryptol

namespace Interop.Cryptol.Semantics

/-- The integer specialization keeps the model's domain carrier explicit for rewriting. -/
@[simp] theorem intOp_values (op : IntOp) (x y : Int) :
    binary op.eval (.value ⟨x⟩ : Computation .integer) (.value ⟨y⟩) =
      ofExcept (op.eval x y) := rfl

@[simp] theorem intEq_values (x y : Int) :
    binary (fun x y : Int => .ok (x == y))
      (.value ⟨x⟩ : Computation .integer) (.value ⟨y⟩) =
      (.value ⟨x == y⟩ : Computation .bit) := rfl

@[simp] theorem conditional_value {a : ClosedTy} (x y : Computation a) (b : Bool) :
    conditional (x, y) (.value ⟨b⟩) = if b then x else y := by cases b <;> rfl

end Interop.Cryptol.Semantics

namespace Interop.Cryptol.Expr

variable {Γ : List ClosedTy} {a b : ClosedTy} (η : Environment Γ)

@[simp] theorem denote_var (v : Var Γ a) : (Expr.var v).denote η = η a v := rfl

@[simp] theorem denote_bit (b : Bool) : (Expr.bit b).denote η = .value ⟨b⟩ := rfl

@[simp] theorem denote_integer (i : Int) : (Expr.integer i).denote η = .value ⟨i⟩ := rfl

@[simp] theorem denote_error (e : EvalError) :
    (Expr.error e : Expr Γ a).denote η = .error e := rfl

@[simp] theorem denote_force (x : Expr Γ a) (next : Expr Γ b) :
    (Expr.force x next).denote η = DomainResult.force (x.denote η) (next.denote η) := rfl

@[simp] theorem denote_letE (x : Expr Γ a) (body : Expr (a :: Γ) b) :
    (Expr.letE x body).denote η = body.denote (η.extend (x.denote η)) := rfl

@[simp] theorem denote_app (f : Expr Γ (.arrow a b)) (x : Expr Γ a) :
    (Expr.app f x).denote η = DomainResult.applyContinuous (f.denote η) (x.denote η) := rfl

/-- A function equation is proved on arbitrary suspended arguments. -/
theorem denote_lam_eq (body : Expr (a :: Γ) b)
    (f : Computation a →𝒄 Computation b)
    (h : ∀ x, body.denote (η.extend x) = f x) :
    (Expr.lam body).denote η = .value f := by
  apply congrArg DomainResult.value
  change body.bodyDenote η = f
  apply DFunLike.ext
  intro x
  exact h x

@[simp] theorem denote_pair (x : Expr Γ a) (y : Expr Γ b) :
    (Expr.pair x y).denote η = .value (x.denote η, y.denote η) := rfl

@[simp] theorem denote_generate {l : Length} (body : Expr (.integer :: Γ) a) :
    (Expr.generate l body).denote η = .value (fun i : l.Index =>
      body.denote (η.extend (.value ⟨(Length.indexNat i : Int)⟩))) := rfl

@[simp] theorem denote_index {l : Length} (xs : Expr Γ (.seq l a)) (i : Expr Γ .integer) :
    (Expr.index xs i).denote η = Semantics.index (xs.denote η) (i.denote η) := rfl

@[simp] theorem denote_ite (p : Expr Γ .bit) (x y : Expr Γ a) :
    (Expr.ite p x y).denote η = Semantics.conditional (x.denote η, y.denote η)
      (p.denote η) := rfl

@[simp] theorem denote_intOp (op : IntOp) (x y : Expr Γ .integer) :
    (Expr.intOp op x y).denote η = Semantics.binary op.eval (x.denote η) (y.denote η) := rfl

@[simp] theorem denote_intEq (x y : Expr Γ .integer) :
    (Expr.intEq x y).denote η = Semantics.binary (fun x y : Int => .ok (x == y))
      (x.denote η) (y.denote η) := rfl

@[simp] theorem denote_intLt (x y : Expr Γ .integer) :
    (Expr.intLt x y).denote η = Semantics.binary (fun x y : Int => .ok (decide (x < y)))
      (x.denote η) (y.denote η) := rfl

/-- Equality of meanings under all environments is a congruence boundary. -/
def SemEq (x y : Expr Γ a) : Prop := ∀ η, x.denote η = y.denote η

theorem SemEq.refl (x : Expr Γ a) : SemEq x x := fun _ => rfl

theorem SemEq.symm {x y : Expr Γ a} (h : SemEq x y) : SemEq y x := fun η => (h η).symm

theorem SemEq.trans {x y z : Expr Γ a} (h : SemEq x y) (h' : SemEq y z) :
    SemEq x z := fun η => (h η).trans (h' η)

end Interop.Cryptol.Expr
