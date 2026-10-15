/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Resolved

/-!
# Equations for resolved syntax

Consumer proofs can normalize source bindings and primitive applications using
ordinary imports, without unfolding the indexed tree or continuous-map carriers.
-/

public section

namespace Interop.Cryptol.Resolved

open OmegaCompletePartialOrder

variable {Γ : List ClosedTy} {a b : ClosedTy}

@[simp] theorem denote_var (v : Var Γ a) (ρ : Environment Γ) :
    denote (Term.var v) ρ = ρ a v := rfl

@[simp] theorem denote_integer (i : Int) (ρ : Environment Γ) :
    denote (Term.integer i) ρ = .value ⟨i⟩ := rfl

@[simp] theorem denote_bit (b : Bool) (ρ : Environment Γ) :
    denote (Term.bit b) ρ = .value ⟨b⟩ := rfl

@[simp] theorem denote_primitive (p : Primitive a) (ρ : Environment Γ) :
    denote (Term.primitive p) ρ = p.denote := rfl

@[simp] theorem denote_word {n : Nat} (x : BitVec n) (ρ : Environment Γ) :
    denote (Term.word x) ρ = .value (wordValue x) := rfl

@[simp] theorem denote_app (f : Term Γ (.arrow a b)) (x : Term Γ a) (ρ : Environment Γ) :
    denote (Term.app f x) ρ = DomainResult.applyContinuous (denote f ρ) (denote x ρ) := rfl

@[simp] theorem denote_lam_apply (body : Term (a :: Γ) b) (x : Computation a)
    (ρ : Environment Γ) :
    DomainResult.applyContinuous (denote (Term.lam body) ρ) x =
      denote body (ρ.extend x) := rfl

/-- A lambda returns a continuous map on suspended arguments. -/
theorem denote_lam (body : Term (a :: Γ) b) (ρ : Environment Γ) :
    denote (Term.lam body) ρ = .value (.ofFun (fun x =>
      denote body (Environment.extendContinuous (ρ, x)))) := rfl

/-- Recursion is the least fixed point of the body in the extended environment. -/
theorem denote_fix (body : Term (a :: Γ) a) (ρ : Environment Γ) :
    denote (Term.fix body) ρ = (ContinuousHom.ofFun (fun x =>
      denote body (Environment.extendContinuous (ρ, x)))).fix := rfl

@[simp] theorem denote_letE (x : Term Γ a) (body : Term (a :: Γ) b) (ρ : Environment Γ) :
    denote (Term.letE x body) ρ = denote body (ρ.extend (denote x ρ)) := rfl

@[simp] theorem denote_sequence (n : Nat) (xs : Fin n → Term Γ a) (ρ : Environment Γ) :
    denote (Term.sequence n xs) ρ = .value (fun i => denote (xs i) ρ) := rfl

@[simp] theorem denote_generate (l : Length) (body : Term (.integer :: Γ) a)
    (ρ : Environment Γ) :
    denote (Term.generate l body) ρ = .value (fun i : l.Index =>
      denote body (ρ.extend (.value ⟨(Length.indexNat i : Int)⟩))) := rfl

@[simp] theorem denote_index {l : Length} (xs : Term Γ (.seq l a)) (i : Term Γ .integer)
    (ρ : Environment Γ) :
    denote (Term.index xs i) ρ = Semantics.index (denote xs ρ) (denote i ρ) := rfl

@[simp] theorem denote_ite (p : Term Γ .bit) (x y : Term Γ a) (ρ : Environment Γ) :
    denote (Term.ite p x y) ρ = Semantics.conditional (denote x ρ, denote y ρ)
      (denote p ρ) := rfl

@[simp] theorem denote_pair (x : Term Γ a) (y : Term Γ b) (ρ : Environment Γ) :
    denote (Term.pair x y) ρ = .value (denote x ρ, denote y ρ) := rfl

@[simp] theorem denote_fst (x : Term Γ (.prod a b)) (ρ : Environment Γ) :
    denote (Term.fst x) ρ = DomainResult.bind (.ofFun Prod.fst) (denote x ρ) := rfl

@[simp] theorem denote_snd (x : Term Γ (.prod a b)) (ρ : Environment Γ) :
    denote (Term.snd x) ρ = DomainResult.bind (.ofFun Prod.snd) (denote x ρ) := rfl

@[simp] theorem denote_wordArithmetic {n : Nat} (op : IntOp)
    (x y : Term Γ (wordTy n)) (ρ : Environment Γ) :
    denote (Term.wordArithmetic op x y) ρ =
      Semantics.wordArithmetic n op (denote x ρ) (denote y ρ) := rfl

@[simp] theorem denote_wordLogic {n : Nat} (op : BitOp)
    (x y : Term Γ (wordTy n)) (ρ : Environment Γ) :
    denote (Term.wordLogic op x y) ρ =
      Semantics.wordLogic n op (denote x ρ) (denote y ρ) := rfl

@[simp] theorem denote_shift {n : Nat} (op : ShiftOp)
    (x : Term Γ (wordTy n)) (i : Term Γ .integer) (ρ : Environment Γ) :
    denote (Term.shift op x i) ρ = Semantics.shift op n (denote x ρ) (denote i ρ) := rfl

@[simp] theorem denote_intOp (op : IntOp) (x y : Term Γ .integer) (ρ : Environment Γ) :
    denote (Term.intOp op x y) ρ = Semantics.binary op.eval (denote x ρ) (denote y ρ) := rfl

/-- Specify a source lambda using its body equation on arbitrary suspended arguments. -/
theorem denote_lam_eq (body : Term (a :: Γ) b) (ρ : Environment Γ)
    (f : Computation a →𝒄 Computation b)
    (h : ∀ x, denote body (ρ.extend x) = f x) :
    denote (Term.lam body) ρ = DomainResult.value f := by
  rw [denote_lam]
  apply congrArg DomainResult.value
  change (_ : Computation a →𝒄 Computation b) = f
  apply DFunLike.ext
  intro x
  exact h x

end Interop.Cryptol.Resolved
