/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Denotation

/-!
# Binding and the compositional semantics

Renaming changes the environment's variable lookup, and simultaneous
substitution composes the denotations of suspended expressions. These laws
connect lexical scope to the machine's capture-avoiding substitution.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

namespace Expr

variable {Γ Δ : List ClosedTy} {a : ClosedTy}

/-- Reindex a semantic environment along a renaming. -/
@[expose] def Renaming.pull (ρ : Renaming Γ Δ) (η : Environment Δ) : Environment Γ :=
  fun a x => η a (ρ x)

@[simp] theorem Renaming.pull_lift (ρ : Renaming Γ Δ) (η : Environment Δ)
    {b : ClosedTy} (x : Computation b) :
    Renaming.pull (Renaming.lift (a := b) ρ) (η.extend x) = (ρ.pull η).extend x := by
  funext a v
  cases v <;> rfl

/-- The continuous function denoted by a body under its next binder. -/
@[expose] noncomputable def bodyDenote {b : ClosedTy} (body : Expr (a :: Γ) b)
    (η : Environment Γ) : Computation a →𝒄 Computation b :=
  ContinuousHom.curry (body.denote.comp Environment.extendContinuous) η

@[simp] theorem bodyDenote_apply {b : ClosedTy} (body : Expr (a :: Γ) b)
    (η : Environment Γ) (x : Computation a) :
    body.bodyDenote η x = body.denote (η.extend x) := rfl

/-- Renaming is interpreted by reindexing the environment. -/
theorem denote_rename {Γ : List ClosedTy} {a : ClosedTy} (e : Expr Γ a)
    {Δ : List ClosedTy} (ρ : Renaming Γ Δ) (η : Environment Δ) :
    (e.rename ρ).denote η = e.denote (ρ.pull η) := by
  induction e generalizing Δ with
  | var x => rfl
  | bit x => rfl
  | integer x => rfl
  | unit => rfl
  | error e => rfl
  | lam body ih =>
      change DomainResult.value ((body.rename ρ.lift).bodyDenote η) =
        DomainResult.value (body.bodyDenote (ρ.pull η))
      congr 1
      ext x
      simp only [bodyDenote_apply, ih, Renaming.pull_lift]
  | app f x ihf ihx =>
      change DomainResult.applyContinuous ((f.rename ρ).denote η) ((x.rename ρ).denote η) = _
      rw [ihf, ihx]
      rfl
  | letE x body ihx ihbody =>
      change (body.rename ρ.lift).denote (η.extend ((x.rename ρ).denote η)) = _
      rw [ihx, ihbody, Renaming.pull_lift]
      rfl
  | force x next ihx ihn =>
      change DomainResult.force ((x.rename ρ).denote η) ((next.rename ρ).denote η) = _
      rw [ihx, ihn]
      rfl
  | pair x y ihx ihy =>
      change DomainResult.value ((x.rename ρ).denote η, (y.rename ρ).denote η) = _
      rw [ihx, ihy]
      rfl
  | fst x ih =>
      change DomainResult.bind _ ((x.rename ρ).denote η) = _
      rw [ih]
      rfl
  | snd x ih =>
      change DomainResult.bind _ ((x.rename ρ).denote η) = _
      rw [ih]
      rfl
  | generate l body ih =>
      change DomainResult.value (fun i : l.Index =>
        (body.rename ρ.lift).denote (η.extend (.value ⟨(Length.indexNat i : Int)⟩))) = _
      simp only [ih, Renaming.pull_lift]
      rfl
  | index xs i ihxs ihi =>
      change Semantics.index ((xs.rename ρ).denote η) ((i.rename ρ).denote η) = _
      rw [ihxs, ihi]
      rfl
  | ite p x y ihp ihx ihy =>
      change Semantics.conditional ((x.rename ρ).denote η, (y.rename ρ).denote η)
        ((p.rename ρ).denote η) = _
      rw [ihp, ihx, ihy]
      rfl
  | fix body ih =>
      change ((body.rename ρ.lift).bodyDenote η).fix = (body.bodyDenote (ρ.pull η)).fix
      congr 1
      ext x
      simp only [bodyDenote_apply, ih, Renaming.pull_lift]
  | bitNot x ih =>
      change DomainResult.bind _ ((x.rename ρ).denote η) = _
      rw [ih]
      rfl
  | bitOp op x y ihx ihy =>
      change Semantics.binary _ ((x.rename ρ).denote η) ((y.rename ρ).denote η) = _
      rw [ihx, ihy]
      rfl
  | intOp op x y ihx ihy =>
      change Semantics.binary _ ((x.rename ρ).denote η) ((y.rename ρ).denote η) = _
      rw [ihx, ihy]
      rfl
  | intEq x y ihx ihy =>
      change Semantics.binary _ ((x.rename ρ).denote η) ((y.rename ρ).denote η) = _
      rw [ihx, ihy]
      rfl
  | intLt x y ihx ihy =>
      change Semantics.binary _ ((x.rename ρ).denote η) ((y.rename ρ).denote η) = _
      rw [ihx, ihy]
      rfl


/-- Interpret every suspended expression in a simultaneous substitution. -/
@[expose] noncomputable def Substitution.meaning (σ : Substitution Γ Δ)
    (η : Environment Δ) : Environment Γ := fun _ v => (σ v).denote η

@[simp] theorem Substitution.meaning_lift (σ : Substitution Γ Δ) (η : Environment Δ)
    {b : ClosedTy} (x : Computation b) :
    Substitution.meaning (Substitution.lift (a := b) σ) (η.extend x) =
      (σ.meaning η).extend x := by
  funext a v
  cases v with
  | zero => rfl
  | succ v =>
      change ((σ v).rename Var.succ).denote (η.extend x) = (σ v).denote η
      rw [denote_rename]
      rfl

/-- Substitution composes the denotations of suspended expressions. -/
theorem denote_subst {Γ : List ClosedTy} {a : ClosedTy} (e : Expr Γ a)
    {Δ : List ClosedTy} (σ : Substitution Γ Δ) (η : Environment Δ) :
    (e.subst σ).denote η = e.denote (σ.meaning η) := by
  induction e generalizing Δ with
  | var x => rfl
  | bit x => rfl
  | integer x => rfl
  | unit => rfl
  | error e => rfl
  | lam body ih =>
      change DomainResult.value ((body.subst σ.lift).bodyDenote η) =
        DomainResult.value (body.bodyDenote (σ.meaning η))
      congr 1
      ext x
      simp only [bodyDenote_apply, ih, Substitution.meaning_lift]
  | app f x ihf ihx =>
      change DomainResult.applyContinuous ((f.subst σ).denote η) ((x.subst σ).denote η) = _
      rw [ihf, ihx]
      rfl
  | letE x body ihx ihbody =>
      change (body.subst σ.lift).denote (η.extend ((x.subst σ).denote η)) = _
      rw [ihx, ihbody, Substitution.meaning_lift]
      rfl
  | force x next ihx ihn =>
      change DomainResult.force ((x.subst σ).denote η) ((next.subst σ).denote η) = _
      rw [ihx, ihn]
      rfl
  | pair x y ihx ihy =>
      change DomainResult.value ((x.subst σ).denote η, (y.subst σ).denote η) = _
      rw [ihx, ihy]
      rfl
  | fst x ih =>
      change DomainResult.bind _ ((x.subst σ).denote η) = _
      rw [ih]
      rfl
  | snd x ih =>
      change DomainResult.bind _ ((x.subst σ).denote η) = _
      rw [ih]
      rfl
  | generate l body ih =>
      change DomainResult.value (fun i : l.Index =>
        (body.subst σ.lift).denote (η.extend (.value ⟨(Length.indexNat i : Int)⟩))) = _
      simp only [ih, Substitution.meaning_lift]
      rfl
  | index xs i ihxs ihi =>
      change Semantics.index ((xs.subst σ).denote η) ((i.subst σ).denote η) = _
      rw [ihxs, ihi]
      rfl
  | ite p x y ihp ihx ihy =>
      change Semantics.conditional ((x.subst σ).denote η, (y.subst σ).denote η)
        ((p.subst σ).denote η) = _
      rw [ihp, ihx, ihy]
      rfl
  | fix body ih =>
      change ((body.subst σ.lift).bodyDenote η).fix = (body.bodyDenote (σ.meaning η)).fix
      congr 1
      ext x
      simp only [bodyDenote_apply, ih, Substitution.meaning_lift]
  | bitNot x ih =>
      change DomainResult.bind _ ((x.subst σ).denote η) = _
      rw [ih]
      rfl
  | bitOp op x y ihx ihy =>
      change Semantics.binary _ ((x.subst σ).denote η) ((y.subst σ).denote η) = _
      rw [ihx, ihy]
      rfl
  | intOp op x y ihx ihy =>
      change Semantics.binary _ ((x.subst σ).denote η) ((y.subst σ).denote η) = _
      rw [ihx, ihy]
      rfl
  | intEq x y ihx ihy =>
      change Semantics.binary _ ((x.subst σ).denote η) ((y.subst σ).denote η) = _
      rw [ihx, ihy]
      rfl
  | intLt x y ihx ihy =>
      change Semantics.binary _ ((x.subst σ).denote η) ((y.subst σ).denote η) = _
      rw [ihx, ihy]
      rfl

/-- Substituting one argument extends the environment with its meaning. -/
theorem denote_substOne {b : ClosedTy} (body : Expr (a :: Γ) b)
    (argument : Expr Γ a) (η : Environment Γ) :
    (body.substOne argument).denote η = body.denote (η.extend (argument.denote η)) := by
  rw [substOne, denote_subst]
  congr 1
  funext a v
  cases v <;> rfl

/-- Recursive definitions satisfy the compositional unfolding equation. -/
theorem denote_fix (body : Expr (a :: Γ) a) (η : Environment Γ) :
    (Expr.fix body).denote η = body.denote (η.extend ((Expr.fix body).denote η)) :=
  (body.bodyDenote η).map_fix.symm


end Expr

end Interop.Cryptol
