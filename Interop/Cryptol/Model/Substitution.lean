/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Syntax

/-!
# Capture-avoiding substitution laws

The laws apply before and after polymorphic instantiation. They justify
closing a body and then entering its binders in the call-by-name machine.
-/

public section

namespace Interop.Cryptol.Expr

variable {N V : Type} {Γ Δ Ξ : List (Ty N V)} {a : Ty N V}

@[simp] theorem Renaming.lift_id :
    @Renaming.lift N V Γ Γ a (fun {_} x => x) = (fun {_} x => x) := by
  funext b x
  cases x <;> rfl

theorem Renaming.lift_comp (ρ : Renaming Γ Δ) (τ : Renaming Δ Ξ) :
    @Renaming.lift N V Γ Ξ a (fun {_} x => τ (ρ x)) =
      (fun {b} x => @Renaming.lift N V Δ Ξ a τ b (@Renaming.lift N V Γ Δ a ρ b x)) := by
  funext b x
  cases x <;> rfl

/-- Renaming by the identity preserves syntax. -/
@[simp] theorem rename_id (e : Expr Γ a) : e.rename (fun {_} x => x) = e := by
  induction e <;> simp_all only [rename, Renaming.lift_id]

/-- Successive renamings compose. -/
theorem rename_rename (e : Expr Γ a) (ρ : Renaming Γ Δ) (τ : Renaming Δ Ξ) :
    (e.rename ρ).rename τ = e.rename (fun {_} x => τ (ρ x)) := by
  induction e generalizing Δ Ξ <;> simp_all only [rename, ← Renaming.lift_comp]

@[simp] theorem Substitution.lift_var :
    @Substitution.lift N V Γ Γ a (fun {_} x => Expr.var x) =
      (fun {_} x => Expr.var x) := by
  funext b x
  cases x <;> rfl

/-- Substituting variables for themselves preserves syntax. -/
@[simp] theorem subst_var (e : Expr Γ a) : e.subst Expr.var = e := by
  induction e <;> simp_all only [subst, Substitution.lift_var]

theorem Substitution.lift_rename (σ : Substitution Γ Δ) (ρ : Renaming Δ Ξ) :
    @Substitution.lift N V Γ Ξ a (fun {_} x => (σ x).rename ρ) =
      (fun {b} x => (@Substitution.lift N V Γ Δ a σ b x).rename ρ.lift) := by
  funext b x
  cases x with
  | zero => rfl
  | succ x => simp only [Substitution.lift, rename_rename, Renaming.lift]

/-- Renaming a substituted expression renames each suspended substitution. -/
theorem rename_subst (e : Expr Γ a) (σ : Substitution Γ Δ) (ρ : Renaming Δ Ξ) :
    (e.subst σ).rename ρ = e.subst (fun {_} x => (σ x).rename ρ) := by
  induction e generalizing Δ Ξ <;> simp_all only [subst, rename, ← Substitution.lift_rename]

theorem Substitution.lift_renaming (ρ : Renaming Γ Δ) (σ : Substitution Δ Ξ) :
    @Substitution.lift N V Γ Ξ a (fun {_} x => σ (ρ x)) =
      (fun {b} x => @Substitution.lift N V Δ Ξ a σ b (@Renaming.lift N V Γ Δ a ρ b x)) := by
  funext b x
  cases x <;> rfl

/-- Substitution after renaming composes the two variable assignments. -/
theorem subst_rename (e : Expr Γ a) (ρ : Renaming Γ Δ) (σ : Substitution Δ Ξ) :
    (e.rename ρ).subst σ = e.subst (fun {_} x => σ (ρ x)) := by
  induction e generalizing Δ Ξ <;> simp_all only [subst, rename, ← Substitution.lift_renaming]

theorem Substitution.lift_comp (σ : Substitution Γ Δ) (τ : Substitution Δ Ξ) :
    @Substitution.lift N V Γ Ξ a (fun {_} x => (σ x).subst τ) =
      (fun {b} x => (@Substitution.lift N V Γ Δ a σ b x).subst τ.lift) := by
  funext b x
  cases x with
  | zero => rfl
  | succ x => simp only [Substitution.lift, rename_subst, subst_rename]

/-- Capture-avoiding simultaneous substitutions compose. -/
theorem subst_subst (e : Expr Γ a) (σ : Substitution Γ Δ) (τ : Substitution Δ Ξ) :
    (e.subst σ).subst τ = e.subst (fun {_} x => (σ x).subst τ) := by
  induction e generalizing Δ Ξ <;> simp_all only [subst, ← Substitution.lift_comp]

/-- Extend a closing substitution with a suspended argument. -/
@[expose] def Substitution.cons (σ : Substitution Γ Δ) (argument : Expr Δ a) :
    Substitution (a :: Γ) Δ
  | _, .zero => argument
  | _, .succ x => σ x

/-- Closing a body and then entering its binder equals extending its closing
substitution with the actual argument. -/
theorem substOne_subst_lift {b : Ty N V} (body : Expr (a :: Γ) b)
    (σ : Substitution Γ Δ) (argument : Expr Δ a) :
    (body.subst σ.lift).substOne argument = body.subst (σ.cons argument) := by
  rw [substOne, subst_subst]
  congr 1
  funext b x
  cases x with
  | zero => rfl
  | succ x =>
      simp only [Substitution.lift, subst_rename, Substitution.cons]
      exact subst_var (σ x)

end Interop.Cryptol.Expr
