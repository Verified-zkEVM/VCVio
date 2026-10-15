/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyReindex
public import Interop.Cryptol.Model.PolyConstructors

/-!
# Value substitution below polymorphic binders

Entering a numeric or type abstraction weakens every substituted description's
free parameters. New value bindings remain variables. Both operations are
provided by the shared PolyFun binding-family API.
-/

public section

namespace Interop.Cryptol.Polymorphic

namespace Op

/-- The checked parameter weakening performed by a constructor child. -/
@[expose] def binderMap {w : Scope} {s : w.ValueSort} (op : Op w s) (p : Fin op.arity) :
    Scope.Map w (op.world p) := by
  cases op <;> first
    | exact Scope.Map.weakenNum w
    | exact Scope.Map.weakenType w
    | exact Scope.Map.weakenProof w _
    | exact Scope.Map.id w

/-- The checked map agrees with the polynomial's context action. -/
theorem binderMap_sort {w : Scope} {s : w.ValueSort} (op : Op w s) (p : Fin op.arity) :
    (op.binderMap p).sort = op.reindex p := by
  cases op <;> try rfl
  all_goals
    funext a
    exact Scheme.subst_id a

end Op

/-- Reindex an existing term while entering one of its surrounding constructor's children. -/
@[expose] def reindexAction : signature.ReindexAction :=
  fun {_ _} h p {Γ b} t => Eq.mp
    (congrArg (fun f => Term (h.code.2.world p) (Γ.map f) (f b))
      (h.code.2.binderMap_sort p)) (Term.parameters (h.code.2.binderMap p) t)

/-- Parameter weakening preserves variable leaves. -/
theorem reindexAction_preservesVars : reindexAction.PreservesVars signature := by
  intro h p Γ b x
  unfold reindexAction
  rw [Term.parameters_var]
  exact transport _ _ (h.code.2.binderMap_sort p) x
where
  transport {w z : Scope} (f g : w.ValueSort → z.ValueSort) (h : f = g)
      {Γ : List w.ValueSort} {b : w.ValueSort} (x : IPFunctor.ScopedVar Γ b) :
      (Eq.mp (congrArg (fun f => Term z (Γ.map f) (f b)) h)
        (IPFunctor.ScopedFamily.Term.var (σ := signature) (x.map f))) =
        IPFunctor.ScopedFamily.Term.var (x.map g) := by
    cases h
    rfl

/-- Entering a parameter binder commutes with renaming local values. -/
theorem reindexAction_preservesRenaming : reindexAction.PreservesRenaming signature := by
  intro h p Γ Δ b ρ t
  unfold reindexAction
  rw [Term.parameters_rename]
  exact transport _ _ (h.code.2.binderMap_sort p) ρ _
where
  transport {w z : Scope} (f g : w.ValueSort → z.ValueSort) (h : f = g)
      {Γ Δ : List w.ValueSort} {b : w.ValueSort}
      (ρ : IPFunctor.ScopedSignature.Renaming Γ Δ) (t : Term z (Γ.map f) (f b)) :
      Eq.mp (congrArg (fun f => Term z (Δ.map f) (f b)) h)
        (t.rename (IPFunctor.ScopedSignature.Renaming.map f ρ)) =
      (Eq.mp (congrArg (fun f => Term z (Γ.map f) (f b)) h) t).rename
        (IPFunctor.ScopedSignature.Renaming.map g ρ) := by
    cases h
    rfl

/-- Simultaneous, capture-avoiding substitution of local value descriptions. -/
@[expose] def Term.subst {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (θ : signature.Substitution Γ Δ) (t : Term w Γ s) : Term w Δ s :=
  IPFunctor.ScopedFamily.Term.subst reindexAction θ t

/-- Identity substitution holds even below mixed parameter and value binders. -/
@[simp] theorem Term.subst_id {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) : t.subst (fun x => var x) = t :=
  IPFunctor.ScopedFamily.Term.subst_id reindexAction reindexAction_preservesVars t

/-- Substituting after a value renaming composes the variable assignments. -/
theorem Term.subst_rename {w : Scope} {Γ Δ Θ : List w.ValueSort} {s : w.ValueSort}
    (ρ : IPFunctor.ScopedSignature.Renaming Γ Δ) (θ : signature.Substitution Δ Θ)
    (t : Term w Γ s) :
    Term.subst θ (t.rename ρ) = t.subst (fun x => θ (ρ x)) :=
  IPFunctor.ScopedFamily.Term.subst_rename reindexAction ρ θ t

/-- Renaming a substituted term renames all its images, below every kind of binder. -/
theorem Term.rename_subst {w : Scope} {Γ Δ Θ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (θ : signature.Substitution Γ Δ)
    (ρ : IPFunctor.ScopedSignature.Renaming Δ Θ) :
    (t.subst θ).rename ρ = t.subst (fun x => (θ x).rename ρ) :=
  IPFunctor.ScopedFamily.Term.rename_subst reindexAction reindexAction_preservesRenaming t θ ρ

/-- Substitute one local value without capturing its free parameters or values. -/
@[expose] def Term.substOne {w : Scope} {Γ : List w.ValueSort} {s t : w.ValueSort}
    (body : Term w (s :: Γ) t) (value : Term w Γ s) : Term w Γ t :=
  IPFunctor.ScopedFamily.Term.substOne reindexAction body value

end Interop.Cryptol.Polymorphic
