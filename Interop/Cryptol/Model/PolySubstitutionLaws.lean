/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyReindexLaws
public import Interop.Cryptol.Model.PolySubstitution
public import PolyFun.IPFunctor.Scoped.FamilyMapSubstitution

/-!
# Substitution algebra for ordered polymorphic terms

Parameter weakening commutes with lifted parameter maps at each child. This
square supplies parameter/value substitution fusion and makes the value
substitution action lawful under numeric, type, proof and value binders.
-/

public section

namespace Interop.Cryptol.Polymorphic
namespace Op

/-- Entering a child and mapping parameters commute as checked scope maps. -/
theorem binderMap_childMap {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort}
    (op : Op w s) (p : Fin (op.mapHead μ).2.arity) :
    (op.binderMap (p.cast (op.mapHead_arity μ))).comp (op.childMap μ p) =
      μ.comp ((op.mapHead μ).2.binderMap p) := by
  apply Scope.Map.ext
  cases op <;> dsimp only [binderMap, childMap, mapHead, Scope.Map.comp, Scope.Map.id,
    Scope.Map.liftNum, Scope.Map.liftType, Scope.Map.assume,
    Scope.Map.weakenNum, Scope.Map.weakenType, Scope.Map.weakenProof]
  all_goals simp only [ParameterSubstitution.weakenNum_comp_liftNum,
    ParameterSubstitution.weakenType_comp_liftType,
    ParameterSubstitution.id_comp, ParameterSubstitution.comp_id]

end Op

/-- Binder reindexing is parameter substitution followed by context normalization. -/
theorem reindexAction_eq_cast {w : Scope} {a : w.ValueSort} (op : Head w a)
    (p : Fin op.code.2.arity) {Γ : List w.ValueSort} {s : w.ValueSort} (t : Term w Γ s) :
    reindexAction op p t = (Term.parameters (op.code.2.binderMap p) t).cast
      (congrArg (fun f => Γ.map f) (op.code.2.binderMap_sort p))
      (congrFun (op.code.2.binderMap_sort p) s) := by
  exact transport _ _ (op.code.2.binderMap_sort p) _
where
  transport {w z : Scope} (f g : w.ValueSort → z.ValueSort) (h : f = g)
      {Γ : List w.ValueSort} {s : w.ValueSort} (t : Term z (Γ.map f) (f s)) :
      Eq.mp (congrArg (fun f => Term z (Γ.map f) (f s)) h) t =
        t.cast (congrArg (fun f => Γ.map f) h) (congrFun h s) := by
    cases h
    rfl

/-- The constructor-local scope square commutes on complete term images. -/
theorem parameterHom_preservesReindex :
    parameterHom.PreservesReindex reindexAction reindexAction := by
  intro w z μ a op p Γ b t
  change Head w a at op
  change Fin (op.code.2.mapHead μ).2.arity at p
  dsimp only [parameterHom, Head.map]
  rw [reindexAction_eq_cast, reindexAction_eq_cast]
  rw [IPFunctor.ScopedFamily.Term.map_cast]
  apply (IPFunctor.ScopedFamily.Term.cast_heq _ _ _).trans
  apply HEq.trans ?_ (IPFunctor.ScopedFamily.Term.cast_heq _ _ _).symm
  change HEq (Term.parameters (op.code.2.childMap μ p)
      (Term.parameters (op.code.2.binderMap (p.cast (op.code.2.mapHead_arity μ))) t))
    (Term.parameters ((op.code.2.mapHead μ).2.binderMap p) (Term.parameters μ t))
  apply (Term.parameters_parameters_heq _ _ t).trans
  apply HEq.trans ?_ (Term.parameters_parameters_heq _ _ t).symm
  rw [op.code.2.binderMap_childMap μ p]

/-- Parameter mapping commutes with every lifted value substitution. -/
theorem parameterHom_preservesSubstitution :
    parameterHom.PreservesSubstitution reindexAction reindexAction :=
  parameterHom_preservesReindex.preservesSubstitution _ _ _

/-- Parameter and value substitution fuse without identifying binding positions. -/
theorem Term.parameters_subst {w z : Scope} (μ : Scope.Map w z)
    {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (θ : signature.Substitution Γ Δ) (t : Term w Γ s) :
    Term.parameters μ (t.subst θ) =
      (Term.parameters μ t).subst (θ.map parameterHom μ) :=
  IPFunctor.ScopedFamily.Term.map_subst parameterHom reindexAction reindexAction
    parameterHom_preservesSubstitution μ θ t

/-- Reindexing a substitution maps each image and normalizes both contexts. -/
theorem substitution_reindex_eq_map {w : Scope} {a : w.ValueSort} (op : Head w a)
    (p : Fin op.code.2.arity) {Γ Δ : List w.ValueSort} (θ : signature.Substitution Γ Δ) :
    (θ.reindex reindexAction op p : signature.Substitution _ _) =
      (IPFunctor.ScopedFamily.Substitution.cast
        (congrArg (fun f => Γ.map f) (op.code.2.binderMap_sort p))
        (congrArg (fun f => Δ.map f) (op.code.2.binderMap_sort p))
        (θ.map parameterHom (op.code.2.binderMap p)) : signature.Substitution _ _) := by
  apply eq_of_heq
  apply HEq.trans ?_ (IPFunctor.ScopedFamily.Substitution.cast_heq _ _ _).symm
  apply IPFunctor.ScopedVar.mapLookup_heq (op.code.2.binderMap_sort p).symm
  · exact funext (fun s => congrArg (fun Δ => Term (op.code.2.world p) Δ s)
      (congrArg (List.map · Δ) (op.code.2.binderMap_sort p).symm))
  · intro s x
    dsimp only
    rw [reindexAction_eq_cast]
    exact IPFunctor.ScopedFamily.Term.cast_heq _ _ _

/-- Binder reindexing preserves simultaneous value substitution. -/
theorem reindexAction_preservesSubstitution : reindexAction.PreservesSubstitution signature := by
  intro w a op p Γ Δ b θ t
  dsimp only
  rw [reindexAction_eq_cast, reindexAction_eq_cast]
  change IPFunctor.ScopedFamily.Term.cast _ _ (Term.parameters _ (Term.subst θ t)) = _
  rw [Term.parameters_subst, Term.subst, IPFunctor.ScopedFamily.Term.cast_subst]
  rw [substitution_reindex_eq_map]

/-- The polymorphic reindexing action satisfies the full substitution algebra. -/
theorem reindexAction_lawful : reindexAction.Lawful signature :=
  ⟨reindexAction_preservesVars, reindexAction_preservesRenaming,
    reindexAction_preservesSubstitution⟩

/-- Successive value substitutions compose under every parameter and value binder. -/
theorem Term.subst_subst {w : Scope} {Γ Δ Θ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (θ : signature.Substitution Γ Δ) (τ : signature.Substitution Δ Θ) :
    (t.subst θ).subst τ = t.subst (fun x => Term.subst τ (θ x)) :=
  IPFunctor.ScopedFamily.Term.subst_subst reindexAction reindexAction_lawful t θ τ
end Interop.Cryptol.Polymorphic
