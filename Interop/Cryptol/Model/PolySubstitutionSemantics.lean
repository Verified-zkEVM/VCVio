/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyParameterSemantics
public import Interop.Cryptol.Model.PolySubstitutionLaws
public import Interop.Cryptol.Model.PolyRenaming

/-!
# Semantic preservation of value substitution

Substitution denotes a continuous map on local environments. Parameter
preservation supplies its naturality below numeric, type and proof binders;
whole-group fixed-point congruence handles mutually recursive declarations.
-/

public section

open OmegaCompletePartialOrder IPFunctor
namespace Interop.Cryptol.Polymorphic
namespace Env

/-- Evaluate substitution images in the target environment without forcing their results. -/
@[expose] noncomputable def substitute {w : Scope} (ρ : w.Assignment) {Γ Δ : List w.ValueSort}
    (θ : signature.Substitution Γ Δ) : Env ρ Δ →𝒄 Env ρ Γ :=
  .ofFun (fun η s x => Term.denote (θ x) ρ η)

/-- Lifting substitution retains the newly bound suspended value. -/
theorem substitute_lift_cons {w : Scope} (ρ : w.Assignment) {Γ Δ : List w.ValueSort}
    (θ : signature.Substitution Γ Δ) (s : w.ValueSort) (x : s.Meaning ρ.val) (η : Env ρ Δ) :
    substitute ρ (ScopedFamily.Substitution.lift θ s) (cons ρ (η, x)) =
      cons ρ (substitute ρ θ η, x) := by
  funext b v
  cases v with
  | zero => rfl
  | succ v =>
    change Term.denote ((θ v).rename ScopedVar.succ) ρ (cons ρ (η, x)) =
      Term.denote (θ v) ρ η
    rw [Term.denote_rename]
    rfl

/-- Lifting substitution retains a whole block of suspended values. -/
theorem substitute_liftMany_append {w : Scope} (ρ : w.Assignment) {Γ Δ : List w.ValueSort}
    (θ : signature.Substitution Γ Δ) (Ξ : List w.ValueSort) (ξ : Env ρ Ξ) (η : Env ρ Δ) :
    substitute ρ (ScopedFamily.Substitution.liftMany θ Ξ) (append ρ (ξ, η)) =
      append ρ (ξ, substitute ρ θ η) := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
    change substitute ρ (ScopedFamily.Substitution.lift (ScopedFamily.Substitution.liftMany θ Ξ) a)
      (cons ρ (append ρ ((fun b v => ξ b (.succ v)), η), ξ a .zero)) = _
    rw [substitute_lift_cons, ih]
    rfl

/-- Substitution images preserve positional correspondence when entering a child. -/
theorem substitute_reindex_pointwise {w : Scope} {a : w.ValueSort} (op : Head w a)
    (p : Fin op.code.2.arity) {Γ Δ : List w.ValueSort} (θ : signature.Substitution Γ Δ)
    (ρ : (op.code.2.world p).Assignment) (σ : w.Assignment)
    (hρ : σ.val = ρ.val.pull (op.code.2.binderMap p).parameters)
    (η : Env σ Δ) (ζ : Env ρ (Δ.map (op.code.2.reindex p)))
    (hη : ScopedDomain.Env.Pointwise η ζ) :
    ScopedDomain.Env.Pointwise (substitute σ θ η)
      (substitute ρ (θ.reindex reindexAction op p) ζ) := by
  intro a b x y hxy
  induction y using ScopedVar.map_inductionOn (op.code.2.reindex p) with
  | h b y =>
    have hpos := ScopedVar.sigma_eq_of_index_eq x y
      (by simpa only [ScopedVar.index_map] using hxy)
    apply (congr_arg_heq (fun v : (s : w.ValueSort) × ScopedVar Γ s =>
      Term.denote (θ v.2) σ η) hpos).trans
    change HEq (Term.denote (θ y) σ η)
      (Term.denote ((θ.reindex reindexAction op p) (y.map (op.code.2.reindex p))) ρ ζ)
    rw [ScopedFamily.Substitution.reindex_map]
    dsimp only
    rw [reindexAction_eq_cast]
    apply HEq.symm
    apply (Term.denote_cast_heq _ _ _ ρ ζ).trans
    apply Term.denote_parameters_related (θ y) (op.code.2.binderMap p) ρ σ hρ η _
    exact fun {_ _} x y he => ScopedDomain.Env.Pointwise.cast_right _ hη x y he
/-- Evaluating substitution images commutes with the child's parameter transport. -/
theorem substitute_reindex {w : Scope} {a : w.ValueSort} (op : Head w a)
    (p : Fin op.code.2.arity) {Γ Δ : List w.ValueSort} (θ : signature.Substitution Γ Δ)
    (ρ : (op.code.2.world p).Assignment) (σ : w.Assignment)
    (hρ : σ.val = ρ.val.pull (op.code.2.binderMap p).parameters)
    (hD : ∀ s, (op.code.2.reindex p s).domain ρ.val = s.domain σ.val) (η : Env σ Δ) :
    substitute ρ (θ.reindex reindexAction op p)
      (ScopedDomain.Env.reindex _ _ (op.code.2.reindex p) hD η) =
      ScopedDomain.Env.reindex _ _ (op.code.2.reindex p) hD (substitute σ θ η) := by
  symm
  apply ScopedDomain.Env.pointwise_reindex_eq
  apply substitute_reindex_pointwise op p θ ρ σ hρ
  apply ScopedDomain.Env.Pointwise.reindex_right
  exact ScopedDomain.Env.pointwise_refl η

end Env
/-- Every constructor commutes with simultaneous substitution in its ambient context. -/
theorem denoteOp_subst {w : Scope} {Γ Δ : List w.ValueSort}
    (θ : signature.Substitution Γ Δ) {s : w.ValueSort} (op : Op w s)
    (next : (p : Fin op.arity) → (ρ : (op.world p).Assignment) →
      Env ρ (op.binders p ++ Γ.map (op.reindex p)) →𝒄 (op.sort p).Meaning ρ.val)
    (ρ : w.Assignment) (η : Env ρ Δ) :
    denoteOp Δ op (fun p ρ => (next p ρ).comp (Env.substitute ρ
      (ScopedFamily.Substitution.liftMany (θ.reindex reindexAction (Head.ofOp op) p)
        (op.binders p)))) ρ η =
      denoteOp Γ op next ρ (Env.substitute ρ θ η) := by
  have hn (p : Fin op.arity) (σ : (op.world p).Assignment)
      (hσ : ρ.val = σ.val.pull (op.binderMap p).parameters)
      (hD : ∀ s, (op.reindex p s).domain σ.val = s.domain ρ.val) (ζ : Env ρ Δ) :=
    Env.substitute_reindex (Head.ofOp op) p θ σ ρ hσ hD ζ
  cases op <;>
    simp only [denoteOp, ContinuousHom.comp_apply, ContinuousHom.ofFun_apply,
      ContinuousHom.const_apply, ContinuousHom.curry, Op.binders, Op.reindex,
      ScopedFamily.Substitution.liftMany, List.nil_append, Fin.cases_zero, Fin.cases_succ,
      Env.substitute_lift_cons]
  all_goals try
    have hs := fun p ζ => hn p ρ (ParameterAssignment.pull_id ρ.val).symm (fun _ => rfl) ζ
  all_goals try (simp only [Env.same, hs]; done)
  case numAbs body =>
    congr 1
    funext l
    apply congrArg (next 0 (ρ.extendNum l))
    exact hn 0 (ρ.extendNum l) (ParameterAssignment.pull_weakenNum ρ.val l).symm _ η
  case typeAbs body =>
    congr 1
    funext a
    apply congrArg (next 0 (ρ.extendType a))
    exact hn 0 (ρ.extendType a) (ParameterAssignment.pull_weakenType ρ.val a).symm _ η
  case proofAbs c body =>
    funext h
    apply congrArg (next 0 (ρ.assume h.down))
    exact hn 0 (ρ.assume h.down) (ParameterAssignment.pull_id ρ.val).symm (fun _ => rfl) η
  case lam a b =>
    change DomainResult.value _ = DomainResult.value _
    congr 1
    apply ContinuousHom.ext
    intro x
    change next 0 ρ (Env.substitute ρ
      (ScopedFamily.Substitution.lift (θ.reindex reindexAction (Head.ofOp (.lam a b)) 0) (.mono a))
      (Env.cons ρ (s := .mono a) (Env.same ρ η, x))) = _
    erw [Env.substitute_lift_cons]
    simp only [Env.same, hs]
    rfl
  case app a b =>
    change DomainResult.applyContinuous (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.app a b)) 0)
      (Env.same ρ η))) _ = _
    simp only [Env.same, hs]
    rfl
  case pair a b =>
    change DomainResult.valueContinuous (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.pair a b)) 0)
      (Env.same ρ η)), _) = _
    simp only [Env.same, hs]
    rfl
  case fst a b =>
    change DomainResult.bind (.ofFun Prod.fst) (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.fst a b)) 0)
      (Env.same ρ η))) = _
    simp only [Env.same, hs]
    rfl
  case snd a b =>
    change DomainResult.bind (.ofFun Prod.snd) (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.snd a b)) 0)
      (Env.same ρ η))) = _
    simp only [Env.same, hs]
    rfl
  case index l a =>
    change Semantics.index (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.index l a)) 0)
      (Env.same ρ η))) _ = _
    simp only [Env.same, hs]
    rfl
  case ite =>
    change s.conditional ρ.val _ (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.ite s)) 0)
      (Env.same ρ η))) = _
    simp only [Env.same, hs]
    rfl
  case bitNot =>
    change Semantics.bitNot (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.bitNot)) 0)
      (Env.same ρ η))) = _
    simp only [Env.same, hs]
    rfl
  case bitOp op =>
    change Semantics.binary _ (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.bitOp op)) 0)
      (Env.same ρ η))) _ = _
    simp only [Env.same, hs]
    rfl
  case intOp op =>
    change Semantics.binary _ (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.intOp op)) 0)
      (Env.same ρ η))) _ = _
    simp only [Env.same, hs]
    rfl
  case intEq =>
    change Semantics.binary _ (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.intEq)) 0)
      (Env.same ρ η))) _ = _
    simp only [Env.same, hs]
    rfl
  case intLt =>
    change Semantics.binary _ (next 0 ρ
      (Env.substitute ρ (θ.reindex reindexAction (Head.ofOp (.intLt)) 0)
      (Env.same ρ η))) _ = _
    simp only [Env.same, hs]
    rfl
  case letE value =>
    change next 1 ρ (Env.substitute ρ
      (ScopedFamily.Substitution.lift (θ.reindex reindexAction
        (Head.ofOp (.letE value s)) 1) value)
      (Env.cons ρ (s := value) (Env.same ρ η, next 0 ρ (Env.substitute ρ
        (θ.reindex reindexAction (Head.ofOp (.letE value s)) 0) (Env.same ρ η))))) = _
    erw [Env.substitute_lift_cons]
    simp only [Env.same, hs]
    rfl
  case letRec bindings =>
    change next 0 ρ (Env.substitute ρ
      (ScopedFamily.Substitution.liftMany (θ.reindex reindexAction
        (Head.ofOp (.letRec bindings s)) 0) bindings)
      (Env.append ρ (_, Env.same ρ η))) = _
    rw [Env.substitute_liftMany_append]
    simp only [Env.same, hs]
    let D := fun s : w.ValueSort => s.domain ρ.val
    let rhs : (i : Fin bindings.length) → Env ρ (bindings ++ Γ.map id) →𝒄
        bindings[i].Meaning ρ.val := fun i => next i.succ ρ
    let rhs' : (i : Fin bindings.length) → Env ρ (bindings ++ Δ.map id) →𝒄
        bindings[i].Meaning ρ.val := fun i => (next i.succ ρ).comp (Env.substitute ρ
          (ScopedFamily.Substitution.liftMany (θ.reindex reindexAction
            (Head.ofOp (.letRec bindings s)) i.succ) bindings))
    have hg : ScopedDomain.Env.fixGroup D rhs' (Env.same ρ η) =
        ScopedDomain.Env.fixGroup D rhs (Env.same ρ (Env.substitute ρ θ η)) := by
      apply ScopedDomain.Env.fixGroup_congr
      intro ξ i
      change next i.succ ρ (Env.substitute ρ
        (ScopedFamily.Substitution.liftMany (θ.reindex reindexAction
          (Head.ofOp (.letRec bindings s)) i.succ) bindings)
        (Env.append ρ (ξ, Env.same ρ η))) = _
      rw [Env.substitute_liftMany_append]
      simp only [Env.same, hs]
      rfl
    exact congrArg (fun ξ => next 0 ρ (Env.append ρ
      (ξ, Env.same ρ (Env.substitute ρ θ η)))) hg

/-- Value substitution preserves denotation under mixed binders and simultaneous recursion. -/
theorem Term.denote_subst {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (θ : signature.Substitution Γ Δ) (ρ : w.Assignment) (η : Env ρ Δ) :
    Term.denote (t.subst θ) ρ η = t.denote ρ (Env.substitute ρ θ η) := by
  induction t using ScopedFamily.Term.inductionOn with
  | hvar => rfl
  | hnode w Γ s h args ih =>
      rw [Term.subst, ScopedFamily.Term.subst_node]
      change denoteHead Δ h (fun p ρ => Term.denote (Term.subst _ (args p)) ρ) ρ η =
        denoteHead Γ h (fun p ρ => Term.denote (args p) ρ) ρ (Env.substitute ρ θ η)
      have hc : (fun p ρ => Term.denote (Term.subst
          (ScopedFamily.Substitution.liftMany (θ.reindex reindexAction h p)
            (signature.binders h p)) (args p)) ρ) =
          (fun p ρ => (Term.denote (args p) ρ).comp (Env.substitute ρ
            (ScopedFamily.Substitution.liftMany (θ.reindex reindexAction h p)
              (signature.binders h p)))) := by
        funext p ρ
        apply ContinuousHom.ext
        intro η
        exact ih p _ ρ η
      rw [hc]
      rcases h with ⟨⟨s, op⟩, hs⟩
      cases hs
      exact denoteOp_subst θ op (fun p ρ => Term.denote (args p) ρ) ρ η

end Interop.Cryptol.Polymorphic
