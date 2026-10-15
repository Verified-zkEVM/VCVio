/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyDenotation

/-!
# Renaming preservation for ordered polymorphic semantics

Value renaming preserves the meaning of every constructor. Parameter binders
transport environments positionally, and recursive groups retain one fixed
point over the whole environment. No quantifier is moved across that fixed point.
-/

public section

open OmegaCompletePartialOrder IPFunctor

namespace Interop.Cryptol.Polymorphic

namespace Env

variable {w : Scope} (ρ : w.Assignment) {Γ Δ : List w.ValueSort}

/-- Read local values at the positions selected by a renaming. -/
@[expose] noncomputable def rename (r : ScopedSignature.Renaming Γ Δ) : Env ρ Δ →𝒄 Env ρ Γ :=
  ScopedDomain.Env.rename _ r

@[simp] theorem rename_apply (r : ScopedSignature.Renaming Γ Δ) (η : Env ρ Δ)
    {s : w.ValueSort} (x : ScopedVar Γ s) : rename ρ r η s x = η s (r x) := rfl

/-- Context normalization commutes with value lookup. -/
theorem rename_same (r : ScopedSignature.Renaming Γ Δ) (η : Env ρ Δ) :
    rename ρ (ScopedSignature.Renaming.map id r) (same ρ η) = same ρ (rename ρ r η) :=
  (ScopedDomain.Env.reindex_rename _ _ _ _ r η).symm

/-- Entering a numeric binder commutes with value lookup. -/
theorem rename_enterNum (r : ScopedSignature.Renaming Γ Δ) (l : Length) (η : Env ρ Δ) :
    rename (ρ.extendNum l) (ScopedSignature.Renaming.map
      (Scheme.subst (ParameterSubstitution.weakenNum w.numbers w.types)) r) (enterNum ρ l η) =
      enterNum ρ l (rename ρ r η) :=
  (ScopedDomain.Env.reindex_rename _ _ _ _ r η).symm

/-- Entering a type binder commutes with value lookup. -/
theorem rename_enterType (r : ScopedSignature.Renaming Γ Δ) (a : ClosedTy) (η : Env ρ Δ) :
    rename (ρ.extendType a) (ScopedSignature.Renaming.map
      (Scheme.subst (ParameterSubstitution.weakenType w.numbers w.types)) r) (enterType ρ a η) =
      enterType ρ a (rename ρ r η) :=
  (ScopedDomain.Env.reindex_rename _ _ _ _ r η).symm

/-- A lifted renaming retains the newly bound value. -/
theorem rename_cons (r : ScopedSignature.Renaming Γ Δ) {s : w.ValueSort}
    (x : s.Meaning ρ.val) (η : Env ρ Δ) :
    rename ρ (r.lift s) (cons ρ (η, x)) = cons ρ (rename ρ r η, x) := by
  funext b v
  cases v <;> rfl

/-- A lifted renaming retains a whole block of newly bound values. -/
theorem rename_append (r : ScopedSignature.Renaming Γ Δ) {Ξ : List w.ValueSort}
    (ξ : Env ρ Ξ) (η : Env ρ Δ) :
    rename ρ (r.liftMany Ξ) (append ρ (ξ, η)) = append ρ (ξ, rename ρ r η) :=
  ScopedDomain.Env.rename_append _ r ξ η

end Env

/-- Every constructor commutes with a renaming of its ambient value context. -/
theorem denoteOp_rename {w : Scope} {Γ Δ : List w.ValueSort}
    (r : ScopedSignature.Renaming Γ Δ) {s : w.ValueSort} (op : Op w s)
    (next : (p : Fin op.arity) → (ρ : (op.world p).Assignment) →
      Env ρ (op.binders p ++ Γ.map (op.reindex p)) →𝒄 (op.sort p).Meaning ρ.val)
    (ρ : w.Assignment) (η : Env ρ Δ) :
    denoteOp Δ op (fun p ρ => (next p ρ).comp (Env.rename ρ
      (ScopedSignature.Renaming.liftMany (ScopedSignature.Renaming.map (op.reindex p) r)
        (op.binders p)))) ρ η =
      denoteOp Γ op next ρ (Env.rename ρ r η) := by
  cases op <;>
    simp only [denoteOp, ContinuousHom.comp_apply, ContinuousHom.ofFun_apply,
      ContinuousHom.const_apply, ContinuousHom.curry, Op.binders, Op.reindex,
      ScopedSignature.Renaming.liftMany, List.nil_append, Fin.cases_zero, Fin.cases_succ,
      Env.rename_same, Env.rename_cons, Env.rename_enterNum, Env.rename_enterType] <;> try rfl
  case proofAbs c body =>
    funext h
    change next 0 (ρ.assume h.down) (Env.rename (ρ.assume h.down)
      (ScopedSignature.Renaming.map id r) (Env.assume ρ h.down η)) =
        next 0 (ρ.assume h.down) (Env.assume ρ h.down (Env.rename ρ r η))
    exact congrArg (next 0 (ρ.assume h.down)) (Env.rename_same ρ r η)
  case lam a b =>
    change DomainResult.value _ = DomainResult.value _
    congr 1
    apply ContinuousHom.ext
    intro x
    change next 0 ρ (Env.rename ρ
      (ScopedSignature.Renaming.lift (ScopedSignature.Renaming.map id r) (.mono a))
      (Env.cons ρ (s := .mono a) (Env.same ρ η, x))) = _
    exact congrArg (next 0 ρ) ((Env.rename_cons ρ (ScopedSignature.Renaming.map id r)
      (s := .mono a) x (Env.same ρ η)).trans (congrArg
        (fun ζ => Env.cons ρ (s := .mono a) (ζ, x)) (Env.rename_same ρ r η)))
  case fst a b =>
    change DomainResult.bind _ (next 0 ρ (Env.rename ρ (ScopedSignature.Renaming.map id r)
      (Env.same ρ η))) = _
    rw [Env.rename_same]
    rfl
  case snd a b =>
    change DomainResult.bind _ (next 0 ρ (Env.rename ρ (ScopedSignature.Renaming.map id r)
      (Env.same ρ η))) = _
    rw [Env.rename_same]
    rfl
  case bitNot =>
    change Semantics.bitNot (next 0 ρ (Env.rename ρ (ScopedSignature.Renaming.map id r)
      (Env.same ρ η))) = _
    rw [Env.rename_same]
    rfl
  case app a b =>
    change DomainResult.applyContinuous (next 0 ρ (Env.rename ρ
      (ScopedSignature.Renaming.map id r) (Env.same ρ η))) _ = _
    rw [Env.rename_same]
    rfl
  case pair a b =>
    change DomainResult.valueContinuous (next 0 ρ (Env.rename ρ
      (ScopedSignature.Renaming.map id r) (Env.same ρ η)), _) = _
    rw [Env.rename_same]
    rfl
  case index l a =>
    change Semantics.index (next 0 ρ (Env.rename ρ
      (ScopedSignature.Renaming.map id r) (Env.same ρ η))) _ = _
    rw [Env.rename_same]
    rfl
  case ite =>
    change (s.conditional ρ.val _) (next 0 ρ (Env.rename ρ
      (ScopedSignature.Renaming.map id r) (Env.same ρ η))) = _
    rw [Env.rename_same]
    rfl
  case letE value =>
    change next 1 ρ (Env.rename ρ
      (ScopedSignature.Renaming.lift (ScopedSignature.Renaming.map id r) value)
      (Env.cons ρ (s := value) (Env.same ρ η, next 0 ρ (Env.rename ρ
        (ScopedSignature.Renaming.map id r) (Env.same ρ η))))) = _
    exact congrArg (next 1 ρ) ((Env.rename_cons ρ (ScopedSignature.Renaming.map id r)
      (s := value) (next 0 ρ (Env.rename ρ (ScopedSignature.Renaming.map id r) (Env.same ρ η)))
        (Env.same ρ η)).trans (congrArg (fun ζ => Env.cons ρ (s := value) (ζ, next 0 ρ ζ))
          (Env.rename_same ρ r η)))
  case letRec bindings =>
    change next 0 ρ (Env.rename ρ
      (ScopedSignature.Renaming.liftMany (ScopedSignature.Renaming.map id r) bindings)
      (Env.append ρ (_, Env.same ρ η))) = _
    rw [Env.rename_append, Env.rename_same]
    let D := fun s : w.ValueSort => s.domain ρ.val
    let rhs : (i : Fin bindings.length) → Env ρ (bindings ++ Γ.map id) →𝒄
        bindings[i].Meaning ρ.val := fun i => next i.succ ρ
    have hg := ScopedDomain.Env.fixGroup_rename D (Ξ := bindings) rhs
      (ScopedSignature.Renaming.map id r) (Env.same ρ η)
    have hg' : ScopedDomain.Env.fixGroup D (Ξ := bindings)
        (fun i => (rhs i).comp (Env.rename ρ
          (ScopedSignature.Renaming.liftMany (ScopedSignature.Renaming.map id r) bindings)))
            (Env.same ρ η) = ScopedDomain.Env.fixGroup D rhs
              (Env.same ρ (Env.rename ρ r η)) :=
      hg.symm.trans (congrArg (ScopedDomain.Env.fixGroup D rhs) (Env.rename_same ρ r η))
    exact congrArg (fun ξ => next 0 ρ (Env.append ρ (Ξ := bindings)
      (ξ, Env.same ρ (Env.rename ρ r η)))) hg'

/-- Renaming preserves denotation, including below mixed binders and recursive groups. -/
theorem Term.denote_rename {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (r : ScopedSignature.Renaming Γ Δ) (ρ : w.Assignment) (η : Env ρ Δ) :
    Term.denote (t.rename r) ρ η = t.denote ρ (Env.rename ρ r η) := by
  induction t using ScopedFamily.Term.inductionOn with
  | hvar => rfl
  | hnode w Γ s h args ih =>
      rw [ScopedFamily.Term.rename_node]
      change denoteHead Δ h (fun p ρ => Term.denote ((args p).rename _) ρ) ρ η =
        denoteHead Γ h (fun p ρ => Term.denote (args p) ρ) ρ (Env.rename ρ r η)
      have hc : (fun p ρ => Term.denote ((args p).rename
          (ScopedSignature.Renaming.liftMany (ScopedSignature.Renaming.map
            (signature.reindex h p) r) (signature.binders h p))) ρ) =
          (fun p ρ => (Term.denote (args p) ρ).comp (Env.rename ρ
            (ScopedSignature.Renaming.liftMany (ScopedSignature.Renaming.map
              (signature.reindex h p) r) (signature.binders h p)))) := by
        funext p ρ
        apply ContinuousHom.ext
        intro η
        exact ih p _ ρ η
      rw [hc]
      rcases h with ⟨⟨s, op⟩, hs⟩
      cases hs
      exact denoteOp_rename r op (fun p ρ => Term.denote (args p) ρ) ρ η

end Interop.Cryptol.Polymorphic
