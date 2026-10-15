/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyReindex
public import Interop.Cryptol.Model.PolyDenotation
public import PolyFun.IPFunctor.Scoped.DomainRelation

/-!
# Parameter transport in ordered semantic domains

Environment transport retains binding positions even when symbolic sorts merge.
Errors, instantiation and finite-word evidence respect the same domain equalities,
without moving a suspension across a quantifier.
-/

public section

open OmegaCompletePartialOrder IPFunctor

namespace Interop.Cryptol.Polymorphic
namespace Env

/-- Transport a local environment along a checked parameter substitution. -/
@[expose] noncomputable def parameters {w z : Scope} (μ : Scope.Map w z)
    (ρ : z.Assignment) {Γ : List w.ValueSort} :
    Env (μ.pull ρ) Γ →𝒄 Env ρ (Γ.map μ.sort) :=
  ScopedDomain.Env.reindex _ _ μ.sort (fun s => Scheme.domain_subst s μ.parameters ρ.val)

/-- Parameter transport retains every value at its original binding position. -/
theorem parameters_related {w z : Scope} (μ : Scope.Map w z)
    (ρ : z.Assignment) {Γ : List w.ValueSort} (η : Env (μ.pull ρ) Γ) :
    ScopedDomain.Env.Pointwise η (parameters μ ρ η) := by
  apply ScopedDomain.Env.Pointwise.reindex_right
  exact ScopedDomain.Env.pointwise_refl η

/-- Identity context normalization preserves positional semantic correspondence. -/
theorem same_pointwise {w z : Scope} {σ : w.Assignment} {ρ : z.Assignment}
    {Γ : List w.ValueSort} {Δ : List z.ValueSort} {η : Env σ Γ} {ζ : Env ρ Δ}
    (h : ScopedDomain.Env.Pointwise η ζ) :
    ScopedDomain.Env.Pointwise (same σ η) (same ρ ζ) := by
  apply ScopedDomain.Env.Pointwise.reindex_right
  exact fun {_ _} x y he => ScopedDomain.Env.Pointwise.reindex_left h _ _ x y he

/-- Entering numeric binders retains existing values without forcing them. -/
theorem enterNum_pointwise {w z : Scope} {σ : w.Assignment} {ρ : z.Assignment}
    {Γ : List w.ValueSort} {Δ : List z.ValueSort} {η : Env σ Γ} {ζ : Env ρ Δ}
    (h : ScopedDomain.Env.Pointwise η ζ) (l k : Length) :
    ScopedDomain.Env.Pointwise (enterNum σ l η) (enterNum ρ k ζ) := by
  apply ScopedDomain.Env.Pointwise.reindex_right
  exact fun {_ _} x y he => ScopedDomain.Env.Pointwise.reindex_left h _ _ x y he

/-- Entering type binders retains existing values without forcing them. -/
theorem enterType_pointwise {w z : Scope} {σ : w.Assignment} {ρ : z.Assignment}
    {Γ : List w.ValueSort} {Δ : List z.ValueSort} {η : Env σ Γ} {ζ : Env ρ Δ}
    (h : ScopedDomain.Env.Pointwise η ζ) (a b : ClosedTy) :
    ScopedDomain.Env.Pointwise (enterType σ a η) (enterType ρ b ζ) := by
  apply ScopedDomain.Env.Pointwise.reindex_right
  exact fun {_ _} x y he => ScopedDomain.Env.Pointwise.reindex_left h _ _ x y he
end Env

namespace Scheme

/-- Parameter substitution preserves errors at every ordered quantifier stage. -/
theorem error_subst_heq {n v m u : Nat} (μ : ParameterSubstitution n v m u)
    (ρ : ParameterAssignment m u) (s : Scheme n v) (e : EvalError) :
    HEq ((s.subst μ).error ρ e) (s.error (ρ.pull μ) e) := by
  induction s generalizing m u with
  | mono a =>
    dsimp only [subst, error]
    have h := ParameterAssignment.apply_subst ρ μ a
    exact error_mono_heq h e
  | allNum s ih =>
    dsimp only [subst, error]
    apply result_error_heq (e := e)
    exact congrArg (fun D : Length → PointedDomain => (l : Length) → D l)
      (funext (fun l => (domain_subst s μ.liftNum (ρ.extendNum l)).trans
        (congrArg (domain s) (ParameterAssignment.pull_liftNum ρ μ l))))
  | allType s ih =>
    dsimp only [subst, error]
    apply result_error_heq (e := e)
    exact congrArg (fun D : ClosedTy → PointedDomain => (a : ClosedTy) → D a)
      (funext (fun a => (domain_subst s μ.liftType (ρ.extendType a)).trans
        (congrArg (domain s) (ParameterAssignment.pull_liftType ρ μ a))))
  | guard c s ih =>
    dsimp only [subst, error]
    apply guard_heq (propext (Constraint.holds_subst c μ.numbers ρ.numbers))
      (domain_subst s μ ρ)
    exact ih μ ρ
where
  result_error_heq {α β : Type} (h : α = β) (e : EvalError) :
      HEq (DomainResult.error e : DomainResult EvalError α)
        (DomainResult.error e : DomainResult EvalError β) := by
    cases h
    rfl
  guard_heq {P Q : Prop} {D E : PointedDomain} (hp : P = Q) (hd : D = E)
      {x : D} {y : E} (h : HEq x y) :
      HEq (fun _ : PLift P => x) (fun _ : PLift Q => y) := by
    cases hp
    cases hd
    cases eq_of_heq h
    rfl
  error_mono_heq {a b : ClosedTy} (h : a = b) (e : EvalError) :
      HEq (DomainResult.error e : Computation a) (DomainResult.error e : Computation b) := by
    cases h
    rfl

private theorem family_apply_heq {I : Type} {D E : I → PointedDomain}
    (hD : ∀ i, D i = E i) (errD : ∀ i, EvalError → D i) (errE : ∀ i, EvalError → E i)
    (he : ∀ i e, HEq (errD i e) (errE i e)) {i j : I} (hi : i = j)
    {x : DomainResult EvalError ((i : I) → D i)}
    {y : DomainResult EvalError ((i : I) → E i)} (hxy : HEq x y) :
    HEq (DomainResult.elim (errD i) (.ofFun (fun f => f i)) x)
      (DomainResult.elim (errE j) (.ofFun (fun f => f j)) y) := by
  cases hi
  cases funext hD
  cases eq_of_heq hxy
  induction x using DomainResult.inductionOn with
  | bot => rfl
  | error e => exact he i e
  | value f => rfl

/-- Numeric instantiation preserves semantic correspondence across parameter substitution. -/
theorem applyNum_subst_heq {n v m u : Nat} (μ : ParameterSubstitution n v m u)
    (ρ : ParameterAssignment m u) (s : Scheme (n + 1) v) (a : NumExpr n)
    {x : (s.subst μ.liftNum).allNum.Meaning ρ} {y : s.allNum.Meaning (ρ.pull μ)}
    (hxy : HEq x y) :
    HEq ((s.subst μ.liftNum).applyNum (a.subst μ.numbers) ρ x)
      (s.applyNum a (ρ.pull μ) y) := by
  change HEq (PointedDomain.cast _ _) (PointedDomain.cast _ _)
  apply (PointedDomain.cast_heq _ _).trans
  apply HEq.trans ?_ (PointedDomain.cast_heq (domain_singleNum s a (ρ.pull μ)).symm _).symm
  apply family_apply_heq
    (D := fun l => (s.subst μ.liftNum).domain (ρ.extendNum l))
    (E := fun l => s.domain ((ρ.pull μ).extendNum l))
    (fun l => (domain_subst _ _ _).trans
      (congrArg s.domain (ParameterAssignment.pull_liftNum ρ μ l)))
    (fun l => (s.subst μ.liftNum).error (ρ.extendNum l))
    (fun l => s.error ((ρ.pull μ).extendNum l)) ?_
    (NumExpr.eval_subst a μ.numbers ρ.numbers) hxy
  intro l e
  exact (error_subst_heq μ.liftNum (ρ.extendNum l) s e).trans
    (congr_arg_heq (fun ρ => s.error ρ e) (ParameterAssignment.pull_liftNum ρ μ l))

/-- Type instantiation preserves semantic correspondence across parameter substitution. -/
theorem applyType_subst_heq {n v m u : Nat} (μ : ParameterSubstitution n v m u)
    (ρ : ParameterAssignment m u) (s : Scheme n (v + 1)) (a : PolyTy n v)
    {x : (s.subst μ.liftType).allType.Meaning ρ} {y : s.allType.Meaning (ρ.pull μ)}
    (hxy : HEq x y) :
    HEq ((s.subst μ.liftType).applyType (μ.apply a) ρ x)
      (s.applyType a (ρ.pull μ) y) := by
  change HEq (PointedDomain.cast _ _) (PointedDomain.cast _ _)
  apply (PointedDomain.cast_heq _ _).trans
  apply HEq.trans ?_ (PointedDomain.cast_heq (domain_singleType s a (ρ.pull μ)).symm _).symm
  apply family_apply_heq
    (D := fun a => (s.subst μ.liftType).domain (ρ.extendType a))
    (E := fun a => s.domain ((ρ.pull μ).extendType a))
    (fun a => (domain_subst _ _ _).trans
      (congrArg s.domain (ParameterAssignment.pull_liftType ρ μ a)))
    (fun a => (s.subst μ.liftType).error (ρ.extendType a))
    (fun a => s.error ((ρ.pull μ).extendType a)) ?_
    (ParameterAssignment.apply_subst ρ μ a) hxy
  intro a e
  exact (error_subst_heq μ.liftType (ρ.extendType a) s e).trans
    (congr_arg_heq (fun ρ => s.error ρ e) (ParameterAssignment.pull_liftType ρ μ a))

/-- Parameter substitution preserves lazy conditional selection and failure. -/
theorem conditional_subst_heq {n v m u : Nat} (μ : ParameterSubstitution n v m u)
    (ρ : ParameterAssignment m u) (s : Scheme n v)
    {x y : (s.subst μ).Meaning ρ} {x' y' : s.Meaning (ρ.pull μ)}
    (hx : HEq x x') (hy : HEq y y') {p q : Computation .bit} (hp : HEq p q) :
    HEq ((s.subst μ).conditional ρ (x, y) p) (s.conditional (ρ.pull μ) (x', y') q) := by
  cases eq_of_heq hp
  induction p using DomainResult.inductionOn with
  | bot =>
    exact (PointedDomain.cast_heq (domain_subst s μ ρ) ⊥).symm.trans
      (heq_of_eq (PointedDomain.cast_bot _))
  | error e => exact error_subst_heq μ ρ s e
  | value b => cases b with | mk b => cases b <;> assumption

end Scheme

/-- Closed-type transport retains the underlying partial computation. -/
theorem castComputation_heq {a b : ClosedTy} (h : a = b) (x : Computation a) :
    HEq (castComputation h x) x := PointedDomain.cast_heq _ _

/-- Finite-word semantics is independent of transported finiteness evidence. -/
theorem wordLogic_parameters_heq {w z : Scope} (μ : Scope.Map w z)
    (l : NumExpr w.numbers) (op : BitOp) (valid : w.Entails (.fin l)) (ρ : z.Assignment) :
    HEq (wordLogic (l.subst μ.parameters.numbers) op (μ.entails valid) ρ)
      (wordLogic l op valid (μ.pull ρ)) := by
  have hn : Classical.choose (μ.entails valid ρ) = Classical.choose (valid (μ.pull ρ)) :=
    Length.finite.inj ((Classical.choose_spec (μ.entails valid ρ)).symm.trans
      ((NumExpr.eval_subst l μ.parameters.numbers ρ.val.numbers).trans
        (Classical.choose_spec (valid (μ.pull ρ)))))
  unfold wordLogic
  dsimp only
  apply (castComputation_heq _ _).trans
  apply HEq.trans ?_ (castComputation_heq _ _).symm
  exact congr_arg_heq (fun n => (Primitive.wordLogic n op).denote) hn

/-- Context and result annotation transports preserve a term's denotation. -/
theorem Term.denote_cast_heq {w : Scope} {Γ Δ : List w.ValueSort} {s t : w.ValueSort}
    (hΓ : Γ = Δ) (hs : s = t) (e : Term w Γ s) (ρ : w.Assignment) (η : Env ρ Δ) :
    HEq (Term.denote (e.cast hΓ hs) ρ η) (e.denote ρ (hΓ.symm ▸ η)) := by
  cases hΓ
  cases hs
  rfl

end Interop.Cryptol.Polymorphic
