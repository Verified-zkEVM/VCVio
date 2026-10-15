/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyParameterDomain

/-!
# Semantic preservation of parameter substitution

Constructor compatibility lifts to every finite polymorphic term. The result
compares arbitrary partial environments, including fixed points of heterogeneous
recursive groups, and retains all numeric, type and erased proof stages.
-/

public section

open OmegaCompletePartialOrder IPFunctor

namespace Interop.Cryptol.Polymorphic

private theorem proof_heq {P Q : Prop} {D E : PointedDomain} (hp : P = Q) (hd : D = E)
    (f : PLift P → D) (g : PLift Q → E) (h : ∀ p q, HEq (f p) (g q)) : HEq f g := by
  cases hp
  cases hd
  exact heq_of_eq (funext (fun p => eq_of_heq (h p p)))

private theorem proof_apply_heq {P Q : Prop} {D E : PointedDomain}
    (hp : P = Q) (hd : D = E) {f : PLift P → D} {g : PLift Q → E}
    (h : HEq f g) (p : PLift P) (q : PLift Q) : HEq (f p) (g q) := by
  cases hp
  cases hd
  cases eq_of_heq h
  exact heq_of_eq (congrArg f (Subsingleton.elim p q))

private theorem unary_heq {I : Type} {A B : I → Type} (f : (i : I) → A i → B i)
    {i j : I} (h : i = j) {x : A i} {y : A j} (hx : HEq x y) : HEq (f i x) (f j y) := by
  cases h
  cases eq_of_heq hx
  rfl

private theorem binary_heq {I : Type} {A B C : I → Type}
    (f : (i : I) → A i → B i → C i) {i j : I} (h : i = j)
    {x : A i} {y : A j} {a : B i} {b : B j} (hx : HEq x y) (ha : HEq a b) :
    HEq (f i x a) (f j y b) := by
  cases h
  cases eq_of_heq hx
  cases eq_of_heq ha
  rfl

private theorem lam_heq {a b c d : ClosedTy} (ha : a = c) (hb : b = d)
    (f : Computation a →𝒄 Computation b) (g : Computation c →𝒄 Computation d)
    (h : ∀ x y, HEq x y → HEq (f x) (g y)) :
    HEq (DomainResult.value f : Computation (.arrow a b))
      (DomainResult.value g : Computation (.arrow c d)) := by
  cases ha
  cases hb
  apply heq_of_eq
  congr 1
  apply ContinuousHom.ext
  intro x
  exact eq_of_heq (h x x HEq.rfl)

private theorem generate_heq {l k : Length} {a b : ClosedTy} (hl : l = k) (ha : a = b)
    (f : l.Index → Computation a) (g : k.Index → Computation b)
    (h : ∀ i j, HEq i j → HEq (f i) (g j)) :
    HEq (DomainResult.value f : Computation (.seq l a))
      (DomainResult.value g : Computation (.seq k b)) := by
  cases hl
  cases ha
  apply heq_of_eq
  congr 1
  funext i
  exact eq_of_heq (h i i HEq.rfl)

set_option maxHeartbeats 1500000 in
-- The constructor cases elaborate dependent transports between ordered semantic domains.
/-- Every constructor preserves denotation under checked parameter substitution. -/
theorem denoteOp_parameters {w z : Scope} (μ : Scope.Map w z)
    (Γ : List w.ValueSort) {s : w.ValueSort} (op : Op w s)
    (next : (p : Fin op.arity) → (ρ : (op.world p).Assignment) →
      Env ρ (op.binders p ++ Γ.map (op.reindex p)) →𝒄 (op.sort p).Meaning ρ.val)
    (mapped : (p : Fin (op.mapHead μ).2.arity) →
      (ρ : ((op.mapHead μ).2.world p).Assignment) →
      Env ρ ((op.mapHead μ).2.binders p ++ (Γ.map μ.sort).map ((op.mapHead μ).2.reindex p)) →𝒄
        ((op.mapHead μ).2.sort p).Meaning ρ.val)
    (ih : ∀ (p : Fin (op.mapHead μ).2.arity)
      (ρ : ((op.mapHead μ).2.world p).Assignment)
      (σ : (op.world (p.cast (op.mapHead_arity μ))).Assignment),
      σ.val = ρ.val.pull (op.childMap μ p).parameters →
      ∀ η ζ, ScopedDomain.Env.Pointwise η ζ →
        HEq (mapped p ρ ζ) (next (p.cast (op.mapHead_arity μ)) σ η))
    (ρ : z.Assignment) (σ : w.Assignment) (hρ : σ.val = ρ.val.pull μ.parameters)
    (η : Env σ Γ) (ζ : Env ρ (Γ.map μ.sort)) (hη : ScopedDomain.Env.Pointwise η ζ) :
    HEq (denoteOp (Γ.map μ.sort) (op.mapHead μ).2 mapped ρ ζ)
      (denoteOp Γ op next σ η) := by
  have hs : σ = μ.pull ρ := Subtype.ext hρ
  subst σ
  have hsame : ScopedDomain.Env.Pointwise (Env.same (μ.pull ρ) η) (Env.same ρ ζ) :=
    Env.same_pointwise hη
  cases op <;>
    dsimp only [Op.mapHead, Op.arity, Op.world, Op.binders, Op.reindex, Op.sort,
      Op.childMap, List.nil_append] at next mapped ih ⊢ <;>
    dsimp only [denoteOp, ContinuousHom.comp_apply, ContinuousHom.ofFun_apply,
      ContinuousHom.const_apply] <;> try rfl
  case error e => exact Scheme.error_subst_heq μ.parameters ρ.val s e
  case numApp body a =>
    change HEq ((body.subst μ.parameters.liftNum).applyNum
      (a.subst μ.parameters.numbers) ρ.val ((mapped 0 ρ).toFun (Env.same ρ ζ)))
      (body.applyNum a (μ.pull ρ).val ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact Scheme.applyNum_subst_heq μ.parameters ρ.val body a
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame)
  case typeApp body a =>
    change HEq ((body.subst μ.parameters.liftType).applyType
      (μ.parameters.apply a) ρ.val ((mapped 0 ρ).toFun (Env.same ρ ζ)))
      (body.applyType a (μ.pull ρ).val ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact Scheme.applyType_subst_heq μ.parameters ρ.val body a
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame)
  case ite =>
    change HEq ((s.subst μ.parameters).conditional ρ.val
      ((mapped 1 ρ).toFun (Env.same ρ ζ), (mapped 2 ρ).toFun (Env.same ρ ζ))
      ((mapped 0 ρ).toFun (Env.same ρ ζ)))
      (s.conditional (μ.pull ρ).val
        ((next 1 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η),
          (next 2 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η))
        ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact Scheme.conditional_subst_heq μ.parameters ρ.val s
      (ih 1 ρ (μ.pull ρ) rfl _ _ hsame) (ih 2 ρ (μ.pull ρ) rfl _ _ hsame)
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame)
  case numAbs body =>
    change HEq (DomainResult.value (fun l => (mapped 0 (ρ.extendNum l)).toFun
      (Env.enterNum ρ l ζ)))
      (DomainResult.value (fun l => (next 0 ((μ.pull ρ).extendNum l)).toFun
        (Env.enterNum (μ.pull ρ) l η)))
    have hd (l : Length) : (body.subst μ.parameters.liftNum).domain (ρ.val.extendNum l) =
        body.domain ((ρ.val.pull μ.parameters).extendNum l) :=
      (Scheme.domain_subst _ _ _).trans
        (congrArg body.domain (ParameterAssignment.pull_liftNum ρ.val μ.parameters l))
    apply PointedDomain.result_value_heq (congrArg (PointedDomain.pi Length) (funext hd))
    apply PointedDomain.pi_heq hd
    intro l
    exact ih 0 (ρ.extendNum l) ((μ.pull ρ).extendNum l)
      (ParameterAssignment.pull_liftNum ρ.val μ.parameters l).symm _ _
      (Env.enterNum_pointwise hη l l)
  case typeAbs body =>
    change HEq (DomainResult.value (fun a => (mapped 0 (ρ.extendType a)).toFun
      (Env.enterType ρ a ζ)))
      (DomainResult.value (fun a => (next 0 ((μ.pull ρ).extendType a)).toFun
        (Env.enterType (μ.pull ρ) a η)))
    have hd (a : ClosedTy) : (body.subst μ.parameters.liftType).domain (ρ.val.extendType a) =
        body.domain ((ρ.val.pull μ.parameters).extendType a) :=
      (Scheme.domain_subst _ _ _).trans
        (congrArg body.domain (ParameterAssignment.pull_liftType ρ.val μ.parameters a))
    apply PointedDomain.result_value_heq (congrArg (PointedDomain.pi ClosedTy) (funext hd))
    apply PointedDomain.pi_heq hd
    intro a
    exact ih 0 (ρ.extendType a) ((μ.pull ρ).extendType a)
      (ParameterAssignment.pull_liftType ρ.val μ.parameters a).symm _ _
      (Env.enterType_pointwise hη a a)
  case proofAbs c body =>
    change HEq (fun h => (mapped 0 (ρ.assume h.down)).toFun (Env.assume ρ h.down ζ))
      (fun h => (next 0 ((μ.pull ρ).assume h.down)).toFun (Env.assume (μ.pull ρ) h.down η))
    apply proof_heq (propext (Constraint.holds_subst c μ.parameters.numbers ρ.val.numbers))
      (Scheme.domain_subst body μ.parameters ρ.val)
    intro p q
    exact ih 0 (ρ.assume p.down) ((μ.pull ρ).assume q.down) rfl _ _ hsame
  case proofApp c valid =>
    change HEq (((mapped 0 ρ).toFun (Env.same ρ ζ)) ⟨_⟩)
      (((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)) ⟨_⟩)
    exact proof_apply_heq (propext (Constraint.holds_subst c μ.parameters.numbers ρ.val.numbers))
      (Scheme.domain_subst s μ.parameters ρ.val)
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame) _ _
  case lam a b =>
    change HEq (DomainResult.value _) (DomainResult.value _)
    apply lam_heq (ParameterAssignment.apply_subst ρ.val μ.parameters a)
      (ParameterAssignment.apply_subst ρ.val μ.parameters b)
    intro x y he
    change HEq ((mapped 0 ρ).toFun (Env.cons ρ (Env.same ρ ζ, x)))
      ((next 0 (μ.pull ρ)).toFun (Env.cons (μ.pull ρ) (Env.same (μ.pull ρ) η, y)))
    apply ih 0 ρ (μ.pull ρ) rfl
    exact fun {_ _} v w hv => ScopedDomain.Env.Pointwise.cons hsame he.symm v w hv
  case fix =>
    change HEq (ContinuousHom.fix _) (ContinuousHom.fix _)
    apply PointedDomain.fix_heq (Scheme.domain_subst s μ.parameters ρ.val)
    intro x y he
    change HEq ((mapped 0 ρ).toFun (Env.cons ρ (Env.same ρ ζ, x)))
      ((next 0 (μ.pull ρ)).toFun (Env.cons (μ.pull ρ) (Env.same (μ.pull ρ) η, y)))
    apply ih 0 ρ (μ.pull ρ) rfl
    exact fun {_ _} v w hv => ScopedDomain.Env.Pointwise.cons hsame he.symm v w hv
  case app a b =>
    change HEq (DomainResult.applyContinuous ((mapped 0 ρ).toFun (Env.same ρ ζ))
      ((mapped 1 ρ).toFun (Env.same ρ ζ)))
      (DomainResult.applyContinuous ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η))
        ((next 1 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact binary_heq
      (A := fun p : ClosedTy × ClosedTy => Computation (.arrow p.1 p.2))
      (B := fun p => Computation p.1) (C := fun p => Computation p.2)
      (fun _ f x => DomainResult.applyContinuous f x)
      (i := (ρ.val.apply (μ.parameters.apply a), ρ.val.apply (μ.parameters.apply b)))
      (j := ((μ.pull ρ).val.apply a, (μ.pull ρ).val.apply b))
      (Prod.ext (ParameterAssignment.apply_subst ρ.val μ.parameters a)
        (ParameterAssignment.apply_subst ρ.val μ.parameters b))
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame) (ih 1 ρ (μ.pull ρ) rfl _ _ hsame)
  case pair a b =>
    change HEq (DomainResult.value ((mapped 0 ρ).toFun (Env.same ρ ζ),
      (mapped 1 ρ).toFun (Env.same ρ ζ)))
      (DomainResult.value ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η),
        (next 1 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact binary_heq (A := fun p : ClosedTy × ClosedTy => Computation p.1)
      (B := fun p => Computation p.2) (C := fun p => Computation (.prod p.1 p.2))
      (fun _ x y => DomainResult.value (x, y))
      (i := (ρ.val.apply (μ.parameters.apply a), ρ.val.apply (μ.parameters.apply b)))
      (j := ((μ.pull ρ).val.apply a, (μ.pull ρ).val.apply b))
      (Prod.ext (ParameterAssignment.apply_subst ρ.val μ.parameters a)
        (ParameterAssignment.apply_subst ρ.val μ.parameters b))
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame) (ih 1 ρ (μ.pull ρ) rfl _ _ hsame)
  case fst a b =>
    change HEq (DomainResult.bind (.ofFun Prod.fst) ((mapped 0 ρ).toFun (Env.same ρ ζ)))
      (DomainResult.bind (.ofFun Prod.fst) ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact unary_heq (A := fun p : ClosedTy × ClosedTy => Computation (.prod p.1 p.2))
      (B := fun p => Computation p.1) (fun _ x => DomainResult.bind (.ofFun Prod.fst) x)
      (i := (ρ.val.apply (μ.parameters.apply a), ρ.val.apply (μ.parameters.apply b)))
      (j := ((μ.pull ρ).val.apply a, (μ.pull ρ).val.apply b))
      (Prod.ext (ParameterAssignment.apply_subst ρ.val μ.parameters a)
        (ParameterAssignment.apply_subst ρ.val μ.parameters b))
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame)
  case snd a b =>
    change HEq (DomainResult.bind (.ofFun Prod.snd) ((mapped 0 ρ).toFun (Env.same ρ ζ)))
      (DomainResult.bind (.ofFun Prod.snd) ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact unary_heq (A := fun p : ClosedTy × ClosedTy => Computation (.prod p.1 p.2))
      (B := fun p => Computation p.2) (fun _ x => DomainResult.bind (.ofFun Prod.snd) x)
      (i := (ρ.val.apply (μ.parameters.apply a), ρ.val.apply (μ.parameters.apply b)))
      (j := ((μ.pull ρ).val.apply a, (μ.pull ρ).val.apply b))
      (Prod.ext (ParameterAssignment.apply_subst ρ.val μ.parameters a)
        (ParameterAssignment.apply_subst ρ.val μ.parameters b))
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame)
  case index l a =>
    change HEq (Semantics.index ((mapped 0 ρ).toFun (Env.same ρ ζ))
      ((mapped 1 ρ).toFun (Env.same ρ ζ)))
      (Semantics.index ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η))
        ((next 1 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    exact binary_heq (A := fun p : Length × ClosedTy => Computation (.seq p.1 p.2))
      (B := fun _ => Computation .integer) (C := fun p => Computation p.2)
      (fun _ x y => Semantics.index x y)
      (i := ((l.subst μ.parameters.numbers).eval ρ.val.numbers, ρ.val.apply (μ.parameters.apply a)))
      (j := (l.eval (μ.pull ρ).val.numbers, (μ.pull ρ).val.apply a))
      (Prod.ext (NumExpr.eval_subst l μ.parameters.numbers ρ.val.numbers)
        (ParameterAssignment.apply_subst ρ.val μ.parameters a))
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame) (ih 1 ρ (μ.pull ρ) rfl _ _ hsame)
  case generate l a =>
    change HEq (DomainResult.value (fun i => (mapped 0 ρ).toFun
      (Env.cons ρ (Env.same ρ ζ, DomainResult.value ⟨(Length.indexNat i : Int)⟩))))
      (DomainResult.value (fun i => (next 0 (μ.pull ρ)).toFun
        (Env.cons (μ.pull ρ) (Env.same (μ.pull ρ) η,
          DomainResult.value ⟨(Length.indexNat i : Int)⟩))))
    have hl := NumExpr.eval_subst l μ.parameters.numbers ρ.val.numbers
    apply generate_heq hl (ParameterAssignment.apply_subst ρ.val μ.parameters a)
    intro i j he
    apply ih 0 ρ (μ.pull ρ) rfl
    have hn := congr_heq (congr_arg_heq (fun l => @Length.indexNat l) hl) he
    have hv : HEq (DomainResult.value ⟨(Length.indexNat j : Int)⟩ : Computation .integer)
        (DomainResult.value ⟨(Length.indexNat i : Int)⟩ : Computation .integer) := by
      rw [hn]
    exact fun {_ _} x y hxy => ScopedDomain.Env.Pointwise.cons hsame hv x y hxy
  case letE value =>
    change HEq ((mapped 1 ρ).toFun (Env.cons ρ (Env.same ρ ζ,
      (mapped 0 ρ).toFun (Env.same ρ ζ))))
      ((next 1 (μ.pull ρ)).toFun (Env.cons (μ.pull ρ) (Env.same (μ.pull ρ) η,
        (next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η))))
    apply ih 1 ρ (μ.pull ρ) rfl
    exact fun {_ _} x y he => ScopedDomain.Env.Pointwise.cons hsame
      (ih 0 ρ (μ.pull ρ) rfl _ _ hsame).symm x y he
  case bitNot =>
    change HEq (Semantics.bitNot ((mapped 0 ρ).toFun (Env.same ρ ζ)))
      (Semantics.bitNot ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    apply heq_of_eq
    congr 1
    exact eq_of_heq (ih 0 ρ (μ.pull ρ) rfl _ _ hsame)
  case bitOp op | intOp op | intEq | intLt =>
    change HEq (Semantics.binary _ ((mapped 0 ρ).toFun (Env.same ρ ζ))
      ((mapped 1 ρ).toFun (Env.same ρ ζ)))
      (Semantics.binary _ ((next 0 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η))
        ((next 1 (μ.pull ρ)).toFun (Env.same (μ.pull ρ) η)))
    apply heq_of_eq
    congr 1
    · congr 1
      exact eq_of_heq (ih 0 ρ (μ.pull ρ) rfl _ _ hsame)
    · exact eq_of_heq (ih 1 ρ (μ.pull ρ) rfl _ _ hsame)
  case wordLogic l op valid =>
    change HEq (wordLogic (l.subst μ.parameters.numbers) op (μ.entails valid) ρ)
      (wordLogic l op valid (μ.pull ρ))
    exact wordLogic_parameters_heq μ l op valid ρ
  case letRec bindings =>
    let D := fun s : w.ValueSort => s.domain (μ.pull ρ).val
    let E := fun s : z.ValueSort => s.domain ρ.val
    let rhs : (i : Fin bindings.length) → Env (μ.pull ρ) (bindings ++ Γ.map id) →𝒄
        bindings[i].Meaning (μ.pull ρ).val := fun i => next i.succ (μ.pull ρ)
    let rhs' : (j : Fin (bindings.map μ.sort).length) →
        Env ρ (bindings.map μ.sort ++ (Γ.map μ.sort).map id) →𝒄
        (bindings.map μ.sort)[j].Meaning ρ.val := fun j => mapped j.succ ρ
    have hg : ScopedDomain.Env.Pointwise
        (ScopedDomain.Env.fixGroup D rhs (Env.same (μ.pull ρ) η))
        (ScopedDomain.Env.fixGroup E rhs' (Env.same ρ ζ)) := by
      apply ScopedDomain.Env.fixGroup_pointwise μ.sort
        (fun a => Scheme.domain_subst a μ.parameters ρ.val)
      intro ξ ψ hξ i j hij
      have hp : (j.succ.cast (by simp only [List.length_map]) : Fin (bindings.length + 1)) =
          i.succ := Fin.ext (congrArg (· + 1) hij.symm)
      have hen : ScopedDomain.Env.Pointwise
          (Env.append (μ.pull ρ) (ξ, Env.same (μ.pull ρ) η))
          (Env.append ρ (ψ, Env.same ρ ζ)) :=
        ScopedDomain.Env.Pointwise.append (List.length_map μ.sort).symm hξ hsame
      have hh := ih j.succ ρ (μ.pull ρ) rfl _ _ hen
      exact (hh.trans (congr_arg_heq (fun p => (next p (μ.pull ρ)).toFun
        (Env.append (μ.pull ρ) (ξ, Env.same (μ.pull ρ) η))) hp)).symm
    change HEq ((mapped 0 ρ).toFun (Env.append ρ
      (ScopedDomain.Env.fixGroup E rhs' (Env.same ρ ζ), Env.same ρ ζ)))
      ((next 0 (μ.pull ρ)).toFun (Env.append (μ.pull ρ)
        (ScopedDomain.Env.fixGroup D rhs (Env.same (μ.pull ρ) η), Env.same (μ.pull ρ) η)))
    apply ih 0 ρ (μ.pull ρ) rfl
    exact fun {_ _} x y he => ScopedDomain.Env.Pointwise.append
      (List.length_map μ.sort).symm hg hsame x y he
  case closed t =>
    change HEq (castComputation _ (Resolved.denote t Environment.empty))
      (castComputation _ (Resolved.denote t Environment.empty))
    exact (castComputation_heq _ _).trans (castComputation_heq _ _).symm

/-- Parameter substitution preserves denotation in positionally corresponding environments. -/
theorem Term.denote_parameters_related {w z : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (μ : Scope.Map w z) (ρ : z.Assignment) (σ : w.Assignment)
    (hρ : σ.val = ρ.val.pull μ.parameters) (η : Env σ Γ) (ζ : Env ρ (Γ.map μ.sort))
    (hη : ScopedDomain.Env.Pointwise η ζ) :
    HEq ((Term.parameters μ t).denote ρ ζ) (t.denote σ η) := by
  induction t using ScopedFamily.Term.inductionOn generalizing z with
  | hvar w Γ s x =>
    exact (hη x (x.map μ.sort) (ScopedVar.index_map μ.sort x).symm).symm
  | hnode w Γ s head args ih =>
    simp only [Term.parameters, ScopedFamily.Term.map_node]
    rcases head with ⟨⟨sort, op⟩, hs⟩
    cases hs
    change HEq (PointedDomain.cast _ (denoteOp (Γ.map μ.sort) (op.mapHead μ).2 _ ρ ζ))
      (denoteOp Γ op (fun p ρ => Term.denote (args p) ρ) σ η)
    apply (PointedDomain.cast_heq _ _).trans
    apply denoteOp_parameters μ Γ op _ _ ?_ ρ σ hρ η ζ hη
    intro p ρ σ hρ η ζ hη
    apply (Term.denote_cast_heq _ _ _ ρ ζ).trans
    apply ih _ (op.childMap μ p) ρ σ hρ η _
    exact fun {_ _} x y he => ScopedDomain.Env.Pointwise.cast_right _ hη x y he

/-- Parameter substitution preserves denotation for arbitrary partial local environments. -/
theorem Term.denote_parameters {w z : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (μ : Scope.Map w z) (ρ : z.Assignment) (η : Env (μ.pull ρ) Γ) :
    PointedDomain.cast (Scheme.domain_subst s μ.parameters ρ.val)
      ((Term.parameters μ t).denote ρ (Env.parameters μ ρ η)) =
        t.denote (μ.pull ρ) η := by
  apply (PointedDomain.cast_eq_iff _ _ _).mpr
  exact t.denote_parameters_related μ ρ (μ.pull ρ) rfl η (Env.parameters μ ρ η)
    (Env.parameters_related μ ρ η)
end Interop.Cryptol.Polymorphic
