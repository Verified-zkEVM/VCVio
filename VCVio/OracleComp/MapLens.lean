/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Transporting oracle computations along polynomial lenses

A lens `l : PFunctor.Lens spec.toPFunctor spec'.toPFunctor` sends each `spec`-query `t` to the
`spec'`-query `l.toFunA t` and translates each answer back by `l.toFunB t`. This file defines
the action of such a lens on oracle computations, `OracleComp.mapLens`, as PolyFun's
`PFunctor.FreeM.mapLens`, and proves:

* the monad-morphism and functoriality laws `mapLens_pure`, `mapLens_bind`, `mapLens_map`,
  `mapLens_id`, `mapLens_mapLens`, and the action `mapLens_liftM_query` on a single query;
* `simulateQ_mapLens`: simulating a transported computation with `impl` is simulating the
  original with the pulled-back handler `impl.comapLens l`, and `mapLens_eq_simulateQ`, which
  expresses `mapLens` itself as a simulation;
* `liftComp_eq_mapLens`: the lift along a sub-spec inclusion `h : spec ⊂ₒ superSpec` is
  `mapLens h.toLens`, with the summand inclusions into `spec₁ + spec₂` as instances;
* `IsQueryBound.mapLens`, `IsTotalQueryBound.mapLens`, `IsQueryBoundP.mapLens`: a query bound
  on a computation, read through the lens, bounds the transported computation, since each query
  is sent to exactly one query.
-/

public section

universe u u' u'' v w

open OracleSpec PFunctor

open scoped PFunctor

namespace OracleComp

section mapLens

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  {spec : OracleSpec.{u, v} ι} {spec' : OracleSpec.{u', v} ι'}
  {spec'' : OracleSpec.{u'', v} ι''} {α β : Type w}

/-- Transport an oracle computation along a polynomial lens: each query `t` to `spec` is
replaced by the query `l.toFunA t` to `spec'`, whose answer is translated back by
`l.toFunB t`. -/
@[expose]
def mapLens (l : Lens spec.toPFunctor spec'.toPFunctor) (oa : OracleComp spec α) :
    OracleComp spec' α :=
  FreeM.mapLens l oa

/-- Transport along a lens fixes `pure`. -/
@[simp]
lemma mapLens_pure (l : Lens spec.toPFunctor spec'.toPFunctor) (x : α) :
    (pure x : OracleComp spec α).mapLens l = pure x :=
  FreeM.mapLens_pure l x

/-- Transport along a lens on a query node: the query is relabelled forward and each answer of
the new query is translated back before entering the continuation. -/
lemma mapLens_queryBind (l : Lens spec.toPFunctor spec'.toPFunctor) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    (queryBind t k).mapLens l = queryBind (l.toFunA t) fun d => (k (l.toFunB t d)).mapLens l :=
  FreeM.mapLens_liftBind l t k

/-- Transport along a lens commutes with `bind`. -/
@[simp]
lemma mapLens_bind (l : Lens spec.toPFunctor spec'.toPFunctor) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) :
    (oa >>= f).mapLens l = oa.mapLens l >>= fun a => (f a).mapLens l :=
  FreeM.mapLens_bind' l oa f

/-- Transport along a lens commutes with `map`. -/
@[simp]
lemma mapLens_map (l : Lens spec.toPFunctor spec'.toPFunctor) (f : α → β)
    (oa : OracleComp spec α) :
    (f <$> oa).mapLens l = f <$> oa.mapLens l :=
  FreeM.mapLens_map l f oa

/-- Transport along the identity lens is the identity. -/
@[simp]
lemma mapLens_id (oa : OracleComp spec α) :
    oa.mapLens (Lens.id spec.toPFunctor) = oa :=
  FreeM.mapLens_id oa

/-- Transport along two lenses in turn is transport along their composite. -/
@[simp]
lemma mapLens_mapLens (l₂ : Lens spec'.toPFunctor spec''.toPFunctor)
    (l₁ : Lens spec.toPFunctor spec'.toPFunctor) (oa : OracleComp spec α) :
    (oa.mapLens l₁).mapLens l₂ = oa.mapLens (l₂ ∘ₗ l₁) :=
  FreeM.mapLens_mapLens l₂ l₁ oa

/-- A single query `t` is transported to the query `l.toFunA t`, its answer mapped back by
`l.toFunB t`. -/
@[simp]
lemma mapLens_liftM_query {spec : OracleSpec.{u, w} ι} {spec' : OracleSpec.{u', w} ι'}
    (l : Lens spec.toPFunctor spec'.toPFunctor) (t : spec.Domain) :
    (liftM (spec.query t) : OracleComp spec (spec.Range t)).mapLens l =
      l.toFunB t <$> (liftM (spec'.query (l.toFunA t)) : OracleComp spec' _) :=
  rfl

end mapLens

end OracleComp

namespace QueryImpl

variable {ι : Type u} {ι' : Type u'} {spec : OracleSpec.{u, v} ι}
  {spec' : OracleSpec.{u', v} ι'} {m : Type v → Type w}

/-- Pull a handler for `spec'` back along a lens into `spec'`: a `spec`-query `t` is answered by
`impl (l.toFunA t)`, mapped by `l.toFunB t`. -/
@[expose]
def comapLens [Functor m] (impl : QueryImpl spec' m) (l : Lens spec.toPFunctor spec'.toPFunctor) :
    QueryImpl spec m :=
  fun t => l.toFunB t <$> impl (l.toFunA t)

/-- The pulled-back handler at a query `t`. -/
@[simp]
lemma comapLens_apply [Functor m] (impl : QueryImpl spec' m)
    (l : Lens spec.toPFunctor spec'.toPFunctor) (t : spec.Domain) :
    impl.comapLens l t = l.toFunB t <$> impl (l.toFunA t) := rfl

/-- Pulling a handler back along the identity lens returns the handler. -/
@[simp]
lemma comapLens_id [Functor m] [LawfulFunctor m] (impl : QueryImpl spec m) :
    impl.comapLens (Lens.id spec.toPFunctor) = impl := by
  grind only [comapLens_apply, id_map']

end QueryImpl

namespace OracleComp

section simulateQ

variable {ι : Type u} {ι' : Type u'} {spec : OracleSpec.{u, v} ι}
  {spec' : OracleSpec.{u', v} ι'} {m : Type v → Type w} [Monad m] [LawfulMonad m] {α : Type v}

/-- Simulating a transported computation with `impl` is simulating the original computation
with the handler pulled back along the lens. -/
theorem simulateQ_mapLens (impl : QueryImpl spec' m) (l : Lens spec.toPFunctor spec'.toPFunctor)
    (oa : OracleComp spec α) :
    simulateQ impl (oa.mapLens l) = simulateQ (impl.comapLens l) oa :=
  FreeM.liftM_mapLens l impl oa

/-- Transport along a lens is the simulation that answers each query `t` by the query
`l.toFunA t`, mapped back by `l.toFunB t`. -/
theorem mapLens_eq_simulateQ (l : Lens spec.toPFunctor spec'.toPFunctor)
    (oa : OracleComp spec α) :
    oa.mapLens l = simulateQ ((QueryImpl.id' spec').comapLens l) oa := by
  rw [← simulateQ_mapLens, simulateQ_id']

end simulateQ

section liftComp

variable {ι : Type u} {τ : Type u'} {spec : OracleSpec.{u, w} ι} {superSpec : OracleSpec.{u', w} τ}
  {α : Type w}

/-- Lifting a computation along a sub-spec inclusion is transport along the inclusion's lens. -/
theorem liftComp_eq_mapLens [h : spec ⊂ₒ superSpec] (mx : OracleComp spec α) :
    liftComp mx superSpec = mx.mapLens h.toLens := by
  rw [mapLens_eq_simulateQ, liftComp_def]
  congr 1
  funext t
  have e : (liftM (spec.query t) : OracleQuery superSpec _) =
      ⟨h.onQuery t, h.onResponse t⟩ :=
    SubSpec.liftM_eq_lift (self := h) _
  rw [liftM_eq_liftM_liftM (superSpec := superSpec), e]
  rfl

variable {ι₁ : Type u} {ι₂ : Type u'} {spec₁ : OracleSpec.{u, w} ι₁}
  {spec₂ : OracleSpec.{u', w} ι₂}

/-- Lifting a computation into the left summand of `spec₁ + spec₂` is transport along the
inclusion lens `Sum.inl`. -/
theorem liftComp_add_left_eq_mapLens (mx : OracleComp spec₁ α) :
    liftComp mx (spec₁ + spec₂) = mx.mapLens (Sum.inl ⇆ fun _ => id) :=
  liftComp_eq_mapLens mx

/-- Lifting a computation into the right summand of `spec₁ + spec₂` is transport along the
inclusion lens `Sum.inr`. -/
theorem liftComp_add_right_eq_mapLens (mx : OracleComp spec₂ α) :
    liftComp mx (spec₁ + spec₂) = mx.mapLens (Sum.inr ⇆ fun _ => id) :=
  liftComp_eq_mapLens mx

end liftComp

section queryBound

variable {ι ι' : Type u} {spec : OracleSpec.{u, u} ι} {spec' : OracleSpec.{u, u} ι'}
  {α : Type u} {B : Type*}

/-- A query bound on `oa`, with validity check and cost read through the lens, bounds
`oa.mapLens l`. -/
theorem IsQueryBound.mapLens (l : Lens spec.toPFunctor spec'.toPFunctor)
    {canQuery : ι' → B → Prop} {cost : ι' → B → B} :
    ∀ (oa : OracleComp spec α) {b : B},
      oa.IsQueryBound b (fun t => canQuery (l.toFunA t)) (fun t => cost (l.toFunA t)) →
      (oa.mapLens l).IsQueryBound b canQuery cost
  | .pure _, _, _ => trivial
  | .liftBind a rest, _, h =>
      ⟨h.1, fun d => IsQueryBound.mapLens l (rest (l.toFunB a d)) (h.2 (l.toFunB a d))⟩

/-- Transport along a lens preserves a total query bound. -/
theorem IsTotalQueryBound.mapLens (l : Lens spec.toPFunctor spec'.toPFunctor)
    {oa : OracleComp spec α} {n : ℕ} (h : oa.IsTotalQueryBound n) :
    (oa.mapLens l).IsTotalQueryBound n :=
  IsQueryBound.mapLens l oa h

/-- A bound on the queries satisfying `p ∘ l.toFunA` bounds the queries of the transported
computation satisfying `p`. -/
theorem IsQueryBoundP.mapLens (l : Lens spec.toPFunctor spec'.toPFunctor) {p : ι' → Prop}
    [DecidablePred p] {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP (fun t => p (l.toFunA t)) n) :
    (oa.mapLens l).IsQueryBoundP p n :=
  IsQueryBound.mapLens l oa h

end queryBound

end OracleComp
