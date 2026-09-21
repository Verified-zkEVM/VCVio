/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Two lazy random oracles are one lazy random oracle on the sum signature

A proof that runs two independently cached lazy random oracles, one for `spec₁` and one for
`spec₂`, may be read as a single run of `(spec₁ + spec₂).randomOracle` on one joint cache.  The
two component caches are paired by `OracleSpec.QueryCache.addEquiv`, and the statements are
equalities of `simulateQ … .run` values: the two runs are the *same* computation up to that
pairing, with no side condition on either signature, on the sampled ranges or on the computation
being simulated.

Three arrangements of the two caches are covered and all three are identified:

* `QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle`, which carries the product
  cache `spec₁.QueryCache × spec₂.QueryCache` as one state
  (`OracleComp.map_run_simulateQ_parallelStateT_randomOracle`);
* `OracleSpec.nestedRandomOracle spec₁ spec₂`, which carries `spec₁`'s cache as the outer state
  of a two-level `StateT` stack over `spec₂`'s (`OracleComp.run_run_simulateQ_nestedRandomOracle`);
* `OracleSpec.nestedRandomOracleSwap spec₁ spec₂`, the same stack the other way round
  (`OracleComp.run_run_simulateQ_nestedRandomOracleSwap`).

The two nesting orders both hold because neither handler reads the other's state: a `spec₁` query
is answered from `spec₁`'s cache alone and a `spec₂` query from `spec₂`'s cache alone, so the
stack order only permutes where an untouched state sits and is removed by
`QueryImpl.flattenStateT`.  Which signature is outermost is therefore free, and a consumer may
place the cache it needs to read at whichever level is convenient.

The `_add_` forms put a stateless private-sampling summand in front of the pair, which is the
shape the fresh-answer engine of `RandomOracle/FreshAnswer.lean` consumes; transporting that
engine's bound along the pairing gives `OracleComp.evalDist_run_parallel_setOf_le_of_fresh_bound`
and `OracleComp.evalDist_run_run_nested_setOf_le_of_fresh_bound`.

## Scope

* The measurable-space arguments of the `𝒟[…] {z | …}` statements are pinned to `⊤` by a `letI`
  inside the statement, exactly as in `RandomOracle/FreshAnswer.lean`, because the engine they
  transport pins them that way.  A consumer must fix `⊤` as well.
* Nothing here is probabilistic beyond transporting a measure along a map: the two fresh-answer
  bounds are the engine's own bound pushed forward along `OracleSpec.QueryCache.addEquiv` and the
  reassociation of a nested state, and every other statement is an equality of computations with
  no measure in sight.  That push-forward loses nothing because it is a preimage computation,
  which is exact for any measurable map; what bijectivity of the pairing buys is that the
  product-side event is exactly the joint-side one rather than a coarsening of it, and that a
  consumer may travel in the other direction as well
  (`OracleComp.map_run_run_simulateQ_nestedRandomOracle`).
* Both delivered bounds leave the cache-size conjunct `QueryCache.enncard … ≤ q` inside the
  measured set, and discharging it from a query budget is not done here;
  `OracleSpec.QueryCache.toSet_addEquiv` and `OracleSpec.QueryCache.enncard_addEquiv` are the
  inputs such a transport would need.
* The sampler on `(spec₁ + spec₂).Range t` is the ambient `SampleableType` instance for a sum of
  specs; no sampler is introduced here, so the `$ᵗ` terms of the engine's hypothesis and of these
  statements are the same term.
* Nothing here is quantum: the handlers are classical lazily-sampled tables.

## Labels

Fifteen declarations.

*The nested handlers*:

* `OracleSpec.nestedRandomOracle`, `OracleSpec.nestedRandomOracleSwap`.

*Flattening a sum of handlers*:

* `QueryImpl.flattenStateT_add`.

*One step*:

* `QueryImpl.run_parallelStateT_randomOracle_map_eq`.

*Flattening*:

* `QueryImpl.flattenStateT_nestedRandomOracle`,
  `QueryImpl.flattenStateT_add_nestedRandomOracle`.

*The run equalities*:

* `OracleComp.map_run_simulateQ_parallelStateT_randomOracle`,
  `OracleComp.map_run_simulateQ_add_parallelStateT_randomOracle`,
  `OracleComp.run_run_simulateQ_nestedRandomOracle`,
  `OracleComp.map_run_run_simulateQ_nestedRandomOracle`,
  `OracleComp.map_run_simulateQ_flattenStateT_nestedRandomOracleSwap`,
  `OracleComp.run_run_simulateQ_nestedRandomOracleSwap`.

*The fresh-answer bounds*:

* `unifFwdProd`, `OracleComp.evalDist_run_parallel_setOf_le_of_fresh_bound`,
  `OracleComp.evalDist_run_run_nested_setOf_le_of_fresh_bound`.
-/

public section

open OracleComp OracleSpec OracleSpec.QueryCache MeasureTheory
open scoped ENNReal

/-! ## The nested handlers -/

namespace OracleSpec

/-- Two lazy random oracles nested as an outer state over an inner state: the left signature's
cache is the outer state and the right signature's cache the inner one. -/
@[expose]
def nestedRandomOracle {ι₁ ι₂ : Type}
    (spec₁ : OracleSpec.{0, 0} ι₁) (spec₂ : OracleSpec.{0, 0} ι₂)
    [DecidableEq ι₁] [DecidableEq ι₂]
    [∀ t : spec₁.Domain, SampleableType (spec₁.Range t)]
    [∀ t : spec₂.Domain, SampleableType (spec₂.Range t)] :
    QueryImpl (spec₁ + spec₂)
      (StateT spec₁.QueryCache (StateT spec₂.QueryCache ProbComp)) :=
  (QueryImpl.liftBase (τ := spec₂.QueryCache) spec₁.randomOracle :
      QueryImpl spec₁ (StateT spec₁.QueryCache (StateT spec₂.QueryCache ProbComp))) +
    spec₂.randomOracle.liftTarget (StateT spec₁.QueryCache (StateT spec₂.QueryCache ProbComp))

/-- The same pair of lazy random oracles nested the other way round: the right signature's cache
is the outer state and the left signature's cache the inner one. -/
@[expose]
def nestedRandomOracleSwap {ι₁ ι₂ : Type}
    (spec₁ : OracleSpec.{0, 0} ι₁) (spec₂ : OracleSpec.{0, 0} ι₂)
    [DecidableEq ι₁] [DecidableEq ι₂]
    [∀ t : spec₁.Domain, SampleableType (spec₁.Range t)]
    [∀ t : spec₂.Domain, SampleableType (spec₂.Range t)] :
    QueryImpl (spec₁ + spec₂)
      (StateT spec₂.QueryCache (StateT spec₁.QueryCache ProbComp)) :=
  spec₁.randomOracle.liftTarget (StateT spec₂.QueryCache (StateT spec₁.QueryCache ProbComp)) +
    (QueryImpl.liftBase (τ := spec₁.QueryCache) spec₂.randomOracle :
      QueryImpl spec₂ (StateT spec₂.QueryCache (StateT spec₁.QueryCache ProbComp)))

end OracleSpec

/-! ## Flattening a sum of handlers -/

namespace QueryImpl

universe u v w x

/-- `flattenStateT` acts on each query index separately, so it distributes over a sum of
handlers. -/
theorem flattenStateT_add {ι₁ : Type u} {ι₂ : Type v}
    {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{v, w} ι₂}
    {m : Type w → Type x} [Monad m] {σ τ : Type w}
    (impl₁ : QueryImpl spec₁ (StateT σ (StateT τ m)))
    (impl₂ : QueryImpl spec₂ (StateT σ (StateT τ m))) :
    (impl₁ + impl₂).flattenStateT = impl₁.flattenStateT + impl₂.flattenStateT := by
  funext t; cases t <;> rfl

end QueryImpl

/-! ## One step -/

namespace QueryImpl

variable {ι₀ ι₁ ι₂ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
  {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}
  [DecidableEq ι₁] [DecidableEq ι₂]
  [∀ t : spec₁.Domain, SampleableType (spec₁.Range t)]
  [∀ t : spec₂.Domain, SampleableType (spec₂.Range t)]

/-- One step of the two independent lazy random oracles on a product cache is one step of the
lazy random oracle on the sum signature, transported along `OracleSpec.QueryCache.addEquiv`. -/
lemma run_parallelStateT_randomOracle_map_eq (t : (spec₁ + spec₂).Domain)
    (p : spec₁.QueryCache × spec₂.QueryCache) :
    Prod.map id (addEquiv spec₁ spec₂) <$>
        ((QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle) t).run p =
      ((spec₁ + spec₂).randomOracle t).run (addEquiv spec₁ spec₂ p) := by
  obtain ⟨c₁, c₂⟩ := p
  cases t with
  | inl t =>
      rcases h : c₁ t with _ | u <;>
        simp [QueryImpl.parallelStateT, h, addEquiv_cacheQuery_inl, Prod.map]
  | inr t =>
      rcases h : c₂ t with _ | u <;>
        simp [QueryImpl.parallelStateT, h, addEquiv_cacheQuery_inr, Prod.map]

/-! ## Flattening the nested handlers -/

/-- Flattening the nested pair of lazy random oracles gives the parallel product-cache handler,
with the left signature's cache as the first component. -/
theorem flattenStateT_nestedRandomOracle :
    (nestedRandomOracle spec₁ spec₂).flattenStateT =
      QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle := by
  rw [nestedRandomOracle, flattenStateT_add]
  funext t
  refine StateT.ext fun ⟨c₁, c₂⟩ => ?_
  cases t
  · rw [QueryImpl.add_apply_inl, flattenStateT_liftBase_apply_run]; rfl
  · rw [QueryImpl.add_apply_inr, QueryImpl.flattenStateT_liftTarget_apply_run]; rfl

/-- Flattening a stateless private-sampling summand in front of the nested pair gives the same
summand in front of the parallel product-cache handler. -/
theorem flattenStateT_add_nestedRandomOracle (implBase : QueryImpl spec₀ ProbComp) :
    (implBase.liftTarget (StateT spec₁.QueryCache (StateT spec₂.QueryCache ProbComp)) +
          nestedRandomOracle spec₁ spec₂).flattenStateT =
      implBase.liftTarget (StateT (spec₁.QueryCache × spec₂.QueryCache) ProbComp) +
        QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle := by
  rw [flattenStateT_add, flattenStateT_liftTarget_base, flattenStateT_nestedRandomOracle]

end QueryImpl

/-! ## The run equalities -/

namespace OracleComp

variable {ι₀ ι₁ ι₂ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
  {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}
  [DecidableEq ι₁] [DecidableEq ι₂]
  [∀ t : spec₁.Domain, SampleableType (spec₁.Range t)]
  [∀ t : spec₂.Domain, SampleableType (spec₂.Range t)]

/-- **Two independently cached lazy random oracles are one lazy random oracle on the sum
signature.**  The product-cache run is the joint-cache run up to the pairing
`OracleSpec.QueryCache.addEquiv`. -/
theorem map_run_simulateQ_parallelStateT_randomOracle {α : Type}
    (oa : OracleComp (spec₁ + spec₂) α) (p : spec₁.QueryCache × spec₂.QueryCache) :
    Prod.map id (addEquiv spec₁ spec₂) <$>
        (simulateQ (QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle) oa).run p =
      (simulateQ (spec₁ + spec₂).randomOracle oa).run (addEquiv spec₁ spec₂ p) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    QueryImpl.run_parallelStateT_randomOracle_map_eq oa p

/-- The same identification with a stateless private-sampling summand in front, which is the
shape the fresh-answer engine consumes. -/
theorem map_run_simulateQ_add_parallelStateT_randomOracle
    (implBase : QueryImpl spec₀ ProbComp) {α : Type}
    (oa : OracleComp (spec₀ + (spec₁ + spec₂)) α)
    (p : spec₁.QueryCache × spec₂.QueryCache) :
    Prod.map id (addEquiv spec₁ spec₂) <$>
        (simulateQ (implBase.liftTarget
              (StateT (spec₁.QueryCache × spec₂.QueryCache) ProbComp) +
            QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle) oa).run p =
      (simulateQ (implBase.liftTarget
            (StateT (spec₁ + spec₂).QueryCache ProbComp) +
          (spec₁ + spec₂).randomOracle) oa).run (addEquiv spec₁ spec₂ p) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ ?_ oa p
  rintro (i | t) s
  · rw [QueryImpl.add_apply_inl, QueryImpl.add_apply_inl]
    exact QueryImpl.run_liftTarget_map_eq implBase _ i s
  · rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
    exact QueryImpl.run_parallelStateT_randomOracle_map_eq t s

/-- **Two independently nested lazy random oracles are one lazy random oracle on the sum
signature.**  The nested run, read at the outer state then the inner state, is the joint-cache
run up to the pairing `OracleSpec.QueryCache.addEquiv`. -/
theorem run_run_simulateQ_nestedRandomOracle {α : Type}
    (oa : OracleComp (spec₁ + spec₂) α)
    (c₁ : spec₁.QueryCache) (c₂ : spec₂.QueryCache) :
    ((simulateQ (nestedRandomOracle spec₁ spec₂) oa).run c₁).run c₂ =
      (fun z : α × (spec₁ + spec₂).QueryCache =>
          ((z.1, ((addEquiv spec₁ spec₂).symm z.2).1),
            ((addEquiv spec₁ spec₂).symm z.2).2)) <$>
        (simulateQ (spec₁ + spec₂).randomOracle oa).run (addEquiv spec₁ spec₂ (c₁, c₂)) := by
  rw [← map_run_simulateQ_parallelStateT_randomOracle,
    ← QueryImpl.flattenStateT_nestedRandomOracle, simulateQ_flattenStateT_run, Functor.map_map]
  simp [Prod.map, bind_pure_comp]

/-- Pairing the two final caches of the nested run gives the joint run exactly: the transport
discards nothing. -/
theorem map_run_run_simulateQ_nestedRandomOracle {α : Type}
    (oa : OracleComp (spec₁ + spec₂) α)
    (c₁ : spec₁.QueryCache) (c₂ : spec₂.QueryCache) :
    (fun w : (α × spec₁.QueryCache) × spec₂.QueryCache =>
        (w.1.1, addEquiv spec₁ spec₂ (w.1.2, w.2))) <$>
      ((simulateQ (nestedRandomOracle spec₁ spec₂) oa).run c₁).run c₂ =
      (simulateQ (spec₁ + spec₂).randomOracle oa).run (addEquiv spec₁ spec₂ (c₁, c₂)) := by
  rw [run_run_simulateQ_nestedRandomOracle, Functor.map_map]
  simp [Equiv.apply_symm_apply]

/-- The opposite nesting order is the same joint lazy oracle, paired the other way round: neither
summand has to be the outer one.  Stated for the flattened one-state handler. -/
theorem map_run_simulateQ_flattenStateT_nestedRandomOracleSwap {α : Type}
    (oa : OracleComp (spec₁ + spec₂) α)
    (c₂ : spec₂.QueryCache) (c₁ : spec₁.QueryCache) :
    Prod.map id (fun p : spec₂.QueryCache × spec₁.QueryCache =>
          addEquiv spec₁ spec₂ (p.2, p.1)) <$>
        (simulateQ (nestedRandomOracleSwap spec₁ spec₂).flattenStateT oa).run (c₂, c₁) =
      (simulateQ (spec₁ + spec₂).randomOracle oa).run (addEquiv spec₁ spec₂ (c₁, c₂)) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ ?_ oa (c₂, c₁)
  rintro (t | t) ⟨d₂, d₁⟩
  · rw [nestedRandomOracleSwap, QueryImpl.flattenStateT_add, QueryImpl.add_apply_inl,
      QueryImpl.flattenStateT_liftTarget_apply_run,
      ← QueryImpl.run_parallelStateT_randomOracle_map_eq, QueryImpl.parallelStateT]
    simp [Functor.map_map, Prod.map]
  · rw [nestedRandomOracleSwap, QueryImpl.flattenStateT_add, QueryImpl.add_apply_inr,
      QueryImpl.flattenStateT_liftBase_apply_run,
      ← QueryImpl.run_parallelStateT_randomOracle_map_eq, QueryImpl.parallelStateT]
    simp [Functor.map_map, Prod.map]

/-- The two-level form of the swapped nesting: the nested run, read at the outer state then the
inner state, is the joint-cache run up to the pairing. -/
theorem run_run_simulateQ_nestedRandomOracleSwap {α : Type}
    (oa : OracleComp (spec₁ + spec₂) α)
    (c₂ : spec₂.QueryCache) (c₁ : spec₁.QueryCache) :
    ((simulateQ (nestedRandomOracleSwap spec₁ spec₂) oa).run c₂).run c₁ =
      (fun z : α × (spec₁ + spec₂).QueryCache =>
          ((z.1, ((addEquiv spec₁ spec₂).symm z.2).2),
            ((addEquiv spec₁ spec₂).symm z.2).1)) <$>
        (simulateQ (spec₁ + spec₂).randomOracle oa).run (addEquiv spec₁ spec₂ (c₁, c₂)) := by
  rw [← map_run_simulateQ_flattenStateT_nestedRandomOracleSwap, simulateQ_flattenStateT_run,
    Functor.map_map]
  simp [Prod.map, bind_pure_comp]

end OracleComp

/-! ## The fresh-answer bounds -/

/-- The private-sampling summand of the fresh-answer engine, on a product cache. -/
abbrev unifFwdProd {ι₁ ι₂ : Type} (spec₁ : OracleSpec.{0, 0} ι₁)
    (spec₂ : OracleSpec.{0, 0} ι₂) :
    QueryImpl unifSpec (StateT (spec₁.QueryCache × spec₂.QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget _

namespace OracleComp

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}
  [DecidableEq ι₁] [DecidableEq ι₂]
  [∀ t : spec₁.Domain, SampleableType (spec₁.Range t)]
  [∀ t : spec₂.Domain, SampleableType (spec₂.Range t)]

/-- **The fresh-answer bound for two independently cached lazy random oracles.**  The bound the
engine proves for one joint cache started from `∅` transports verbatim to the product cache. -/
theorem evalDist_run_parallel_setOf_le_of_fresh_bound
    (P : (spec₁ + spec₂).QueryCache → Prop) (hP : ¬ P ∅)
    (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : (spec₁ + spec₂).Domain) (c : (spec₁ + spec₂).QueryCache), ¬ P c →
      c t = none →
      (letI : MeasurableSpace ((spec₁ + spec₂).Range t) := ⊤;
        𝒟[($ᵗ (spec₁ + spec₂).Range t : ProbComp ((spec₁ + spec₂).Range t))]
          {u | P (c.cacheQuery t u)} ≤ ε))
    {α : Type} (oa : OracleComp (unifSpec + (spec₁ + spec₂)) α) (q : ℕ) :
    (letI : MeasurableSpace (α × (spec₁.QueryCache × spec₂.QueryCache)) := ⊤;
      𝒟[(simulateQ (unifFwdProd spec₁ spec₂ +
            QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle) oa).run (∅, ∅)]
        {z | P (addEquiv spec₁ spec₂ z.2) ∧
          QueryCache.enncard (addEquiv spec₁ spec₂ z.2) ≤ (q : ℝ≥0∞)} ≤ (q : ℝ≥0∞) * ε) := by
  let _ : MeasurableSpace (α × (spec₁.QueryCache × spec₂.QueryCache)) := ⊤
  let _ : MeasurableSpace (α × (spec₁ + spec₂).QueryCache) := ⊤
  have hmap := map_run_simulateQ_add_parallelStateT_randomOracle
    (spec₀ := unifSpec) (QueryImpl.ofLift unifSpec ProbComp) oa (∅, ∅)
  rw [addEquiv_empty] at hmap
  have hpush : 𝒟[(simulateQ (unifFwdProd spec₁ spec₂ +
        QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle) oa).run (∅, ∅)]
      {z | P (addEquiv spec₁ spec₂ z.2) ∧
        QueryCache.enncard (addEquiv spec₁ spec₂ z.2) ≤ (q : ℝ≥0∞)} =
      𝒟[(simulateQ (unifFwdImpl (spec₁ + spec₂) + (spec₁ + spec₂).randomOracle) oa).run ∅]
        {z | P z.2 ∧ QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} := by
    rw [unifFwdImpl, ← hmap, evalDist_map_of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    rfl
  rw [hpush]
  exact evalDist_run_setOf_le_of_fresh_bound P hP ε hε hfresh oa q

/-- **The fresh-answer bound for two independently nested lazy random oracles.**  The bound the
engine proves for one joint cache started from `∅` transports verbatim to the nested experiment,
with each of the two caches started empty. -/
theorem evalDist_run_run_nested_setOf_le_of_fresh_bound
    (P : (spec₁ + spec₂).QueryCache → Prop) (hP : ¬ P ∅)
    (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : (spec₁ + spec₂).Domain) (c : (spec₁ + spec₂).QueryCache), ¬ P c →
      c t = none →
      (letI : MeasurableSpace ((spec₁ + spec₂).Range t) := ⊤;
        𝒟[($ᵗ (spec₁ + spec₂).Range t : ProbComp ((spec₁ + spec₂).Range t))]
          {u | P (c.cacheQuery t u)} ≤ ε))
    {α : Type} (oa : OracleComp (unifSpec + (spec₁ + spec₂)) α) (q : ℕ) :
    (letI : MeasurableSpace ((α × spec₁.QueryCache) × spec₂.QueryCache) := ⊤;
      𝒟[((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT spec₁.QueryCache (StateT spec₂.QueryCache ProbComp)) +
            nestedRandomOracle spec₁ spec₂) oa).run ∅).run ∅]
        {z | P (addEquiv spec₁ spec₂ (z.1.2, z.2)) ∧
          QueryCache.enncard (addEquiv spec₁ spec₂ (z.1.2, z.2)) ≤ (q : ℝ≥0∞)} ≤
        (q : ℝ≥0∞) * ε) := by
  let _ : MeasurableSpace ((α × spec₁.QueryCache) × spec₂.QueryCache) := ⊤
  let _ : MeasurableSpace (α × (spec₁.QueryCache × spec₂.QueryCache)) := ⊤
  have hflat := simulateQ_flattenStateT_run
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT spec₁.QueryCache (StateT spec₂.QueryCache ProbComp)) +
        nestedRandomOracle spec₁ spec₂) oa (∅ : spec₁.QueryCache) (∅ : spec₂.QueryCache)
  rw [QueryImpl.flattenStateT_add_nestedRandomOracle] at hflat
  have hpush :
      𝒟[((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT spec₁.QueryCache (StateT spec₂.QueryCache ProbComp)) +
            nestedRandomOracle spec₁ spec₂) oa).run ∅).run ∅]
        {z | P (addEquiv spec₁ spec₂ (z.1.2, z.2)) ∧
          QueryCache.enncard (addEquiv spec₁ spec₂ (z.1.2, z.2)) ≤ (q : ℝ≥0∞)} =
      𝒟[(simulateQ (unifFwdProd spec₁ spec₂ +
            QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle) oa).run (∅, ∅)]
        {z | P (addEquiv spec₁ spec₂ z.2) ∧
          QueryCache.enncard (addEquiv spec₁ spec₂ z.2) ≤ (q : ℝ≥0∞)} := by
    rw [hflat, bind_pure_comp, evalDist_map_of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    rfl
  rw [hpush]
  exact evalDist_run_parallel_setOf_le_of_fresh_bound P hP ε hε hfresh oa q

end OracleComp
