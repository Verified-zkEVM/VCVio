/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.EvalDist.Measure

/-!
# Value distributions under random-oracle presampling

An actual total prefix may interleave stateless private sampling and the lazy random oracle.
Discarding the prefix preserves a fixed subsequent client's complete returned-value law, even
when inputs collide, coordinates repeat or its cache is populated. This observes neither the
final cache nor prefix work or trace. A separate virtual fresh-entry overwrite law requires
that the overwritten coordinate is missing from the initial cache.
-/

public section

open OracleComp OracleSpec OracleComp.RandomOracleTraversal

namespace OracleComp.RandomOraclePresampling

/-- Presampling one fresh answer preserves the complete returned value distribution. -/
theorem evalDist_prepend_fresh {ι Input Output α : Type} {privateSpec : OracleSpec.{0, 0} ι}
    [DecidableEq Input] [SampleableType Output]
    (privateImpl : QueryImpl privateSpec ProbComp)
    (computation : OracleComp (privateSpec + (Input →ₒ Output)) α)
    (cache : QueryCache (Input →ₒ Output)) (target : Input) (hfresh : cache target = none) :
    let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
      (randomOracle : QueryImpl (Input →ₒ Output)
        (StateT (QueryCache (Input →ₒ Output)) ProbComp))
    (Prod.fst <$> (simulateQ H computation).run cache) =ᵈ
      (do
        let value ← ($ᵗ Output : ProbComp Output)
        Prod.fst <$> (simulateQ H computation).run (cache.cacheQuery target value)) := by
  let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
    (randomOracle : QueryImpl (Input →ₒ Output)
      (StateT (QueryCache (Input →ₒ Output)) ProbComp))
  change (Prod.fst <$> (simulateQ H computation).run cache) =ᵈ
    (do
      let value ← ($ᵗ Output : ProbComp Output)
      Prod.fst <$> (simulateQ H computation).run (cache.cacheQuery target value))
  induction computation using OracleComp.inductionOn generalizing cache target with
  | pure result =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind queried next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases queried with coin | input
    · have hcoin : ∀ probe : QueryCache (Input →ₒ Output),
          (H (Sum.inl coin)).run probe =
            (fun value => (value, probe)) <$> privateImpl coin := by
        intro probe
        simp only [H, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_liftM,
          bind_pure_comp]
        rfl
      simp only [hcoin, bind_map_left]
      refine (EvalDistEq.bind_right _
        (fun value => ih value cache target hfresh)).trans ?_
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    · have hmissAt : ∀ probe : QueryCache (Input →ₒ Output), probe input = none →
          (H (Sum.inr input)).run probe =
            (fun value => (value, probe.cacheQuery input value)) <$>
              ($ᵗ Output : ProbComp Output) := by
        intro probe hprobe
        change (randomOracle input).run probe = _
        rw [QueryImpl.withCaching_run_none _ hprobe]
        simp [uniformSampleImpl]
      have hhitAt : ∀ (probe : QueryCache (Input →ₒ Output)) (value : Output),
          probe input = some value → (H (Sum.inr input)).run probe = pure (value, probe) := by
        intro probe value hprobe
        change (randomOracle input).run probe = _
        rw [QueryImpl.withCaching_run_some _ hprobe]
      by_cases hsame : input = target
      · subst hsame
        simp only [hmissAt cache hfresh, bind_map_left]
        refine EvalDistEq.bind_right _ (fun value => ?_)
        simp only [hhitAt (cache.cacheQuery input value) value
          (QueryCache.cacheQuery_self cache input value), pure_bind]
        exact EvalDistEq.rfl
      · cases hlookup : cache input with
        | some cached =>
          simp only [hhitAt cache cached hlookup, pure_bind]
          refine (ih cached cache target hfresh).trans
            (EvalDistEq.bind_right _ (fun value => ?_))
          simp only [hhitAt (cache.cacheQuery target value) cached
            (by rw [QueryCache.cacheQuery_of_ne cache value hsame]; exact hlookup), pure_bind]
          exact EvalDistEq.rfl
        | none =>
          simp only [hmissAt cache hlookup, bind_map_left]
          refine (EvalDistEq.bind_right _
            (fun value => ih value (cache.cacheQuery input value) target
              (by rw [QueryCache.cacheQuery_of_ne cache value (Ne.symm hsame)];
                  exact hfresh))).trans ?_
          refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
          refine EvalDistEq.bind_right _ (fun extra => ?_)
          simp only [hmissAt (cache.cacheQuery target extra)
            (by rw [QueryCache.cacheQuery_of_ne cache extra hsame]; exact hlookup),
            bind_map_left, QueryCache.cacheQuery_comm cache hsame]
          rfl

/-- Discarding any total prefix preserves the fixed client's complete returned-value law. -/
theorem evalDist_prepend_prefix {ι Input Output α β : Type}
    {privateSpec : OracleSpec.{0, 0} ι} [DecidableEq Input] [SampleableType Output]
    (privateImpl : QueryImpl privateSpec ProbComp)
    (before : OracleComp (privateSpec + (Input →ₒ Output)) β)
    (client : OracleComp (privateSpec + (Input →ₒ Output)) α)
    (cache : QueryCache (Input →ₒ Output)) :
    let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
      (randomOracle : QueryImpl (Input →ₒ Output)
        (StateT (QueryCache (Input →ₒ Output)) ProbComp))
    (Prod.fst <$> (simulateQ H client).run cache) =ᵈ
      (Prod.fst <$> (simulateQ H (before >>= fun _ => client)).run cache) := by
  let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
    (randomOracle : QueryImpl (Input →ₒ Output)
      (StateT (QueryCache (Input →ₒ Output)) ProbComp))
  change (Prod.fst <$> (simulateQ H client).run cache) =ᵈ
    (Prod.fst <$> (simulateQ H (before >>= fun _ => client)).run cache)
  induction before using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp only [pure_bind]
    exact EvalDistEq.rfl
  | query_bind queried next ih =>
    rcases queried with coin | input
    · have hcoin : ∀ probe : QueryCache (Input →ₒ Output),
          (H (Sum.inl coin)).run probe =
            (fun value => (value, probe)) <$> privateImpl coin := by
        intro probe
        simp only [H, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_liftM,
          bind_pure_comp]
        rfl
      refine (OracleComp.EvalDistEq.bind_const (privateImpl coin)
        (Prod.fst <$> (simulateQ H client).run cache)).symm.trans ?_
      have h := EvalDistEq.bind_right (privateImpl coin) (fun value => ih value cache)
      simpa only [bind_assoc, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        map_bind, hcoin, bind_map_left] using h
    · cases hlookup : cache input with
      | some value =>
        have hhit : (H (Sum.inr input)).run cache = pure (value, cache) := by
          change (randomOracle input).run cache = _
          exact QueryImpl.withCaching_run_some _ hlookup
        simpa only [bind_assoc, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          map_bind, hhit, pure_bind] using ih value cache
      | none =>
        have hmiss : (H (Sum.inr input)).run cache =
            (fun value => (value, cache.cacheQuery input value)) <$>
              ($ᵗ Output : ProbComp Output) := by
          change (randomOracle input).run cache = _
          rw [QueryImpl.withCaching_run_none _ hlookup]
          simp [uniformSampleImpl]
        refine (evalDist_prepend_fresh privateImpl client cache input hlookup).trans ?_
        have h := EvalDistEq.bind_right ($ᵗ Output : ProbComp Output)
          (fun value => ih value (cache.cacheQuery input value))
        simpa only [bind_assoc, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          map_bind, hmiss, bind_map_left] using h

/-- A discarded traversal preserves client values for arbitrary schedules, inputs and caches. -/
theorem evalDist_prepend_traversal {ι Input Output α Index State : Type}
    {privateSpec : OracleSpec.{0, 0} ι} [DecidableEq Input] [SampleableType Output]
    (privateImpl : QueryImpl privateSpec ProbComp)
    (client : OracleComp (privateSpec + (Input →ₒ Output)) α)
    (input : Index → State → Input) (step : Index → State → Output → State)
    (nodes : List Index) (state : State) (cache : QueryCache (Input →ₒ Output)) :
    let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
      (randomOracle : QueryImpl (Input →ₒ Output)
        (StateT (QueryCache (Input →ₒ Output)) ProbComp))
    (Prod.fst <$> (simulateQ H client).run cache) =ᵈ
      (Prod.fst <$> (simulateQ H
        ((liftM (evaluate input step nodes state) :
            OracleComp (privateSpec + (Input →ₒ Output)) State) >>= fun _ => client)).run
          cache) :=
  evalDist_prepend_prefix privateImpl _ client cache

end OracleComp.RandomOraclePresampling
