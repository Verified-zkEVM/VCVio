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

A stateless private interpretation can be interleaved with a lazy random oracle. A fresh
uniform entry, or a fresh separated traversal, may precede any client without changing its
returned value distribution. These laws discard the final cache and the prefix state.
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

/-- A fresh separated traversal preserves the complete returned value distribution. -/
theorem evalDist_prepend_traversal {ι Input Output α Index State : Type}
    {privateSpec : OracleSpec.{0, 0} ι} [DecidableEq Input] [SampleableType Output]
    (privateImpl : QueryImpl privateSpec ProbComp)
    (computation : OracleComp (privateSpec + (Input →ₒ Output)) α)
    (input : Index → State → Input) (step : Index → State → Output → State)
    (hseparated : Separated input) (nodes : List Index) (state : State)
    (cache : QueryCache (Input →ₒ Output)) (hnodup : nodes.Nodup)
    (hfresh : FreshFor input nodes cache) :
    let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
      (randomOracle : QueryImpl (Input →ₒ Output)
        (StateT (QueryCache (Input →ₒ Output)) ProbComp))
    (Prod.fst <$> (simulateQ H computation).run cache) =ᵈ
      (Prod.fst <$> (simulateQ H
        ((liftM (evaluate input step nodes state) :
            OracleComp (privateSpec + (Input →ₒ Output)) State) >>=
          fun _ => computation)).run cache) := by
  let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
    (randomOracle : QueryImpl (Input →ₒ Output)
      (StateT (QueryCache (Input →ₒ Output)) ProbComp))
  change (Prod.fst <$> (simulateQ H computation).run cache) =ᵈ
    (Prod.fst <$> (simulateQ H
      ((liftM (evaluate input step nodes state) :
          OracleComp (privateSpec + (Input →ₒ Output)) State) >>=
        fun _ => computation)).run cache)
  have hrun : ∀ ns st c,
      (simulateQ H
        ((liftM (evaluate input step ns st) :
            OracleComp (privateSpec + (Input →ₒ Output)) State) >>=
          fun _ => computation)).run c =
        ((simulateQ randomOracle (evaluate input step ns st)).run c >>=
          fun result => (simulateQ H computation).run result.2) := by
    intro ns st c
    rw [simulateQ_bind, show simulateQ H (liftM (evaluate input step ns st) :
        OracleComp (privateSpec + (Input →ₒ Output)) State) =
        simulateQ randomOracle (evaluate input step ns st) from
      QueryImpl.simulateQ_add_liftM_right _ _ _, StateT.run_bind]
  induction nodes generalizing state cache with
  | nil =>
    exact EvalDistEq.rfl
  | cons node rest ih =>
    have hnot : node ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hhead : cache (input node state) = none := hfresh node (by simp) state
    refine (evalDist_prepend_fresh privateImpl computation cache (input node state) hhead).trans ?_
    have hstep : ∀ value : Output,
        (Prod.fst <$> (simulateQ H computation).run
            (cache.cacheQuery (input node state) value)) =ᵈ
          (Prod.fst <$> (simulateQ H
            ((liftM (evaluate input step rest (step node state value)) :
                OracleComp (privateSpec + (Input →ₒ Output)) State) >>=
              fun _ => computation)).run (cache.cacheQuery (input node state) value)) := by
      intro value
      refine ih (step node state value) (cache.cacheQuery (input node state) value) hrest ?_
      intro other hother otherState
      rw [QueryCache.cacheQuery_of_ne cache value
        (hseparated other node (fun same => hnot (same ▸ hother)) otherState state)]
      exact hfresh other (by simp [hother]) otherState
    refine (EvalDistEq.bind_right ($ᵗ Output : ProbComp Output) hstep).trans ?_
    have hmiss : (randomOracle (input node state)).run cache =
        (fun value => (value, cache.cacheQuery (input node state) value)) <$>
          ($ᵗ Output : ProbComp Output) := by
      rw [QueryImpl.withCaching_run_none _ hhead]
      simp [uniformSampleImpl]
    simp only [hrun]
    simp only [evaluate, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      hmiss, bind_map_left, map_bind, bind_assoc]
    exact EvalDistEq.rfl

end OracleComp.RandomOraclePresampling
