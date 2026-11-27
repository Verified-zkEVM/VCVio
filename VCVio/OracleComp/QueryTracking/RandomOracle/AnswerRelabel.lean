/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.SimSemantics.QueryImpl.Relabel
public import VCVio.OracleComp.SimSemantics.WriterT.Measure
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Dependent answer representation of a lazy random oracle

Explicit chosen-sampler equations preserve actual public answers, chronological logs and the
complete warm cache jointly. Private uniform queries are forwarded statelessly.
-/

public section

open OracleComp OracleSpec

namespace OracleComp.RandomOracleAnswerRelabel

/-- Only public answers change representation; private answers are forwarded unchanged. -/
@[expose] def worldAnswers {ι : Type} {R S : OracleSpec ι}
    (e : ∀ input, R input ≃ S input) :
    ∀ input, (unifSpec + R).Range input ≃ (unifSpec + S).Range input
  | .inl _ => Equiv.refl _
  | .inr input => e input

/-- Running a converted query reads back its response without changing the retained state. -/
theorem relabel_step_run {ι : Type} {R S : OracleSpec ι} {σ : Type}
    (e : ∀ input, R input ≃ S input) (impl : QueryImpl S (StateT σ ProbComp))
    (input : ι) (state : σ) :
    (simulateQ impl (QueryImpl.relabel e input)).run state =
      (fun output => ((e input).symm output.1, output.2)) <$> (impl input).run state := by
  rw [QueryImpl.relabel_apply, simulateQ_map, simulateQ_spec_query]
  change ((impl input).run state >>= fun output =>
    pure ((e input).symm output.1, output.2)) = _
  rw [bind_pure_comp]

/-- One cached public step preserves the joint response and mapped post-cache law. -/
theorem cache_step {ι : Type} [DecidableEq ι] {R S : OracleSpec ι}
    [∀ input, SampleableType (R input)] [∀ input, SampleableType (S input)]
    (e : ∀ input, R input ≃ S input)
    (he : ∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input)))
    (input : ι) (cache : R.QueryCache) :
    (simulateQ S.randomOracle (QueryImpl.relabel e input)).run
        (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
      Prod.map id (QueryCache.mapAnswers (fun input => e input)) <$>
        (R.randomOracle input).run cache := by
  rw [relabel_step_run]
  cases hcache : cache input with
  | none =>
    have htarget : QueryCache.mapAnswers (fun input => e input) cache input = none := by
      simp only [QueryCache.mapAnswers_apply, hcache, Option.map_none]
    have h := ((he input).symm.map fun answer : S input =>
      ((e input).symm answer,
        (QueryCache.mapAnswers (fun input => e input) cache).cacheQuery input answer))
    simpa only [randomOracle.run_eq, htarget, hcache, map_bind, map_pure,
      bind_pure_comp, Functor.map_map, Function.comp_def, Prod.map, id_eq,
      Equiv.symm_apply_apply, QueryCache.mapAnswers_cacheQuery] using h
  | some answer =>
    have htarget : QueryCache.mapAnswers (fun input => e input) cache input =
        some ((e input) answer) := by
      simp only [QueryCache.mapAnswers_apply, hcache, Option.map_some]
    simpa only [randomOracle.run_eq, htarget, hcache, map_pure, Prod.map, id_eq,
      Equiv.symm_apply_apply] using
      (EvalDistEq.refl
        (pure (answer, QueryCache.mapAnswers (fun input => e input) cache) : ProbComp _))

/-- Complete public-cache transport follows from one cached step and the state-map fold. -/
theorem evalDist_run :
  ∀ {ι : Type} [DecidableEq ι] {R S : OracleSpec ι}
    [∀ input, SampleableType (R input)] [∀ input, SampleableType (S input)]
    (e : ∀ input, R input ≃ S input),
    (∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input))) →
    ∀ {α : Type} (program : OracleComp R α) (cache : R.QueryCache),
      (simulateQ S.randomOracle (simulateQ (QueryImpl.relabel e) program)).run
          (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
        Prod.map id (QueryCache.mapAnswers (fun input => e input)) <$>
          (simulateQ R.randomOracle program).run cache := by
  intro ι _ R S _ _ e he α program cache
  have h := OracleComp.evalDistEq_simulateQ_run_map
    (QueryImpl.compose S.randomOracle (QueryImpl.relabel e)) R.randomOracle
    (QueryCache.mapAnswers (fun input => e input))
    (fun input current => cache_step e he input current) program cache
  simpa only [QueryImpl.simulateQ_compose] using h

/-- One world step forwards private draws and transports only the public cache. -/
theorem world_step {ι : Type} [DecidableEq ι] {R S : OracleSpec ι}
    [∀ input, SampleableType (R input)] [∀ input, SampleableType (S input)]
    (e : ∀ input, R input ≃ S input)
    (he : ∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input)))
    (input : (unifSpec + R).Domain) (cache : R.QueryCache) :
    (simulateQ (unifFwdImpl S + S.randomOracle)
        (QueryImpl.relabel (worldAnswers e) input)).run
        (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
      Prod.map id (QueryCache.mapAnswers (fun input => e input)) <$>
        ((unifFwdImpl R + R.randomOracle) input).run cache := by
  cases input with
  | inl input =>
    rw [relabel_step_run, roSim.run_apply_inl, roSim.run_apply_inl]
    simp [worldAnswers, Functor.map_map, Prod.map]
  | inr input =>
    rw [relabel_step_run]
    change ((fun output : S input × S.QueryCache =>
      ((e input).symm output.1, output.2)) <$>
        (S.randomOracle input).run (QueryCache.mapAnswers (fun input => e input) cache)) =ᵈ
      Prod.map id (QueryCache.mapAnswers (fun input => e input)) <$>
        (R.randomOracle input).run cache
    simpa only [relabel_step_run] using cache_step e he input cache

/-- Adaptive world transport retains private draws and the complete public post-cache. -/
theorem evalDist_world_run :
  ∀ {ι : Type} [DecidableEq ι] {R S : OracleSpec ι}
    [∀ input, SampleableType (R input)] [∀ input, SampleableType (S input)]
    (e : ∀ input, R input ≃ S input),
    (∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input))) →
    ∀ {α : Type} (program : OracleComp (unifSpec + R) α) (cache : R.QueryCache),
      (simulateQ (unifFwdImpl S + S.randomOracle)
        (simulateQ (QueryImpl.relabel (worldAnswers e)) program)).run
          (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
        Prod.map id (QueryCache.mapAnswers (fun input => e input)) <$>
          (simulateQ (unifFwdImpl R + R.randomOracle) program).run cache := by
  intro ι _ R S _ _ e he α program cache
  have h := OracleComp.evalDistEq_simulateQ_run_map
    (QueryImpl.compose (unifFwdImpl S + S.randomOracle)
      (QueryImpl.relabel (worldAnswers e)))
    (unifFwdImpl R + R.randomOracle) (QueryCache.mapAnswers (fun input => e input))
    (fun input current => world_step e he input current) program cache
  simpa only [QueryImpl.simulateQ_compose] using h

/-- A logged public step transports its response, emitted singleton and post-cache jointly. -/
theorem loggedPublicStep {ι : Type} [DecidableEq ι] {R S : OracleSpec ι}
    [∀ input, SampleableType (R input)] [∀ input, SampleableType (S input)]
    (e : ∀ input, R input ≃ S input)
    (he : ∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input)))
    (input : ι) (cache : R.QueryCache) :
    (simulateQ S.randomOracle.withLogging (QueryImpl.relabel e input)).run.run
        (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
      (fun output => ((output.1.1, QueryLog.mapAnswers e output.1.2),
        QueryCache.mapAnswers (fun input => e input) output.2)) <$>
        (R.randomOracle.withLogging input).run.run cache := by
  have h := (cache_step e he input cache).map fun output =>
    ((output.1, ([⟨input, (e input) output.1⟩] : QueryLog S)), output.2)
  simpa [QueryImpl.relabel_apply, simulateQ_map, simulateQ_spec_query,
    QueryImpl.run_withLogging_apply, WriterT.run_map', StateT.run_bind, StateT.run_map,
    StateT.run_pure, bind_pure_comp, Functor.map_map, Function.comp_def, Prod.map] using h

/-- A world step records only its public query, retaining the full log/cache square. -/
theorem loggedWorldStep {ι : Type} [DecidableEq ι] {R S : OracleSpec ι}
    [∀ input, SampleableType (R input)] [∀ input, SampleableType (S input)]
    (e : ∀ input, R input ≃ S input)
    (he : ∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input)))
    (input : (unifSpec + R).Domain) (cache : R.QueryCache) :
    (simulateQ
      ((unifFwdImpl S).liftTarget (WriterT (QueryLog S) (StateT S.QueryCache ProbComp)) +
        S.randomOracle.withLogging)
      (QueryImpl.relabel (worldAnswers e) input)).run.run
        (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
      (fun output => ((output.1.1, QueryLog.mapAnswers e output.1.2),
        QueryCache.mapAnswers (fun input => e input) output.2)) <$>
        (((unifFwdImpl R).liftTarget (WriterT (QueryLog R) (StateT R.QueryCache ProbComp)) +
          R.randomOracle.withLogging) input).run.run cache := by
  cases input with
  | inl input =>
    simp [QueryImpl.relabel_apply, worldAnswers,
      unifFwdImpl, StateT.run_map, Functor.map_map]
  | inr input =>
    simp only [QueryImpl.relabel_apply, simulateQ_map, simulateQ_spec_query,
      worldAnswers, QueryImpl.add_apply_inr]
    change (((e input).symm <$> S.randomOracle.withLogging input).run.run
        (QueryCache.mapAnswers (fun input => e input) cache)) =ᵈ
      (fun output : (R input × QueryLog R) × R.QueryCache =>
        ((output.1.1, QueryLog.mapAnswers e output.1.2),
          QueryCache.mapAnswers (fun input => e input) output.2)) <$>
        (R.randomOracle.withLogging input).run.run cache
    simpa only [QueryImpl.relabel_apply, simulateQ_map, simulateQ_spec_query] using
      loggedPublicStep e he input cache

/-- Full public-log/cache transport with an unchanged stateless uniform summand. -/
theorem evalDist_logged_world_run :
  ∀ {ι : Type} [DecidableEq ι] {R S : OracleSpec ι}
    [∀ input, SampleableType (R input)] [∀ input, SampleableType (S input)]
    (e : ∀ input, R input ≃ S input),
    (∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input))) →
    ∀ {α : Type} (program : OracleComp (unifSpec + R) α) (cache : R.QueryCache),
      (simulateQ
        ((unifFwdImpl S).liftTarget (WriterT (QueryLog S) (StateT S.QueryCache ProbComp)) +
          S.randomOracle.withLogging)
        (simulateQ (QueryImpl.relabel (worldAnswers e)) program)).run.run
          (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
        (fun output => ((output.1.1, QueryLog.mapAnswers e output.1.2),
          QueryCache.mapAnswers (fun input => e input) output.2)) <$>
          (simulateQ
            ((unifFwdImpl R).liftTarget (WriterT (QueryLog R) (StateT R.QueryCache ProbComp)) +
              R.randomOracle.withLogging) program).run.run cache := by
  intro ι _ R S _ _ e he α program cache
  have h := OracleComp.evalDistEq_simulateQ_run_writerT_stateT_map
    (QueryImpl.compose
      ((unifFwdImpl S).liftTarget (WriterT (QueryLog S) (StateT S.QueryCache ProbComp)) +
        S.randomOracle.withLogging)
      (QueryImpl.relabel (worldAnswers e)))
    ((unifFwdImpl R).liftTarget (WriterT (QueryLog R) (StateT R.QueryCache ProbComp)) +
      R.randomOracle.withLogging)
    (QueryCache.mapAnswers (fun input => e input)) (QueryLog.mapAnswers e)
    (QueryLog.mapAnswers_empty e) (QueryLog.mapAnswers_append e)
    (fun input current => loggedWorldStep e he input current) program cache
  simpa only [QueryImpl.simulateQ_compose] using h

end OracleComp.RandomOracleAnswerRelabel
