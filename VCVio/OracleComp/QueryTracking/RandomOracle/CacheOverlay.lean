/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The lazy random oracle and the cache overlay

Two descriptions of a lazily sampled random function agree. `OracleSpec.randomOracle` answers each
fresh query of an `OracleComp spec` computation by a uniform sample in `ProbComp` and caches it.
`OracleSpec.withCacheOverlay` caches the computation's queries while forwarding fresh ones to the
oracle itself, which a uniform answer measure (`OracleSpec.UniformAnswerMeasure`) answers uniformly.

Interpreting the forwarded queries of `withCacheOverlay` by uniform sampling is exactly the random
oracle (`simulateQ_uniformSampleImpl_run_cachingOracle`), so both have the same output
distribution from any initial cache (`evalDist_run'_randomOracle_eq_withCacheOverlay`). This lets
a game stated in either form reuse bounds proved for the other.
-/

public section

open OracleComp OracleSpec

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- Answering the forwarded queries of the caching oracle by uniform sampling is the lazy random
oracle, from every initial cache. -/
theorem simulateQ_uniformSampleImpl_run_cachingOracle {α : Type} (oa : OracleComp spec α)
    (cache : spec.QueryCache) :
    simulateQ uniformSampleImpl ((simulateQ spec.cachingOracle oa).run cache) =
      (simulateQ spec.randomOracle oa).run cache := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases h : cache t with _ | u
    · simp [h, ih]
    · simp [h, ih]

/-- Under uniform oracle semantics, the lazy random oracle and the cache overlay have the same
output distribution from every initial cache. -/
theorem evalDist_run'_randomOracle_eq_withCacheOverlay [UniformAnswerMeasure spec]
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) (cache : spec.QueryCache) :
    𝒟[(simulateQ spec.randomOracle oa).run' cache] = 𝒟[withCacheOverlay cache oa] := by
  rw [← uniformSampleImpl.evalDist_simulateQ (withCacheOverlay cache oa)]
  congr 1
  rw [withCacheOverlay, StateT.run'_eq, StateT.run'_eq, simulateQ_map,
    simulateQ_uniformSampleImpl_run_cachingOracle]

/-- Under uniform oracle semantics, every event has the same probability under the lazy random
oracle and under the cache overlay, from every initial cache. -/
theorem prEvent_run'_randomOracle_eq_withCacheOverlay [UniformAnswerMeasure spec]
    {α : Type} (oa : OracleComp spec α) (cache : spec.QueryCache) (p : α → Prop) :
    Pr{let x ← (simulateQ spec.randomOracle oa).run' cache}[p x] =
      Pr{let x ← withCacheOverlay cache oa}[p x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    evalDist_run'_randomOracle_eq_withCacheOverlay]
