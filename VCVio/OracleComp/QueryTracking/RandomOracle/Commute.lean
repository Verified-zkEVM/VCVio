/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Commuting queries to the lazy random oracle

Queries to the lazy random oracle `OracleSpec.randomOracle` commute: running a query before or
after another query, or before or after a whole computation run against the same oracle, gives
the same joint distribution of answers, outputs and final cache. A repeated index is answered from
the cache, so the cache must be threaded through both orders; the statements quantify over every
continuation of the answers and the final cache.

## Main statements

- `randomOracle.evalDist_run_bind_run_swap`: two lazy random-oracle queries commute.
- `randomOracle.evalDist_run_bind_simulateQ_run_swap`: a lazy random-oracle query commutes with
  every computation run against the same oracle.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace randomOracle

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- Two queries to the lazy random oracle commute: their answers and the final cache have the
same joint distribution in either order. -/
theorem evalDist_run_bind_run_swap {γ : Type} [MeasurableSpace γ] (t t' : ι₀)
    (cache : spec₀.QueryCache)
    (f : spec₀.Range t → spec₀.Range t' → spec₀.QueryCache → ProbComp γ) :
    𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦
        (spec₀.randomOracle t').run z.2 >>= fun y ↦ f z.1 y.1 y.2] =
      𝒟[(spec₀.randomOracle t').run cache >>= fun y ↦
        (spec₀.randomOracle t).run y.2 >>= fun z ↦ f z.1 y.1 z.2] := by
  -- After a query at `t`, a query at `t` is answered from the cache.
  have hit : ∀ {t : ι₀} {c : spec₀.QueryCache} {z}, z ∈ support ((spec₀.randomOracle t).run c) →
      (spec₀.randomOracle t).run z.2 = pure z := fun {t c z} hz ↦ by
    rw [QueryImpl.withCaching_run_some _ (QueryImpl.withCaching_run_caches _ _ _ _ hz)]
  have keep : ∀ {t t' : ι₀} {c : spec₀.QueryCache} {v : spec₀.Range t'} {z},
      z ∈ support ((spec₀.randomOracle t).run c) → c t' = some v →
      (spec₀.randomOracle t').run z.2 = pure (v, z.2) := fun {t t' c v z} hz hv ↦
    QueryImpl.withCaching_run_some _ (QueryImpl.withCaching_cache_le _ _ _ _ hz hv)
  by_cases htt : t = t'
  · subst htt
    calc _ = 𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦ f z.1 z.1 z.2] :=
          evalDist_bind_congr_of_support _ _ _ fun z hz ↦ by rw [hit hz, pure_bind]
      _ = _ := evalDist_bind_congr_of_support _ _ _ fun z hz ↦ by rw [hit hz, pure_bind]
  cases ht : cache t with
  | some v =>
    calc _ = 𝒟[(spec₀.randomOracle t').run cache >>= fun y ↦ f v y.1 y.2] := by
          rw [QueryImpl.withCaching_run_some _ ht, pure_bind]
      _ = _ := evalDist_bind_congr_of_support _ _ _ fun z hz ↦ by rw [keep hz ht, pure_bind]
  | none =>
    cases ht' : cache t' with
    | some v' =>
      calc _ = 𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦ f z.1 v' z.2] :=
            evalDist_bind_congr_of_support _ _ _ fun z hz ↦ by rw [keep hz ht', pure_bind]
        _ = _ := by rw [QueryImpl.withCaching_run_some _ ht', pure_bind]
    | none =>
      have h₁ : ∀ u, (cache.cacheQuery t u) t' = none := fun u ↦
        (QueryCache.cacheQuery_of_ne _ _ (Ne.symm htt)).trans ht'
      have h₂ : ∀ u', (cache.cacheQuery t' u') t = none := fun u' ↦
        (QueryCache.cacheQuery_of_ne _ _ htt).trans ht
      simp only [QueryImpl.withCaching_run_none _ ht, QueryImpl.withCaching_run_none _ ht',
        QueryImpl.withCaching_run_none _ (h₁ _), QueryImpl.withCaching_run_none _ (h₂ _),
        bind_map_left, uniformSampleImpl_apply]
      rw [OracleComp.evalDist_bind_bind_swap]
      simp only [QueryCache.cacheQuery_comm _ htt]

/-- A query to the lazy random oracle commutes with any computation run against the same
oracle: the answer, the computation's output and the final cache have the same joint
distribution in either order. -/
theorem evalDist_run_bind_simulateQ_run_swap {α γ : Type} [MeasurableSpace γ] (t : ι₀)
    (oa : OracleComp spec₀ α) (cache : spec₀.QueryCache)
    (f : spec₀.Range t → α → spec₀.QueryCache → ProbComp γ) :
    𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦
        (simulateQ spec₀.randomOracle oa).run z.2 >>= fun w ↦ f z.1 w.1 w.2] =
      𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (spec₀.randomOracle t).run w.2 >>= fun z ↦ f z.1 w.1 z.2] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t' k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rw [evalDist_run_bind_run_swap t t' cache fun u u' c ↦
      (simulateQ spec₀.randomOracle (k u')).run c >>= fun w ↦ f u w.1 w.2]
    exact evalDist_bind_congr_of_support _ _ _ fun y _ ↦ ih y.1 y.2

end randomOracle
