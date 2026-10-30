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
continuation of the answers and the final cache. Queries at distinct points none of which is
cached are answered with independent uniform values and change the cache only at those points.

## Main statements

- `randomOracle.evalDist_run_bind_run_swap`: two lazy random-oracle queries commute.
- `randomOracle.evalDist_run_bind_simulateQ_run_swap`: a lazy random-oracle query commutes with
  every computation run against the same oracle.
- `randomOracle.evalDist_simulateQ_queryAll_run_bind_of_perm`: querying the lazy random oracle at
  the indices of a list depends, through the final cache, only on the list up to permutation.
- `randomOracle.fst_map_run_list_mapM_of_fresh`: querying the lazy random function oracle at
  distinct uncached points answers with independent uniform values, and
  `randomOracle.run_list_mapM_apply_of_forall_ne`: it changes the cache only at those points.
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

/-- Querying the lazy random oracle at the indices of a list leaves a final cache whose
distribution is unchanged when the list is permuted. -/
theorem evalDist_simulateQ_queryAll_run_bind_of_perm {γ : Type} [MeasurableSpace γ]
    {ts ts' : List ι₀} (h : ts.Perm ts') (cache : spec₀.QueryCache)
    (f : spec₀.QueryCache → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle (spec₀.queryAll ts)).run cache >>= fun w ↦ f w.2] =
      𝒟[(simulateQ spec₀.randomOracle (spec₀.queryAll ts')).run cache >>= fun w ↦ f w.2] := by
  induction h generalizing cache with
  | nil => rfl
  | cons t _ ih =>
    simp only [OracleSpec.queryAll_cons, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind, bind_assoc]
    exact evalDist_bind_congr_of_support _ _ _ fun z _ ↦ ih z.2
  | swap t t' ts =>
    simp only [OracleSpec.queryAll_cons, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind, bind_assoc]
    exact evalDist_run_bind_run_swap t' t cache fun _ _ c ↦
      (simulateQ spec₀.randomOracle (spec₀.queryAll ts)).run c >>= fun w ↦ f w.2
  | trans _ _ ih₁ ih₂ => exact (ih₁ cache).trans (ih₂ cache)

/-- A query to the lazy random oracle at `s` leaves the cache unchanged at every other index. -/
theorem run_apply_of_ne {s t : ι₀} (hst : s ≠ t) (cache : spec₀.QueryCache)
    {z : spec₀.Range s × spec₀.QueryCache} (hz : z ∈ support ((spec₀.randomOracle s).run cache)) :
    z.2 t = cache t := by
  rw [QueryImpl.withCaching_run_eq_cacheQuery uniformSampleImpl hz]
  exact QueryCache.cacheQuery_of_ne _ _ hst.symm

end randomOracle

namespace randomOracle

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- Querying the lazy random function oracle at the points `f x`, for `x` in a list, leaves the
cache unchanged at every point that is none of them. -/
theorem run_list_mapM_apply_of_forall_ne {α : Type} (f : α → D) (xs : List α) {t : D}
    (ht : ∀ x ∈ xs, f x ≠ t) (cache : (D →ₒ R).QueryCache) {z : List R × (D →ₒ R).QueryCache}
    (hz : z ∈ support ((xs.mapM fun x => (D →ₒ R).randomOracle (f x)).run cache)) :
    z.2 t = cache t := by
  induction xs generalizing cache z with
  | nil => simp_all
  | cons x xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    rw [ih (fun y hy => ht y (List.mem_cons_of_mem _ hy)) a.2 hb]
    exact run_apply_of_ne (ht x List.mem_cons_self) cache ha

/-- **Fresh distinct points of the lazy random function oracle are independent and uniform.**
Querying it at distinct points `f x`, for `x` in a list, none of them cached, answers with
independent uniform values. -/
theorem fst_map_run_list_mapM_of_fresh {α : Type} (f : α → D) (xs : List α)
    (hnd : (xs.map f).Nodup) (cache : (D →ₒ R).QueryCache)
    (hfresh : ∀ x ∈ xs, cache (f x) = none) :
    Prod.fst <$> (xs.mapM fun x => (D →ₒ R).randomOracle (f x)).run cache =
      xs.mapM fun _ => ($ᵗ R : ProbComp R) := by
  induction xs generalizing cache with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mapM_cons, StateT.run_bind, run_eq, hfresh x List.mem_cons_self]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u => ?_
    have hf : ∀ y ∈ xs, (cache.cacheQuery (f x) u) (f y) = none := fun y hy => by
      rw [QueryCache.cacheQuery_of_ne]
      · exact hfresh y (List.mem_cons_of_mem _ hy)
      · intro h; exact hnd.1 (h ▸ List.mem_map_of_mem hy)
    rw [← ih hnd.2 _ hf]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, StateT.run_pure]

end randomOracle
