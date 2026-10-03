/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.EvalDist.Monad.DependentTable

/-!
# Cached random oracles with dependent answer spaces

For finite oracle domains, lazy cached sampling agrees with sampling a complete dependent table
and then executing the actual oracle computation against that table. Coordinates may have
different answer types. The cache-parametrized equality retains initially cached answers.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace OracleComp

variable {D α : Type} {R : D → Type}

/-- Complete a cache with a total table, retaining every cached answer. -/
@[expose] def completeTable (c : (OracleSpec.ofFn R).QueryCache) (g : ∀ d, R d) : ∀ d, R d :=
  fun t => (c t).getD (g t)

/-- Completing an empty cache returns the supplied table. -/
theorem completeTable_empty (g : ∀ d, R d) :
    completeTable (∅ : (OracleSpec.ofFn R).QueryCache) g = g := by
  funext t
  simp [completeTable]

/-- Adding a cached answer updates the completed table at that coordinate. -/
theorem completeTable_cacheQuery [DecidableEq D]
    (c : (OracleSpec.ofFn R).QueryCache) (g : ∀ d, R d) (t : D) (u : R t) :
    completeTable (c.cacheQuery t u) g = Function.update (completeTable c g) t u := by
  funext t'
  by_cases ht : t' = t
  · subst t'
    simp [completeTable]
  · simp [completeTable, QueryCache.cacheQuery_of_ne _ _ ht, Function.update_of_ne ht]

/-- Updating an uncached coordinate commutes with cache completion. -/
theorem completeTable_update_of_none [DecidableEq D]
    (c : (OracleSpec.ofFn R).QueryCache) (g : ∀ d, R d)
    {t : D} (hc : c t = none) (u : R t) :
    Function.update (completeTable c g) t u = completeTable c (Function.update g t u) := by
  funext t'
  by_cases ht : t' = t
  · subst t'
    simp [completeTable, hc]
  · simp [completeTable, Function.update_of_ne ht]

/-- Caching the answer already supplied by the completed table changes nothing. -/
theorem completeTable_cacheQuery_value [DecidableEq D]
    (c : (OracleSpec.ofFn R).QueryCache) (g : (d : D) → R d) (t : D) :
    completeTable (c.cacheQuery t (completeTable c g t)) g = completeTable c g := by
  rw [completeTable_cacheQuery, Function.update_eq_self]

/-- A cached answer hides any change to its fallback table cell. -/
theorem completeTable_update_of_some [DecidableEq D]
    (c : (OracleSpec.ofFn R).QueryCache) (g : (d : D) → R d)
    {t : D} {v : R t} (hc : c t = some v) (u : R t) :
    completeTable c (Function.update g t u) = completeTable c g := by
  funext t'
  by_cases ht : t' = t
  · subst t'
    simp [completeTable, hc]
  · simp [completeTable, Function.update_of_ne ht]


variable [DecidableEq D] [Finite D] [∀ d, Finite (R d)] [∀ d, Nonempty (R d)]
  [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]

omit [Finite D] [∀ d, Finite (R d)] [∀ d, Nonempty (R d)] in
/-- Pure-case base step for `evalDist_simulateQ_randomOracle_run'_eq_completeTable`: running
`pure a` under the lazy oracle ignores the table, so its distribution is the constant `pure a`,
matching the eager side after the (discarded) uniform table draw. -/
private lemma evalDist_simulateQ_randomOracle_run'_pure_eq_completeTable
    {α : Type} [MeasurableSpace α] (a : α) (c : (OracleSpec.ofFn R).QueryCache) :
    𝒟[(simulateQ randomOracle (pure a : OracleComp (OracleSpec.ofFn R) α)).run' c] =
      𝒟[do let g ← $ᵗ (∀ d, R d);
            pure (evalWithAnswerFn (QueryImpl.ofFn (completeTable c g)) (pure a))] := by
  let : MeasurableSpace (∀ d, R d) := ⊤
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
    evalWithAnswerFn_pure]
  rw [OracleComp.evalDist_bind_const]

/-- Inductive `query`/`bind` step for `evalDist_simulateQ_randomOracle_run'_eq_completeTable`:
given the eager-table identity for every continuation `k u`, it holds for `liftM (query t) >>= k`.
On a cache miss the fresh uniform draw is absorbed into the table by
`evalDist_uniformSample_bind_update_map`; on a cache hit the table already answers with `c t`. -/
private lemma evalDist_simulateQ_randomOracle_run'_query_bind_eq_completeTable
    {α : Type} [MeasurableSpace α] (t : D)
    (k : R t → OracleComp (OracleSpec.ofFn R) α)
    (ih : ∀ (u : R t) (c : (OracleSpec.ofFn R).QueryCache),
      𝒟[(simulateQ randomOracle (k u)).run' c] =
        𝒟[do let g ← $ᵗ (∀ d, R d);
              pure (evalWithAnswerFn (QueryImpl.ofFn (completeTable c g)) (k u))])
    (c : (OracleSpec.ofFn R).QueryCache) :
    𝒟[(simulateQ randomOracle (liftM ((OracleSpec.ofFn R).query t) >>= k)).run' c] =
      𝒟[do let g ← $ᵗ (∀ d, R d);
            pure (evalWithAnswerFn (QueryImpl.ofFn (completeTable c g))
              (liftM ((OracleSpec.ofFn R).query t) >>= k))] := by
  classical
  let : ∀ d, Fintype (R d) := fun d => Fintype.ofFinite (R d)
  have : Nonempty (∀ d, R d) := ⟨fun d => Classical.arbitrary (R d)⟩
  let : ∀ d, MeasurableSpace (R d) := fun _ => ⊤
  have hred :
      (simulateQ randomOracle (liftM ((OracleSpec.ofFn R).query t) >>= k)).run' c
        = ((randomOracle (spec := (OracleSpec.ofFn R)) t).run c) >>=
          fun p : R t × (OracleSpec.ofFn R).QueryCache =>
            (simulateQ randomOracle (k p.1)).run' p.2 := by
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rfl
  have heval : ∀ g : (d : D) → R d,
      evalWithAnswerFn (QueryImpl.ofFn (completeTable c g))
          (liftM ((OracleSpec.ofFn R).query t) >>= k)
        = evalWithAnswerFn (QueryImpl.ofFn (completeTable c g))
            (k (completeTable c g t)) := by
    intro g
    rw [evalWithAnswerFn_bind]
    simp only [evalWithAnswerFn, simulateQ_spec_query, QueryImpl.ofFn_apply]
  rw [hred]
  simp_rw [heval]
  rcases hc : c t with _ | u
  · rw [QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp]
    simp only [Function.comp, bind_assoc, pure_bind]
    set ψ : (∀ d, R d) → α := fun g' =>
      evalWithAnswerFn (QueryImpl.ofFn (completeTable c g')) (k (completeTable c g' t))
      with hψ
    have hfun : ∀ u : R t, (fun g : (d : D) → R d =>
          evalWithAnswerFn (QueryImpl.ofFn (completeTable (c.cacheQuery t u) g)) (k u))
        = fun g : (d : D) → R d => ψ (Function.update g t u) := by
      intro u
      funext g
      simp only [hψ]
      rw [completeTable_cacheQuery, ← completeTable_update_of_none c g hc u]
      simp only [Function.update_self]
    trans 𝒟[do let u ← $ᵗ (R t); let g ← $ᵗ (∀ d, R d); pure (ψ (Function.update g t u))]
    · rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      apply Measure.bind_congr_right
      filter_upwards [] with u
      rw [ih u (c.cacheQuery t u), bind_pure_comp, bind_pure_comp, hfun u]
    · exact evalDist_bind_bind_update_map_dependent t ($ᵗ (R t)) ($ᵗ (∀ d, R d))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample ψ
  · rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih u c]
    have h : ∀ g : (d : D) → R d, completeTable c g t = u := fun g => by simp [completeTable, hc]
    simp_rw [h]

/-- **Lazy random oracle equals eager full-table sampling — cache-parametrized form.**

Running `oa` under the lazy random oracle starting from cache `c` yields the same output
distribution as: sample a full table `g : (d : D) → R d` uniformly, then evaluate `oa`
deterministically
against the table that overlays `c` on `g`.

This is the induction vehicle: the cache `c` is generalized so the `query`/`bind` step can recurse
through `cacheQuery`. -/
theorem evalDist_simulateQ_randomOracle_run'_eq_completeTable
    {α : Type} [MeasurableSpace α] (oa : OracleComp (OracleSpec.ofFn R) α)
    (c : (OracleSpec.ofFn R).QueryCache) :
    𝒟[(simulateQ randomOracle oa).run' c] =
      𝒟[do let g ← $ᵗ (∀ d, R d);
            pure (evalWithAnswerFn (QueryImpl.ofFn (completeTable c g)) oa)] := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => exact evalDist_simulateQ_randomOracle_run'_pure_eq_completeTable a c
  | query_bind t k ih =>
    exact evalDist_simulateQ_randomOracle_run'_query_bind_eq_completeTable t k ih c



end OracleComp
