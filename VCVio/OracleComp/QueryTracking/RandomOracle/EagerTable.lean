/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
public import VCVio.EvalDist.Monad.UniformTable

/-!
# Lazy Random Oracle Equals Eager Full-Table Sampling

For an oracle specification `D →ₒ R` with a single constant range `R`, running an
`OracleComp (D →ₒ R) α` under the lazy random oracle (`OracleSpec.randomOracle`,
i.e. `uniformSampleImpl.withCaching`) has the same output distribution as the eager
strategy: sample a *full* answer table `f : D → R` uniformly, then evaluate the
computation deterministically against `f` via `evalWithAnswerFn`.

The lazy oracle samples a fresh uniform value on first query and caches it for
consistency, so caching only ever affects *repeated* queries. Since every fresh
table entry is uniform and independent, lazily sampling on demand is
distributionally identical to pre-sampling the whole table. The marginalization
lemma `evalDist_bind_bind_update_map` is the workhorse: it absorbs each
fresh on-demand uniform draw into the pre-sampled table.

## Main results

* `evalDist_simulateQ_randomOracle_run'_eq_tableExtending`: the generalized,
  cache-parametrized form, the induction vehicle.
* `evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable`: the empty-cache
  corollary — the lazy-vs-eager equivalence proper.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory


universe u v w

namespace OracleComp

variable {D R : Type}

/-- The total answer table obtained by overlaying a `QueryCache` on top of a full function table:
cached entries take priority, uncached coordinates fall through to `g`. -/
@[reducible] def tableExtending (c : (D →ₒ R).QueryCache) (g : D → R) : D → R :=
  fun t => (c t).getD (g t)

/-- Overlaying the empty cache leaves a full table unchanged. -/
lemma tableExtending_empty (g : D → R) :
    tableExtending (∅ : (D →ₒ R).QueryCache) g = g := by
  funext t; simp [tableExtending]

variable [DecidableEq D]

/-- Overlaying `c.cacheQuery t u` on `g` is the `t`-update of overlaying `c` on `g`. -/
lemma tableExtending_cacheQuery (c : (D →ₒ R).QueryCache) (g : D → R)
    (t : D) (u : R) :
    tableExtending (c.cacheQuery t u) g = Function.update (tableExtending c g) t u := by
  funext t'
  by_cases ht : t' = t <;> simp_all [tableExtending, QueryCache.cacheQuery, Function.update]

/-- When `t` is uncached, updating the overlaid table at `t` equals overlaying the cache on the
updated full table. -/
lemma tableExtending_update_of_none (c : (D →ₒ R).QueryCache) (g : D → R)
    {t : D} (hc : c t = none) (u : R) :
    Function.update (tableExtending c g) t u = tableExtending c (Function.update g t u) := by
  funext t'
  rcases eq_or_ne t' t with rfl | ht <;> simp_all [tableExtending]

variable [SampleableType R] [SampleableType (D → R)]

variable [Finite D]

/-- **Marginalization, post-composed.** For any continuation `ψ : (D → R) → α`, drawing a fresh
uniform `u`, then a full uniform table `g`, and evaluating `ψ` on `Function.update g t u` has the
same distribution as evaluating `ψ` on a directly drawn uniform table. -/
lemma evalDist_uniformSample_bind_update_map {α : Type}
    [MeasurableSpace R] [DiscreteMeasurableSpace R]
    [MeasurableSpace α] [EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (hValue : 𝒟[$ᵗ R] = ProbabilityTheory.uniformOn Set.univ)
    (hTable : 𝒟[$ᵗ (D → R)] = ProbabilityTheory.uniformOn Set.univ)
    (t : D) (ψ : (D → R) → α) :
    𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (ψ (Function.update g t u))] =
      𝒟[do let g ← $ᵗ (D → R); pure (ψ g)] := by
  exact evalDist_bind_bind_update_map ($ᵗ R) ($ᵗ (D → R))
    hValue hTable t ψ

/-- **Two-cell marginalization, post-composed.** For any continuation `ψ : (D → R) → α` and any
two distinct coordinates `t₁ ≠ t₂`, drawing fresh independent uniforms `u₁, u₂`, then a full
uniform table `g`, and evaluating `ψ` on the table with both coordinates overwritten yields the
same distribution as evaluating `ψ` on a directly drawn uniform table.

This is the joint marginal independence at the coordinate pair `(t₁, t₂)`: those two coordinates
are jointly uniform and independent of the rest, so replacing them with fresh independent uniforms
leaves the joint distribution unchanged. Two-cell analogue of
`evalDist_uniformSample_bind_update_map`.

Used at the slot-positive case of the DC unlinkability reduction to marginalize the two cells
`((tag, 0), n)` (read by M) and `((tag, slotK), n)` (read by S, with `slotK ≠ 0`) as independent
uniforms, enabling the IH-rename closure without any per-step cacheBadReader charge. -/
lemma evalDist_uniformSample_bind_update_two_map {α : Type}
    [MeasurableSpace R] [DiscreteMeasurableSpace R]
    [MeasurableSpace α] [EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (hValue : 𝒟[$ᵗ R] = ProbabilityTheory.uniformOn Set.univ)
    (hTable : 𝒟[$ᵗ (D → R)] = ProbabilityTheory.uniformOn Set.univ)
    {t₁ t₂ : D} (hne : t₁ ≠ t₂) (ψ : (D → R) → α) :
    𝒟[do let u₁ ← $ᵗ R; let u₂ ← $ᵗ R; let g ← $ᵗ (D → R);
         pure (ψ (Function.update (Function.update g t₁ u₁) t₂ u₂))] =
      𝒟[do let g ← $ᵗ (D → R); pure (ψ g)] := by
  exact evalDist_bind_bind_bind_update_two_map ($ᵗ R) ($ᵗ (D → R))
    hValue hTable hne ψ

/-- **Lazy random oracle equals eager full-table sampling — cache-parametrized form.**

Running `oa` under the lazy random oracle starting from cache `c` yields the same output
distribution as: sample a full table `g : D → R` uniformly, then evaluate `oa` deterministically
against the table that overlays `c` on `g`.

This is the induction vehicle: the cache `c` is generalized so the `query`/`bind` step can recurse
through `cacheQuery`. -/
theorem evalDist_simulateQ_randomOracle_run'_eq_tableExtending
    {α : Type} [MeasurableSpace α] (oa : OracleComp (D →ₒ R) α)
    (c : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle oa).run' c] =
      𝒟[do let g ← $ᵗ (D → R);
            pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g)) oa)] := by
  exact evalDist_simulateQ_randomOracle_run'_eq_completeTable oa c

/-- **Lazy random oracle equals eager full-table sampling.**

Running an `OracleComp (D →ₒ R) α` under the lazy random oracle from the empty cache yields the
same output distribution as: sample a full answer table `g : D → R` uniformly, then evaluate the
computation deterministically against `g`.

This is the empty-cache specialization of
`evalDist_simulateQ_randomOracle_run'_eq_tableExtending`: the classic lazy-vs-eager-sampling
equivalence. Lazy caching only affects repeated queries, and since each fresh table entry is
uniform and independent, sampling on demand matches pre-sampling the whole table. -/
theorem evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable
    {α : Type} [MeasurableSpace α] (oa : OracleComp (D →ₒ R) α) :
    𝒟[(simulateQ randomOracle oa).run' ∅] =
      𝒟[do let g ← $ᵗ (D → R); pure (evalWithAnswerFn (QueryImpl.ofFn g) oa)] := by
  rw [evalDist_simulateQ_randomOracle_run'_eq_tableExtending oa ∅]
  simp_rw [tableExtending_empty]

end OracleComp
