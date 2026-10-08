/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Counter
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Cached points of a lazy random oracle against its query budget

The lazy random oracle on `ℕ` caches only the point of each query, so the generic bound
`QueryImpl.CachesOnlyQueryPoint.encard_inter_le_add_of_mem_support_simulateQ` applies to it. A
program querying `0` and then `1` has budget `2` and leaves both points cached on every run, so
the bound `2` on the cached points is attained.
-/

public section

namespace VCVioTest.CachedPointsBound

open OracleComp OracleSpec

/-- A random oracle on `ℕ` with Boolean answers. -/
abbrev natSpec : OracleSpec ℕ := fun _ ↦ Bool

/-- The cached points of a cache. -/
def cached (c : natSpec.QueryCache) : Set ℕ := {t | (c t).isSome}

/-- The lazy random oracle caches only the point of its query. -/
theorem randomOracle_cachesOnlyQueryPoint :
    QueryImpl.CachesOnlyQueryPoint natSpec.randomOracle cached some := by
  intro t c w hw k hk
  exact ((QueryImpl.withCaching_run_isSome_apply_iff _ hw k).1 hk).imp id fun h ↦ by
    subst h
    rfl

/-- Query the points `0` and `1`. -/
def twoQueries : OracleComp natSpec Bool := do
  let _ ← natSpec.query 0
  natSpec.query 1

/-- `twoQueries` makes two queries. -/
theorem isQueryBoundP_twoQueries : IsQueryBoundP twoQueries (fun _ ↦ True) 2 := by
  simp [twoQueries]

/-- Every run of `twoQueries` from the empty cache caches at most two points. -/
theorem encard_cached_le {z : Bool × natSpec.QueryCache}
    (hz : z ∈ support ((simulateQ natSpec.randomOracle twoQueries).run ∅)) :
    (cached z.2).encard ≤ 2 := by
  simpa [cached] using
    randomOracle_cachesOnlyQueryPoint.encard_inter_le_add_of_mem_support_simulateQ
      (D := Set.univ) (fun _ _ _ _ ↦ trivial) isQueryBoundP_twoQueries hz

/-- Every run of `twoQueries` caches both of its points, so the bound is attained. -/
theorem encard_cached_eq {z : Bool × natSpec.QueryCache}
    (hz : z ∈ support ((simulateQ natSpec.randomOracle twoQueries).run ∅)) :
    (cached z.2).encard = 2 := by
  refine le_antisymm (encard_cached_le hz) ?_
  rw [twoQueries, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [simulateQ_spec_query] at hz
  have h1 := (QueryImpl.withCaching_run_isSome_apply_iff _ hz 1).2 (Or.inr rfl)
  have h0 := (QueryImpl.withCaching_run_isSome_apply_iff _ hz 0).2
    (Or.inl ((QueryImpl.withCaching_run_isSome_apply_iff _ hw 0).2 (Or.inr rfl)))
  have hsub : ({0, 1} : Set ℕ) ⊆ cached z.2 := by
    rintro k (rfl | rfl)
    · exact h0
    · exact h1
  calc (2 : ℕ∞) = ({0, 1} : Set ℕ).encard := by
        rw [Set.encard_pair (by decide)]
    _ ≤ (cached z.2).encard := Set.encard_le_encard hsub

end VCVioTest.CachedPointsBound
