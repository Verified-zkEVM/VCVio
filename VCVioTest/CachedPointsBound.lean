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
program querying `0`, `2` and `1` is charged only for its queries at points of `D = {0, 1}`, so its
budget is `2` although it makes three queries. Every run caches all three points, so the bound `2`
on the cached points of `D` is attained, and the uncharged point `2` lies outside `D`.
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

/-- The charged points. -/
def D : Set ℕ := {k | k < 2}

/-- Query the points `0`, `2` and `1`. -/
def threeQueries : OracleComp natSpec Bool := do
  let _ ← natSpec.query 0
  let _ ← natSpec.query 2
  natSpec.query 1

/-- `threeQueries` makes two queries at points of `D`. -/
theorem isQueryBoundP_threeQueries : IsQueryBoundP threeQueries (· < 2) 2 := by
  simp [threeQueries]

/-- Every run of `threeQueries` from the empty cache caches at most two points of `D`. -/
theorem encard_inter_cached_le {z : Bool × natSpec.QueryCache}
    (hz : z ∈ support ((simulateQ natSpec.randomOracle threeQueries).run ∅)) :
    (D ∩ cached z.2).encard ≤ 2 := by
  simpa [cached] using
    randomOracle_cachesOnlyQueryPoint.encard_inter_le_add_of_mem_support_simulateQ
      (D := D) (fun _ _ h hk ↦ Option.some_inj.1 h ▸ hk) isQueryBoundP_threeQueries hz

/-- Every run of `threeQueries` caches all three of its points. -/
theorem mem_cached {z : Bool × natSpec.QueryCache}
    (hz : z ∈ support ((simulateQ natSpec.randomOracle threeQueries).run ∅)) :
    ({0, 1, 2} : Set ℕ) ⊆ cached z.2 := by
  rw [threeQueries, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨w₀, hw₀, hz⟩ := hz
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w₂, hw₂, hz⟩ := hz
  rw [simulateQ_spec_query] at hz
  have h₀ := (QueryImpl.withCaching_run_isSome_apply_iff _ hw₀ 0).2 (Or.inr rfl)
  have h₂ := (QueryImpl.withCaching_run_isSome_apply_iff _ hw₂ 2).2 (Or.inr rfl)
  have h₀ := (QueryImpl.withCaching_run_isSome_apply_iff _ hw₂ 0).2 (Or.inl h₀)
  rintro k (rfl | rfl | rfl)
  · exact (QueryImpl.withCaching_run_isSome_apply_iff _ hz 0).2 (Or.inl h₀)
  · exact (QueryImpl.withCaching_run_isSome_apply_iff _ hz 1).2 (Or.inr rfl)
  · exact (QueryImpl.withCaching_run_isSome_apply_iff _ hz 2).2 (Or.inl h₂)

/-- Every run of `threeQueries` caches both points of `D`, so the bound is attained. -/
theorem encard_inter_cached_eq {z : Bool × natSpec.QueryCache}
    (hz : z ∈ support ((simulateQ natSpec.randomOracle threeQueries).run ∅)) :
    (D ∩ cached z.2).encard = 2 := by
  refine le_antisymm (encard_inter_cached_le hz) ?_
  have hsub : ({0, 1} : Set ℕ) ⊆ D ∩ cached z.2 := by
    rintro k (rfl | rfl)
    · exact ⟨by simp [D], mem_cached hz (by simp)⟩
    · exact ⟨by simp [D], mem_cached hz (by simp)⟩
  calc (2 : ℕ∞) = ({0, 1} : Set ℕ).encard := by
        rw [Set.encard_pair (by decide)]
    _ ≤ (D ∩ cached z.2).encard := Set.encard_le_encard hsub

/-- The uncharged point `2` is cached on every run of `threeQueries`, outside `D`. -/
theorem two_mem_cached_diff {z : Bool × natSpec.QueryCache}
    (hz : z ∈ support ((simulateQ natSpec.randomOracle threeQueries).run ∅)) :
    2 ∈ cached z.2 \ D :=
  ⟨mem_cached hz (by simp), by simp [D]⟩

end VCVioTest.CachedPointsBound
