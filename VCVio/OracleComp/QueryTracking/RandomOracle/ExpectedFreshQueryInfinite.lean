/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQuery
public import VCVio.OracleComp.QueryTracking.RandomOracle.FiniteSupport

/-!
# Expected fresh-query bounds on arbitrary random-oracle domains

A finite execution can be restricted to its finite set of possible hash keys while preserving
its returned value, ordered query log, and cache. These results transfer the finite-table
analysis to arbitrary hash-input domains; no infinite uniform answer table is sampled.
-/

public section

open OracleComp OracleSpec MeasureTheory
namespace OracleComp
variable {D α : Type} {R : D → Type}

/-- Every realized finite-domain lazy execution has the same joint result in an execution
against some fixed table, with the same initial cache. -/
theorem mem_support_fixedTableLoggedRun_of_randomOracle_finite [DecidableEq D] [Finite D]
    [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun oa cache)) :
    ∃ g, z ∈ support (fixedTableLoggedRun oa g cache) := by
  let : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  have hpos := (mem_support_iff_evalDist_singleton_pos _ z).mp hz
  rw [evalDist_randomOracleLoggedRun_eq_fixedTable_finite] at hpos
  have hs := (mem_support_iff_evalDist_singleton_pos _ z).mpr hpos
  simp only [support_bind, Set.mem_iUnion] at hs
  obtain ⟨g, _, hg⟩ := hs
  exact ⟨completeTable cache g, hg⟩

/-- Every realized cached execution, even on an infinite hash-input domain, has a fixed answer
assignment producing the identical output, ordered log, and final cache. Private samples remain
interleaved, and the initial cache is unchanged. -/
theorem mem_support_fixedTableLoggedRun_of_randomOracle [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun oa cache)) :
    ∃ g, z ∈ support (fixedTableLoggedRun oa g cache) := by
  classical
  let S := possibleRandomOracleKeys oa
  let hS := allQueriesSatisfy_possibleRandomOracleKeys oa
  let restricted := restrictRandomOracleQueries S oa hS
  have hr := randomOracleLoggedRun_restrictCache S oa hS cache
  rw [← hr, support_map] at hz
  obtain ⟨small, hsmall, heq⟩ := hz
  let : ∀ t : S, Fintype (R t.val) := fun t => Fintype.ofFinite (R t.val)
  let : SampleableType (∀ t : S, R t.val) := SampleableType.piOfFintype _
  obtain ⟨g, hg⟩ := mem_support_fixedTableLoggedRun_of_randomOracle_finite
    restricted (restrictCache S cache) small hsmall
  let full := extendTable S g
  refine ⟨full, ?_⟩
  have hf := fixedTableLoggedRun_restrictCache S full oa hS cache
  rw [← hf, support_map]
  refine ⟨small, ?_, heq⟩
  have hext : (fun t : S => full t.val) = g := by
    funext t
    exact extendTable_subtype S g t
  rw [hext]
  exact hg
end OracleComp
