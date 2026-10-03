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

/-- A cell-resampling bound for every background table bounds bad output by the expected
weight of the distinct hash keys in the actual cached run. Hash inputs may range over an
infinite domain. Private uniform sampling stays interleaved and uncached; returned failures
retain their full query cost. The trace implication uses the very same output, ordered log,
and answer assignment. -/
theorem prEvent_randomOracle_le_expectedFreshQueryCharge [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (event : α → Prop) (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (htrace : ∀ g z, z ∈ support (fixedTableLoggedRun oa g ∅) →
      event z.1.1 → ∃ t ∈ freshKeysOfLog z.1.2, bad t g)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t) :
    Pr{let z ← randomOracleLoggedRun oa}[event z.1.1] ≤
      expectedFreshQueryCharge oa error := by
  classical
  let S := possibleRandomOracleKeys oa
  let hS := allQueriesSatisfy_possibleRandomOracleKeys oa
  let small := restrictRandomOracleQueries S oa hS
  have hrun := randomOracleLoggedRun_restrictCache S oa hS ∅
  simp only [restrictCache_empty] at hrun
  rw [← hrun, prEvent_map]
  rw [← expectedFreshQueryCharge_restrict S oa hS error]
  let : ∀ t : S, Fintype (R t.val) := fun t => Fintype.ofFinite (R t.val)
  let : SampleableType (∀ t : S, R t.val) := SampleableType.piOfFintype _
  apply prEvent_interleavedFreshBad_le_expectedCharge small event
    (fun t g => bad t.val (extendTable S g)) (fun t : S => error t.val)
  · intro g z hz hevent
    let full := extendTable S g
    have hext : (fun t : S => full t.val) = g := by
      funext t
      exact extendTable_subtype S g t
    have hfixed := fixedTableLoggedRun_restrictCache S full oa hS ∅
    simp only [restrictCache_empty, hext] at hfixed
    have hsource : extendLoggedResult S ∅ z ∈ support (fixedTableLoggedRun oa full ∅) := by
      rw [← hfixed, support_map]
      exact Set.mem_image_of_mem _ hz
    obtain ⟨t, ht, hb⟩ := htrace full (extendLoggedResult S ∅ z) hsource hevent
    change t ∈ freshKeysOfLog (extendLog S z.1.2) at ht
    rw [freshKeysOfLog_extendLog, Finset.mem_map] at ht
    obtain ⟨smallt, hsmallt, heq⟩ := ht
    subst t
    exact ⟨smallt, hsmallt, hb⟩
  · intro t g
    simp_rw [extendTable_update]
    exact hbad t.val (extendTable S g)

end OracleComp
