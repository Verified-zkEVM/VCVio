/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.Unpredictability

/-!
# ROM Unpredictability Canaries

These examples pin the finite-target random-oracle bound, including its use of the number of
distinct target values rather than the number of positions from which those values were collected.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace VCVioTest.Unpredictability

abbrev TestSpec : OracleSpec Bool := Bool →ₒ Fin 4

noncomputable instance : IsUniformSpec TestSpec :=
  IsUniformSpec.ofFintypeInhabited TestSpec

def oneQuery : OracleComp TestSpec Unit := do
  let _ ← (TestSpec.query false : OracleComp TestSpec (Fin 4))
  return ()

private lemma oneQuery_totalBound : IsTotalQueryBound oneQuery 1 := by
  rw [oneQuery, isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

def twoTargets : Finset (Fin 4) := {0, 1}

@[simp] lemma twoTargets_card : twoTargets.card = 2 := by
  decide

/-- A single fresh query hitting either of two distinct outputs receives the expected
`2 / 4` upper bound. This rejects accidentally dropping the target-cardinality factor. -/
example :
    Pr[fun z => ∃ v₀ ∈ twoTargets, ∃ t₀ : TestSpec.Domain, ∃ v : TestSpec.Range t₀,
        z.2 t₀ = some v ∧ (∅ : QueryCache TestSpec) t₀ = none ∧ HEq v v₀ |
      (simulateQ TestSpec.cachingOracle oneQuery).run ∅] ≤
      (2 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ := by
  simpa [twoTargets] using
    (probEvent_cache_hits_targets_le_of_noCollision
      (oa := oneQuery) (n := 1) oneQuery_totalBound (by intro t; cases t <;> exact le_rfl)
      twoTargets (∅ : QueryCache TestSpec) (by
        intro ⟨_, _, _, _, _, hcache, _, _⟩
        simp at hcache))

def initialCache : QueryCache TestSpec :=
  (∅ : QueryCache TestSpec).cacheQuery true 0

/-- The unique-preimage theorem permits a target value to occur once in the initial cache and
still bounds a fresh second preimage. This rejects silently strengthening freshness to require
that no target value was present before the residual phase. -/
example :
    Pr[fun z => ∃ v₀ ∈ twoTargets, ∃ t₀ : TestSpec.Domain, ∃ v : TestSpec.Range t₀,
        z.2 t₀ = some v ∧ initialCache t₀ = none ∧ HEq v v₀ |
      (simulateQ TestSpec.cachingOracle oneQuery).run initialCache] ≤
      (2 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ := by
  simpa [twoTargets] using
    (probEvent_cache_hits_targets_le_of_unique_preimage
      (oa := oneQuery) (n := 1) oneQuery_totalBound (by intro t; cases t <;> exact le_rfl)
      twoTargets initialCache (by
        intro _ _ t₀ t₁ v₁ v₂ hcache₀ hcache₁ _ _
        cases t₀ <;> cases t₁ <;> simp [initialCache] at hcache₀ hcache₁ ⊢))

/-- Deduplicating positional labels records two semantic target values, not three positions. -/
example : ({0, 1, 0} : Finset (Fin 4)).card = 2 := by
  decide

end VCVioTest.Unpredictability
