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
They also exercise the bound in a strictly nonzero universe.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace VCVioTest.Unpredictability

universe u

section UniversePolymorphism

variable {ι : Type (u + 1)} [DecidableEq ι] [Inhabited ι]
  {spec : OracleSpec.{u + 1, u + 1} ι} [spec.DecidableEq] [IsUniformSpec spec]

/-- The finite-target bound applies to a genuine fresh query when the oracle's indices,
responses, and computation result live in an arbitrary nonzero universe. The singleton target
is reachable by the query at `default`, so this is not merely an elaboration-only `#check`. -/
example (v₀ : spec.Range default)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    0 < Pr[fun z => ∃ target ∈ ({v₀} : Finset (spec.Range default)),
          ∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            z.2 t₀ = some v ∧ (∅ : QueryCache spec) t₀ = none ∧ HEq v target |
        (simulateQ cachingOracle
          (liftM (spec.query default) : OracleComp spec (spec.Range default))).run ∅] ∧
      Pr[fun z => ∃ target ∈ ({v₀} : Finset (spec.Range default)),
          ∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            z.2 t₀ = some v ∧ (∅ : QueryCache spec) t₀ = none ∧ HEq v target |
        (simulateQ cachingOracle
          (liftM (spec.query default) : OracleComp spec (spec.Range default))).run ∅] ≤
        ((({v₀} : Finset (spec.Range default)).card * 1 : ℕ) : ℝ≥0∞) *
          (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  constructor
  · rw [probEvent_pos_iff]
    refine ⟨(v₀, (∅ : QueryCache spec).cacheQuery default v₀), ?_, ?_⟩
    · simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rw [cachingOracle.run_none (by simp), support_map]
      exact ⟨v₀, by simp, rfl⟩
    · exact ⟨v₀, by simp, default, v₀, by simp, by simp, HEq.rfl⟩
  · apply probEvent_cache_hits_targets_le_of_noCollision
    · rw [← bind_pure
          (liftM (spec.query default) : OracleComp spec (spec.Range default)),
        isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.one_pos, fun _ ↦ trivial⟩
    · exact hrange
    · rintro ⟨t₀, t₁, w₀, w₁, _, hcache, _, _⟩
      simp at hcache

end UniversePolymorphism

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
