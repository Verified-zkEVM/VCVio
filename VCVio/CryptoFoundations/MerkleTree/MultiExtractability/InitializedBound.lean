/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.SequentialBound

/-!
# Initialized Sequential Merkle Bounds

This module initializes the stateful stopping theorem at the empty cache, log, and extractor
history.  The finite-maximum safe numerator is the owner statement.  Coarse binomial and
quadratic bounds are derived only by monotonicity, so they cannot diverge from the executable
sequential semantics.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y R : Type}

/-- Run a fixed commitment prefix from the canonical private and extractor states, then execute
the terminal computation supplied by the caller. -/
def SequentialCommitter.runFromEmptyThen
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R) : OracleComp (Query →ₒ Y) R :=
  committer.runCommitmentsThen rounds 0 committer.initialState ExtractorState.empty finish

/-- Empty-state specialization of the strongest sequential predictable-target theorem.

`nodeBudget` and `checkpointCount` remain caller-chosen uniform envelopes.  Taking them to be
`rounds * perCheckpoint` and `rounds` gives the exact structural corollary below; larger values
support heterogeneous configurations or a deliberately coarser public interface. -/
theorem SequentialCommitter.probEvent_runFromEmptyThen_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (config : Configuration Cfg Address)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (win : R → Prop) (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound : ℕ)
    (nodeBudget checkpointCount verifierOverhead : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (committer.commit round privateState) phaseQueryBound)
    (perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hfinish : ∀ privateState
        (state : ExtractorState Cfg Query Address Y config)
        (terminalCached : ℕ)
        (cache : (Query →ₒ Y).QueryCache)
        (log : (Query →ₒ Y).QueryLog),
      state.cumulativeLog = log →
      ¬ CacheHasCollision cache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, cache input ≠ none → input ∈ keys) →
      (∀ entry ∈ log, cache entry.1 = some entry.2) →
      (∀ input value, cache input = some value →
        ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
      state.StableAt view log →
      Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle (finish privateState state)).run cache] ≤
        (multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
          terminalQueryBound terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹)
    (rounds : ℕ)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (committer.runFromEmptyThen config rounds finish)).run ∅] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  apply committer.probEvent_runCommitmentsThen_le view finish win paddingQuery
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
    hcommit perCheckpoint hconfig hfinish rounds 0 committer.initialState ExtractorState.empty
    (∅ : (Query →ₒ Y).QueryCache) []
    (rounds * phaseQueryBound + terminalQueryBound) 0 (by omega) rfl
  · rintro ⟨_, _, _, _, _, hcached, _, _⟩
    simp at hcached
  · exact ⟨∅, by simp, fun input hinput => (hinput (by simp)).elim⟩
  · simp
  · simp
  · exact ExtractorState.stableAt_empty view config []
  · simpa [ExtractorState.totalNodeBudget, nodeBudgetOfCheckpoints] using hnodes
  · simpa using hcheckpoints

/-- Exact uniform-structure form: one checkpoint per round and at most `perCheckpoint` nodes per
checkpoint. -/
theorem SequentialCommitter.probEvent_runFromEmptyThen_exact_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (config : Configuration Cfg Address)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (win : R → Prop) (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (committer.commit round privateState) phaseQueryBound)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (rounds : ℕ)
    (hfinish : ∀ privateState
        (state : ExtractorState Cfg Query Address Y config)
        (terminalCached : ℕ)
        (cache : (Query →ₒ Y).QueryCache)
        (log : (Query →ₒ Y).QueryLog),
      state.cumulativeLog = log →
      ¬ CacheHasCollision cache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, cache input ≠ none → input ∈ keys) →
      (∀ entry ∈ log, cache entry.1 = some entry.2) →
      (∀ input value, cache input = some value →
        ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
      state.StableAt view log →
      Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle (finish privateState state)).run cache] ≤
        (multiExtractabilitySafePotential (rounds * perCheckpoint) rounds verifierOverhead
          terminalQueryBound terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (committer.runFromEmptyThen config rounds finish)).run ∅] ≤
      (multiExtractabilitySafeNumerator (rounds * perCheckpoint) rounds verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  exact committer.probEvent_runFromEmptyThen_le view config finish win paddingQuery
    phaseQueryBound terminalQueryBound (rounds * perCheckpoint) rounds verifierOverhead
    hcommit perCheckpoint hconfig hfinish rounds le_rfl le_rfl

/-- Coarse binomial relaxation of the initialized finite-maximum theorem. -/
theorem SequentialCommitter.probEvent_runFromEmptyThen_coarse_le
    [DecidableEq Query]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (win : R → Prop)
    (phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead rounds : ℕ)
    (hstrong :
      Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle
          (committer.runFromEmptyThen config rounds finish)).run ∅] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (committer.runFromEmptyThen config rounds finish)).run ∅] ≤
      (((rounds * phaseQueryBound + terminalQueryBound).choose 2 +
          nodeBudget * (rounds * phaseQueryBound + terminalQueryBound + verifierOverhead) : ℕ) :
        ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  refine hstrong.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiExtractabilitySafeNumerator_le_coarse nodeBudget checkpointCount
    verifierOverhead (rounds * phaseQueryBound + terminalQueryBound)

/-- Quadratic relaxation of the initialized finite-maximum theorem. -/
theorem SequentialCommitter.probEvent_runFromEmptyThen_quadratic_le
    [DecidableEq Query]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (win : R → Prop)
    (phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead rounds : ℕ)
    (hstrong :
      Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle
          (committer.runFromEmptyThen config rounds finish)).run ∅] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (committer.runFromEmptyThen config rounds finish)).run ∅] ≤
      (((rounds * phaseQueryBound + terminalQueryBound) *
            (rounds * phaseQueryBound + terminalQueryBound) +
          nodeBudget * (rounds * phaseQueryBound + terminalQueryBound + verifierOverhead) : ℕ) :
        ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  refine hstrong.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiExtractabilitySafeNumerator_le_quadratic nodeBudget checkpointCount
    verifierOverhead (rounds * phaseQueryBound + terminalQueryBound)

end MerkleTreeMultiExtractability
