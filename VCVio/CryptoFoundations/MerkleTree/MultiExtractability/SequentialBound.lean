/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.PhaseExecution
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.ResourceBounds
public import VCVio.OracleComp.QueryTracking.ReservedBudget

/-!
# Sequential Composition of Stateful Merkle Phases

This module composes the one-phase predictable-target theorem across a fixed number of commitment
rounds. A public per-round schedule is summed over the executed round interval. The proof-only
`reserveQueries` continuation reserves the exact budget of later phases, allowing the stopping
induction to expose a residual counter even though the executable terminal strategy may depend on
the accumulated extractor state.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y R : Type}

/-- Run a sequential commitment suffix and then a caller-supplied terminal computation. -/
def SequentialCommitter.runCommitmentsThen
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address}
    (rounds firstRound : ℕ) (privateState : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R) : OracleComp (Query →ₒ Y) R := do
  let (finalPrivateState, finalExtractorState) ←
    committer.runCommitments rounds firstRound privateState extractorState
  finish finalPrivateState finalExtractorState

/-- Exact adversarial query budget for `rounds` consecutive commitment phases beginning at
`firstRound`, allowing a different public budget at every round. -/
def commitmentQueryBudget (phaseBudget : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | rounds + 1, firstRound =>
      phaseBudget firstRound + commitmentQueryBudget phaseBudget rounds (firstRound + 1)

/-- A constant phase schedule recovers the former uniform `rounds * phaseBudget` accounting. -/
@[simp]
theorem commitmentQueryBudget_const (phaseBudget rounds firstRound : ℕ) :
    commitmentQueryBudget (fun _ => phaseBudget) rounds firstRound = rounds * phaseBudget := by
  induction rounds generalizing firstRound with
  | zero => simp [commitmentQueryBudget]
  | succ rounds ih =>
      simp [commitmentQueryBudget, ih, Nat.succ_mul, Nat.add_comm]

/-- **Sequential predictable-target composition theorem.**

The scheduled form keeps one shared cache, one global node/checkpoint envelope, and one safe
potential across every phase. `finish` is abstract: the next module instantiates its pointwise
terminal bound with opening production and honest addressed batch verification. -/
theorem SequentialCommitter.probEvent_runCommitmentsThen_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (win : R → Prop)
    (paddingQuery : Query)
    (phaseQueryBound : ℕ → ℕ) (terminalQueryBound : ℕ)
    (nodeBudget checkpointCount verifierOverhead : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (committer.commit round privateState) (phaseQueryBound round))
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
      state.totalNodeBudget ≤ nodeBudget →
      state.checkpoints.length ≤ checkpointCount →
      Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle (finish privateState state)).run cache] ≤
        (multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
          terminalQueryBound terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹)
    (rounds firstRound : ℕ) (privateState : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (cache : (Query →ₒ Y).QueryCache)
    (log : (Query →ₒ Y).QueryLog)
    (remaining cachedBound : ℕ)
    (hbudget : commitmentQueryBudget phaseQueryBound rounds firstRound +
      terminalQueryBound ≤ remaining)
    (hstateLog : extractorState.cumulativeLog = log)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query,
      keys.card ≤ cachedBound ∧
        ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : extractorState.StableAt view log)
    (hnodes : extractorState.totalNodeBudget + rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : extractorState.checkpoints.length + rounds ≤ checkpointCount) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (committer.runCommitmentsThen rounds firstRound privateState extractorState finish)).run
          cache] ≤
      (multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        remaining cachedBound : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  induction rounds generalizing firstRound privateState extractorState cache log remaining
      cachedBound with
  | zero =>
      have hnodes0 : extractorState.totalNodeBudget ≤ nodeBudget := by simpa using hnodes
      have hcheckpoints0 : extractorState.checkpoints.length ≤ checkpointCount := by
        simpa using hcheckpoints
      have hterminal := hfinish privateState extractorState cachedBound cache log
        hstateLog hno hcacheBound hlogCache hcacheLog hstable hnodes0 hcheckpoints0
      have hremaining : terminalQueryBound ≤ remaining := by
        simpa [commitmentQueryBudget] using hbudget
      have hbase : Pr[ fun z => win z.1 |
          (simulateQ (Query →ₒ Y).cachingOracle
            (committer.runCommitmentsThen 0 firstRound privateState extractorState finish)).run
              cache] ≤
          (multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
            terminalQueryBound cachedBound : ENNReal) *
              (Nat.card Y : ENNReal)⁻¹ := by
        simpa [SequentialCommitter.runCommitmentsThen] using hterminal
      refine hbase.trans ?_
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast multiExtractabilitySafePotential_mono_remaining
          nodeBudget checkpointCount verifierOverhead cachedBound hremaining
      · exact zero_le
  | succ rounds ih =>
      subst log
      let futureBudget := commitmentQueryBudget phaseQueryBound rounds (firstRound + 1) +
        terminalQueryBound
      unfold SequentialCommitter.runCommitmentsThen
      simp only [SequentialCommitter.runCommitments]
      rw [bind_assoc]
      change Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle
          ((committer.commit firstRound privateState).withQueryLog >>= fun phaseResult =>
            committer.runCommitmentsThen rounds (firstRound + 1) phaseResult.1.2.2
              (extractorState.record phaseResult.1.1 phaseResult.2 phaseResult.1.2.1)
              finish)).run cache] ≤ _
      rw [← adaptivePrefixRunFrom_commit_eq extractorState
        (committer.commit firstRound privateState)
        (fun output nextExtractorState =>
          committer.runCommitmentsThen rounds (firstRound + 1) output.2.2
            nextExtractorState finish) cache]
      apply probEvent_stablePhaseRunFrom_le view extractorState
        (fun output currentLog =>
          committer.runCommitmentsThen rounds (firstRound + 1) output.2.2
            (extractorState.recordCumulative output.1 currentLog output.2.1) finish)
        (fun _ => reserveQueries paddingQuery futureBudget) win
        nodeBudget checkpointCount verifierOverhead
        (committer.commit firstRound privateState) remaining cachedBound
      · apply (isTotalQueryBound_bind (hcommit firstRound privateState)
          (fun _ => reserveQueries_isTotalQueryBound paddingQuery futureBudget)).mono
        dsimp only [futureBudget]
        simpa only [commitmentQueryBudget, Nat.add_assoc] using hbudget
      · exact hno
      · exact hcacheBound
      · exact hlogCache
      · exact hcacheLog
      · exact hstable
      · omega
      · omega
      · intro output terminalRemaining terminalCached terminalCache terminalLog
          hreserved hno' hcacheBound' hlogCache' hcacheLog' hstable'
        obtain ⟨tag, root, nextPrivateState⟩ := output
        have hfuture : futureBudget ≤ terminalRemaining :=
          (reserveQueries_isTotalQueryBound_iff paddingQuery futureBudget terminalRemaining).1
            hreserved
        refine ih (firstRound := firstRound + 1) (privateState := nextPrivateState)
          (extractorState := extractorState.recordCumulative tag terminalLog root)
          (cache := terminalCache) (log := terminalLog)
          (remaining := terminalRemaining) (cachedBound := terminalCached)
          hfuture (ExtractorState.recordCumulative_cumulativeLog _ _ _ _)
          hno' hcacheBound' hlogCache' hcacheLog'
          (hstable'.recordCumulative view tag terminalLog root) ?_ ?_
        · rw [ExtractorState.totalNodeBudget_recordCumulative]
          have htag := hconfig tag
          simp only [Nat.add_mul, one_mul] at hnodes
          omega
        · simp only [ExtractorState.recordCumulative_checkpoints, List.length_append,
            List.length_singleton]
          omega

end MerkleTreeMultiExtractability
