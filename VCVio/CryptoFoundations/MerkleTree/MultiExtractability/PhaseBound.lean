/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.OnlineBound
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.OnlineInvariant

/-!
# One Stateful Merkle Commitment Phase

This module instantiates the generic predictable-target theorem with the semantic live targets and
stability invariant of an immutable extractor checkpoint state. The terminal hypothesis uses the
same potential at the remaining resource state, so a caller may record the phase output and invoke
the theorem recursively for the next commitment phase.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y X R C : Type}

/-- A stateful phase is bounded by the safe shared-target potential. Every local hypothesis is
phrased in terms of the actual immutable checkpoint state; in particular, the target-cardinality
obligation is discharged by `liveTargetSet_card_le_sharedTargetCount_of_cover`. -/
theorem probEvent_stablePhaseRunFrom_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (suffix : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) R)
    (continuation : X → OracleComp (Query →ₒ Y) C)
    (win : R → Prop) (overhead : ℕ)
    (prefixComp : OracleComp (Query →ₒ Y) X)
    (remaining cached : ℕ)
    (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (Query →ₒ Y).QueryCache)
    (log : (Query →ₒ Y).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt view log)
    (hterminal : ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (Query →ₒ Y).QueryCache)
        (terminalLog : (Query →ₒ Y).QueryLog),
      IsTotalQueryBound (continuation x) terminalRemaining →
      ¬ CacheHasCollision terminalCache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, terminalCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
      (∀ input value, terminalCache input = some value →
        ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
      state.StableAt view terminalLog →
      Pr[ fun z => win z.1 | (simulateQ (Query →ₒ Y).cachingOracle
          (suffix x terminalLog)).run terminalCache] ≤
        (multiExtractabilitySafePotential state.totalNodeBudget state.checkpoints.length
          overhead terminalRemaining terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr[ fun z => win z.1 |
      adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
        suffix prefixComp cache log] ≤
      (multiExtractabilitySafePotential state.totalNodeBudget state.checkpoints.length
        overhead remaining cached : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  apply probEvent_onlineAdaptivePrefixRunFrom_le suffix continuation win
    (state.liveTargetSet view) (fun _ currentLog => state.StableAt view currentLog)
    state.totalNodeBudget state.checkpoints.length overhead prefixComp remaining cached hbound
    cache log hno hcacheBound hlogCache hcacheLog hstable
  · intro currentCache currentLog query response hstableCurrent hresponse hcacheLogCurrent
    obtain ⟨⟨entryQuery, entryValue⟩, hentry, hquery, hvalue⟩ :=
      hcacheLogCurrent query response hresponse
    have hentryEq :
        (⟨entryQuery, entryValue⟩ : (_query : Query) × Y) = ⟨query, response⟩ := by
      rw [Sigma.ext_iff]
      exact ⟨hquery, heq_of_eq hvalue⟩
    rw [← hentryEq]
    exact hstableCurrent.append_cached view entryQuery entryValue hentry
  · intro currentCache currentLog query response hstableCurrent _hnone _hno hresponse
    exact hstableCurrent.append_of_not_mem_liveTargetSet view query response hresponse
  · intro currentCached currentCache currentLog hkeys hlogCacheCurrent _hcacheLogCurrent _
    obtain ⟨keys, hkeysCard, hkeysMem⟩ := hkeys
    exact state.liveTargetSet_card_le_sharedTargetCount_of_cover view currentLog currentCache
      keys currentCached hkeysCard {
        log_agrees := fun query response hentry =>
          hlogCacheCurrent ⟨query, response⟩ hentry
        cache_keys := hkeysMem }
  · exact hterminal

end MerkleTreeMultiExtractability
