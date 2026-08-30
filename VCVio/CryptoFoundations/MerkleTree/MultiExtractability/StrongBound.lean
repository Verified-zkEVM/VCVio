/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Endgame
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.InitializedBound
public import VCVio.OracleComp.QueryTracking.Unpredictability

/-!
# Strong Multi-Extractability Bound

This module connects the generic sequential stopping theorem to the executable stateful game.
The sole remaining semantic interface is `TerminalStrongBound`: after all commitment checkpoints
have been recorded, it bounds terminal opening production plus honest batch verification under
the exact cache/log/stability invariants maintained by the online proof.

The finite-maximum theorem owns the security statement.  The textbook event, coarse binomial
bound, and quadratic bound are corollaries.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y : Type}

/-- Terminal opening production, honest verification, and transcript assembly. -/
def Adversary.terminalExecution [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) (Transcript Cfg Query Address Y config) := do
  let (claims, terminalSuffix) ←
    (adversary.opening privateState extractorState).withQueryLog
  let attempts ← verifyClaims model claims
  return { extractorState, attempts, terminalSuffix }

/-- The executable inner game is the initialized sequential runner followed by
`terminalExecution`. -/
theorem extractabilityInner_eq_runFromEmptyThen [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    extractabilityInner model config rounds adversary =
      adversary.committer.runFromEmptyThen config rounds
        (adversary.terminalExecution model) := rfl

/-- Pointwise terminal theorem required by sequential composition.  This named interface makes
the last cryptographic obligation auditable: no checkpoint evolution or query accounting is
hidden inside it. -/
def Adversary.TerminalStrongBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead terminalQueryBound : ℕ) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (terminalCached : ℕ) (cache : (Query →ₒ Y).QueryCache)
      (log : (Query →ₒ Y).QueryLog),
    state.cumulativeLog = log →
    ¬ CacheHasCollision cache →
    (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
      ∀ input, cache input ≠ none → input ∈ keys) →
    (∀ entry ∈ log, cache entry.1 = some entry.2) →
    (∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
    state.StableAt model.view log →
    state.totalNodeBudget ≤ nodeBudget →
    state.checkpoints.length ≤ checkpointCount →
    Pr[ fun z => StrongFailure model z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (adversary.terminalExecution model privateState state)).run cache] ≤
      (multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        terminalQueryBound terminalCached : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹

/-- Deterministic terminal reduction needed for the concrete ROM estimate.  Every strong failure
must add, under a previously empty complete-query key, one value that was already live in the
checkpoint extractor at the beginning of the terminal phase. -/
def Adversary.TerminalFreshTargetProperty
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
      (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache),
    state.cumulativeLog = log →
    ¬ CacheHasCollision cache →
    (∀ entry ∈ log, cache entry.1 = some entry.2) →
    (∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
    state.StableAt model.view log →
    z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache) →
    StrongFailure model z.1 →
    ∃ target ∈ state.liveTargetSet model.view log,
      MerkleTreeExtractability.CacheAddsValue cache z.2 target

/-- A total terminal query bound plus the deterministic fresh-target reduction discharges the
probabilistic `TerminalStrongBound` interface.  This theorem contains the entire terminal random-
oracle calculation; proving a concrete game secure is reduced to the support-level Merkle lemma
`TerminalFreshTargetProperty`. -/
theorem Adversary.terminalStrongBound_of_freshTarget
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead terminalQueryBound : ℕ)
    (hbound : ∀ privateState state,
      IsTotalQueryBound (adversary.terminalExecution model privateState state)
        (terminalQueryBound + verifierOverhead))
    (hfresh : adversary.TerminalFreshTargetProperty model) :
    adversary.TerminalStrongBound model nodeBudget checkpointCount verifierOverhead
      terminalQueryBound := by
  intro privateState state terminalCached cache log hstateLog hno hcacheBound hlogCache
    hcacheLog hstable hnodeBudget hcheckpointCount
  let targets := state.liveTargetSet model.view log
  have htargets : targets.card ≤
      sharedTargetCount nodeBudget checkpointCount terminalCached := by
    obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
    apply (state.liveTargetSet_card_le_sharedTargetCount_of_cover model.view log cache keys
      terminalCached hkeysCard {
        log_agrees := fun query response hentry => hlogCache ⟨query, response⟩ hentry
        cache_keys := hkeysMem }).trans
    exact sharedTargetCount_mono_budget hnodeBudget hcheckpointCount
  have hhit :
      Pr[ fun z => StrongFailure model z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle
          (adversary.terminalExecution model privateState state)).run cache] ≤
        Pr[ fun z => ∃ target ∈ targets, ∃ input : Query, ∃ value : Y,
          z.2 input = some value ∧ cache input = none ∧ value = target |
          (simulateQ (Query →ₒ Y).cachingOracle
            (adversary.terminalExecution model privateState state)).run cache] := by
    apply probEvent_mono
    intro z hz hfailure
    obtain ⟨target, htarget, input, hfinal, hinitial⟩ :=
      hfresh privateState state cache log z hstateLog hno hlogCache hcacheLog hstable hz hfailure
    exact ⟨target, htarget, input, target, hfinal, hinitial, rfl⟩
  have hprob := OracleComp.probEvent_cache_hits_targets_le_of_noCollision_homogeneous
    (adversary.terminalExecution model privateState state)
    (terminalQueryBound + verifierOverhead) (hbound privateState state) targets cache hno
  refine hhit.trans (hprob.trans ?_)
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Nat.mul_le_mul_right (terminalQueryBound + verifierOverhead) htargets).trans
      (multiExtractabilitySafePotential_terminal_le nodeBudget checkpointCount verifierOverhead
        terminalQueryBound terminalCached)
  · exact zero_le

/-- **Strongest game-level finite-maximum theorem.**

The adversary may choose configuration tags, roots, and terminal batch selectors adaptively.
Every phase shares one cached homogeneous random oracle.  The hypotheses expose exactly the
uniform structural resources required for a finite public bound. -/
theorem strongFailure_rom_bound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
      perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState) phaseQueryBound)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount)
    (hterminal : adversary.TerminalStrongBound model nodeBudget checkpointCount
      verifierOverhead terminalQueryBound) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  have hraw := adversary.committer.probEvent_runFromEmptyThen_le model.view config
    (adversary.terminalExecution model) (StrongFailure model) paddingQuery
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
    hcommit perCheckpoint hconfig hterminal rounds hnodes hcheckpoints
  rw [extractabilityGame, OracleSpec.withCacheOverlay, StateT.run'_eq,
    extractabilityInner_eq_runFromEmptyThen, probEvent_map]
  simpa [Function.comp_def] using hraw

/-- Game-level theorem with no probabilistic terminal premise.  A structural query bound and the
support-wise fresh-target reduction imply the strongest finite-maximum ROM bound. -/
theorem strongFailure_rom_bound_of_freshTarget
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
      perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState) phaseQueryBound)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount)
    (hterminalBound : ∀ privateState state,
      IsTotalQueryBound (adversary.terminalExecution model privateState state)
        (terminalQueryBound + verifierOverhead))
    (hfresh : adversary.TerminalFreshTargetProperty model) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound model config rounds adversary paddingQuery phaseQueryBound
    terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint hcommit hconfig
    hnodes hcheckpoints
    (adversary.terminalStrongBound_of_freshTarget model nodeBudget checkpointCount
      verifierOverhead terminalQueryBound hterminalBound hfresh)

/-- Exact uniform-shape specialization of the strongest game-level theorem. -/
theorem strongFailure_rom_bound_exact
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState) phaseQueryBound)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hterminal : adversary.TerminalStrongBound model (rounds * perCheckpoint) rounds
      verifierOverhead terminalQueryBound) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator (rounds * perCheckpoint) rounds verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound model config rounds adversary paddingQuery phaseQueryBound
    terminalQueryBound (rounds * perCheckpoint) rounds verifierOverhead perCheckpoint
    hcommit hconfig le_rfl le_rfl hterminal

/-- The public textbook failure event inherits the strongest finite-maximum bound. -/
theorem publicFailure_rom_bound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ)
    (hstrong :
      Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹) :
    Pr[ PublicFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  publicFailure_bound_of_strongFailure_bound model config rounds adversary _ hstrong

/-- Coarse binomial corollary of the strongest finite-maximum bound. -/
theorem strongFailure_rom_bound_coarse
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ)
    (hstrong :
      Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      ((queryBound.choose 2 + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  refine hstrong.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiExtractabilitySafeNumerator_le_coarse nodeBudget checkpointCount
    verifierOverhead queryBound

/-- Quadratic corollary of the strongest finite-maximum bound. -/
theorem strongFailure_rom_bound_quadratic
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ)
    (hstrong :
      Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      ((queryBound * queryBound + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  refine hstrong.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiExtractabilitySafeNumerator_le_quadratic nodeBudget checkpointCount
    verifierOverhead queryBound

end MerkleTreeMultiExtractability
