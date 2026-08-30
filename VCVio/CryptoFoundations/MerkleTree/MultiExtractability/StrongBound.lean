/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Endgame
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.InitializedBound
public import VCVio.OracleComp.QueryTracking.ReservedBudget
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
open BinaryTree InductiveMerkleTree

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

/-- The executable terminal phase uses exactly the opening budget plus a support-wise bound for
honest verification. Query logging itself is resource-transparent. -/
theorem Adversary.terminalExecution_isTotalQueryBound
    [DecidableEq Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (openingBound verifierBound : ℕ)
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) openingBound)
    (hverifier : adversary.HasVerifierQueryBound verifierBound) :
    ∀ privateState extractorState,
      IsTotalQueryBound (adversary.terminalExecution model privateState extractorState)
        (openingBound + verifierBound) := by
  intro privateState extractorState
  unfold Adversary.terminalExecution
  apply isTotalQueryBound_bind_of_mem_support
      (prefixBound := openingBound) (suffixBound := verifierBound)
  · exact (isTotalQueryBound_withQueryLog_iff
      (adversary.opening privateState extractorState) openingBound).2
      (hopening privateState extractorState)
  · rintro ⟨claims, terminalSuffix⟩ hclaimsLogged
    have hclaims : claims ∈ support (adversary.opening privateState extractorState) := by
      have hmapped : claims ∈ support
          (Prod.fst <$> (adversary.opening privateState extractorState).withQueryLog) := by
        rw [support_map]
        exact ⟨(claims, terminalSuffix), hclaimsLogged, rfl⟩
      change claims ∈ support (Prod.fst <$> (simulateQ
        (Query →ₒ Y).loggingOracle
        (adversary.opening privateState extractorState)).run) at hmapped
      simpa using hmapped
    exact isTotalQueryBound_bind
      (n₁ := verifierBound) (n₂ := 0)
      ((verifyClaims_isTotalQueryBound model claims).mono
        (hverifier privateState extractorState claims hclaims))
      fun _ => trivial

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

/-- Generic cache/log facts retained by terminal execution. -/
def Adversary.TerminalTraceInvariant
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
      (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache),
    state.cumulativeLog = log →
    z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache) →
    z.1.extractorState = state ∧ cache ≤ z.2 ∧
      ∀ entry ∈ z.1.terminalSuffix, z.2 entry.1 = some entry.2

/-- The remaining Merkle-specific endgame obligation after terminal checkpoint evolution is
handled generically: under final stability, an accepted opening disagreement adds a fresh value
from the immutable checkpoint target set. -/
def Adversary.TerminalAcceptedFreshProperty
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
    state.StableAt model.view (log ++ z.1.terminalSuffix) →
    HasAcceptedOpeningDisagreement model.view state z.1.attempts →
    ∃ target ∈ state.targetSet model.view,
      MerkleTreeExtractability.CacheAddsValue cache z.2 target

/-- Support-level evidence expected from honest batch verification: every accepted disagreeing
attempt exposes the generated selected path consumed by the deterministic extraction kernel. -/
def Adversary.TerminalOpeningEvidenceProperty
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (cache : (Query →ₒ Y).QueryCache)
      (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache)
      tag (attempt : OpeningAttempt Query Y config tag),
    z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache) →
    (⟨tag, attempt⟩ : AnyOpeningAttempt Cfg Query Address Y config) ∈ z.1.attempts →
    (⟨tag, attempt.checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈
      state.checkpoints →
    AcceptedOpeningDisagreement model.view attempt →
    Nonempty (OpeningKernelEvidence model attempt z.2)

/-- Terminal execution always preserves its input extractor state, grows the shared cache, and
leaves every terminal-opening log entry in the final cache. -/
theorem Adversary.terminalTraceInvariant
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) :
    adversary.TerminalTraceInvariant model := by
  intro privateState state cache _log z _hstateLog hz
  unfold Adversary.terminalExecution at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨claims, terminalSuffix⟩, cacheOpening⟩, hopening, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨attempts, cacheFinal⟩, hverify, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst z
  have hopeningInvariant := OracleComp.log_entry_in_cache_and_mono
    (adversary.opening privateState state) cache
    ((claims, terminalSuffix), cacheOpening) hopening
  have hverifyMono : cacheOpening ≤ cacheFinal :=
    simulateQ_cachingOracle_cache_le (verifyClaims model claims) cacheOpening
      (attempts, cacheFinal) hverify
  exact ⟨rfl, hopeningInvariant.2.trans hverifyMono,
    fun entry hentry => hverifyMono (hopeningInvariant.1 entry hentry)⟩

/-- Honest-verifier path evidence implies the accepted-opening fresh-target property. -/
theorem Adversary.terminalAcceptedFreshProperty_of_openingEvidence
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (hevidence : adversary.TerminalOpeningEvidenceProperty model) :
    adversary.TerminalAcceptedFreshProperty model := by
  intro privateState state cache log z hstateLog hno hlogCache hcacheLog hstable hz
    _hstableFinal hopening
  obtain ⟨_hstate, hmono, _hsuffixFinal⟩ :=
    adversary.terminalTraceInvariant model privateState state cache log z hstateLog hz
  obtain ⟨tag, attempt, hattempt, hcheckpoint, hdisagreement⟩ := hopening
  obtain ⟨evidence⟩ :=
    hevidence privateState state cache z tag attempt hz hattempt hcheckpoint hdisagreement
  have hpathDisagreement := evidence.disagrees
  rw [hstable tag attempt.checkpoint hcheckpoint] at hpathDisagreement
  obtain ⟨target, htarget, hfresh⟩ :=
    MerkleTreeExtractability.fresh_extractedTarget_of_extractor_disagreement
      model (config.addressKey tag) evidence.index log cache z.2 attempt.checkpoint.root
      (selectedValueAt attempt.opening.values evidence.index evidence.selected) evidence.proof
      hlogCache hcacheLog hno hmono evidence.chain hpathDisagreement
  refine ⟨target, ?_, hfresh⟩
  simp only [ExtractorState.targetSet, List.mem_toFinset, ExtractorState.targetList,
    targetsOfCheckpoints, List.mem_flatMap]
  refine ⟨⟨tag, attempt.checkpoint⟩, hcheckpoint, ?_⟩
  have htargetsEq := MerkleTreeExtractor.targets_eq_of_tree_eq model.view
    (config.skeleton tag) (config.addressKey tag) attempt.checkpoint.cumulativeLog log
    attempt.checkpoint.root attempt.checkpoint.root (hstable tag attempt.checkpoint hcheckpoint)
  simpa [Checkpoint.targets] using htargetsEq.symm ▸ htarget

/-- Trace preservation, causal suffix stability, and the accepted-opening kernel together imply
the single deterministic terminal fresh-target property used by the ROM theorem. -/
theorem Adversary.terminalFreshTargetProperty_of_trace_and_accepted
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (htrace : adversary.TerminalTraceInvariant model)
    (haccepted : adversary.TerminalAcceptedFreshProperty model) :
    adversary.TerminalFreshTargetProperty model := by
  intro privateState state cache log z hstateLog hno hlogCache hcacheLog hstable hz hfailure
  obtain ⟨hstate, hmono, hsuffixFinal⟩ :=
    htrace privateState state cache log z hstateLog hz
  have hfailure' : Failure model.view state z.1.attempts z.1.terminalSuffix := by
    simpa only [StrongFailure, hstate] using hfailure
  have freshOfNotStable
      (hnotStable : ¬ state.StableAt model.view (log ++ z.1.terminalSuffix)) :
      ∃ target ∈ state.liveTargetSet model.view log,
        MerkleTreeExtractability.CacheAddsValue cache z.2 target := by
    obtain ⟨target, htarget, hfresh⟩ :=
      hstable.exists_freshTarget_of_not_stable_append model.view z.1.terminalSuffix
        cache z.2 hcacheLog hmono hsuffixFinal hnotStable
    refine ⟨target, ?_, hfresh⟩
    rwa [hstable.liveTargetSet_eq_targetSet model.view]
  rcases hfailure' with hopening | hequalRoot | hterminal
  · by_cases hstableFinal : state.StableAt model.view (log ++ z.1.terminalSuffix)
    · obtain ⟨target, htarget, hfresh⟩ := haccepted privateState state cache log z
        hstateLog hno hlogCache hcacheLog hstable hz hstableFinal hopening
      refine ⟨target, ?_, hfresh⟩
      rwa [hstable.liveTargetSet_eq_targetSet model.view]
    · exact freshOfNotStable hstableFinal
  · exact (hstable.not_hasEqualRootExtractionDisagreement model.view hequalRoot).elim
  · apply freshOfNotStable
    intro hstableFinal
    have hstableTerminal : state.StableAt model.view
        (state.terminalLog z.1.terminalSuffix) := by
      simpa [ExtractorState.terminalLog, hstateLog] using hstableFinal
    exact hstableTerminal.not_hasCheckpointTerminalExtractionDisagreement
      model.view z.1.terminalSuffix hterminal

/-- The honest-verifier evidence property alone supplies the Merkle-specific part of the complete
terminal fresh-target reduction; generic trace preservation is automatic. -/
theorem Adversary.terminalFreshTargetProperty_of_openingEvidence
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (hevidence : adversary.TerminalOpeningEvidenceProperty model) :
    adversary.TerminalFreshTargetProperty model :=
  adversary.terminalFreshTargetProperty_of_trace_and_accepted model
    (adversary.terminalTraceInvariant model)
    (adversary.terminalAcceptedFreshProperty_of_openingEvidence model hevidence)

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

/-- Strongest verifier-facing theorem: it remains only to supply the support-level selected-path
evidence exported by honest batch verification.  All probability, cache evolution, checkpoint
stability, and failure-branch reasoning is discharged internally. -/
theorem strongFailure_rom_bound_of_openingEvidence
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
    (hevidence : adversary.TerminalOpeningEvidenceProperty model) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_of_freshTarget model config rounds adversary paddingQuery
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint
    hcommit hconfig hnodes hcheckpoints hterminalBound
    (adversary.terminalFreshTargetProperty_of_openingEvidence model hevidence)

/-- Fully resource-separated verifier-facing theorem. The terminal structural budget follows from
the adversary's opening bound and the verifier overhead on claims in the opening's support. -/
theorem strongFailure_rom_bound_of_openingEvidence_and_queryBounds
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
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount)
    (hevidence : adversary.TerminalOpeningEvidenceProperty model) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_of_openingEvidence model config rounds adversary paddingQuery
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint
    hcommit hconfig hnodes hcheckpoints
    (adversary.terminalExecution_isTotalQueryBound model terminalQueryBound verifierOverhead
      hopening hverifier)
    hevidence

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
