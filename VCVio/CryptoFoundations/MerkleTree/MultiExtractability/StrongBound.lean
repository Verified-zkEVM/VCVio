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
`TerminalStrongBound` is an internal decomposition boundary: after all commitment checkpoints
have been recorded, it isolates terminal opening production plus honest batch verification under
the exact cache/log/stability invariants maintained by the online proof. The final theorems
discharge it from executable query bounds and honest-verifier semantics.

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

/-- Proof-only terminal computation used to account exactly the adversary's opening work while
excluding honest verification. The cumulative log argument is intentionally ignored here: it is
needed by the generic residual runner to select continuations, while the adversary already
receives the equivalent extractor state. -/
def Adversary.openingAccountingFinish
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (_log : (Query →ₒ Y).QueryLog) : OracleComp (Query →ₒ Y) Unit := do
  let _claims ← adversary.opening privateState extractorState
  pure ()

/-- The residual accounting runner is exactly the previously exposed whole-adversary prefix
program. Consequently, clients state one ordinary global query bound and never mention the
proof-only logged runner. -/
theorem Adversary.runCommitmentsThenAccounting_opening_eq_prefixProgram
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) (rounds : ℕ) :
    adversary.committer.runCommitmentsThenAccounting adversary.openingAccountingFinish
        rounds 0 adversary.committer.initialState
        (ExtractorState.empty : ExtractorState Cfg Query Address Y config) [] =
      adversary.prefixProgram rounds := by
  rw [adversary.committer.runCommitmentsThenAccounting_eq_runCommitmentsThen
    adversary.openingAccountingFinish
    (fun privateState extractorState => do
      let _claims ← adversary.opening privateState extractorState
      pure ()) (by intros; rfl) rounds 0 adversary.committer.initialState
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config) [] rfl]
  rfl

/-- Pointwise query accounting for the executable terminal phase.  The opening computation uses
the supplied residual adversarial budget; honest verification contributes only its separately
justified support-wise overhead. Query logging itself is resource-transparent. -/
theorem Adversary.terminalExecution_isTotalQueryBound_of_opening
    [DecidableEq Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (openingBound verifierBound : ℕ)
    (hopening : IsTotalQueryBound
      (adversary.opening privateState extractorState) openingBound)
    (hverifier : adversary.HasVerifierQueryBound verifierBound) :
    IsTotalQueryBound (adversary.terminalExecution model privateState extractorState)
      (openingBound + verifierBound) := by
  unfold Adversary.terminalExecution
  apply isTotalQueryBound_bind_of_mem_support
      (prefixBound := openingBound) (suffixBound := verifierBound)
  · exact (isTotalQueryBound_withQueryLog_iff
      (adversary.opening privateState extractorState) openingBound).2
      hopening
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

/-- Uniform specialization of pointwise terminal accounting. -/
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
  exact adversary.terminalExecution_isTotalQueryBound_of_opening model privateState
    extractorState openingBound verifierBound (hopening privateState extractorState) hverifier

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

/-- A supported terminal execution retains the complete cache-level batch run for every accepted
attempt selected from its result list.  This is the generic support bridge used before applying
the pure selected-path disagreement theorem. -/
theorem Adversary.batchRunInCache_of_terminalExecution_support
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (state : ExtractorState Cfg Query Address Y config)
    (cache : (Query →ₒ Y).QueryCache)
    (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache)
    (hz : z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache))
    (tag : Cfg) (attempt : OpeningAttempt Query Y config tag)
    (hmem : (⟨tag, attempt⟩ : AnyOpeningAttempt Cfg Query Address Y config) ∈ z.1.attempts)
    (haccepted : attempt.accepted = true) :
    MerkleTreeBatchExtractability.BatchRunInCache model (config.addressKey tag) z.2
      attempt.opening.values attempt.opening.proof attempt.checkpoint.root := by
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
  exact batchRunInCache_of_mem_support_verifyClaims model claims cacheOpening cacheFinal attempts
    hverify tag attempt hmem haccepted

/-- Reverse whole-structure disagreement at a checkpoint is exactly the explicit selected-values
or pruned-proof disagreement consumed by the batch path kernel.  The selector is definitionally
shared, so the dependent payload equalities are the only two possible equality obligations. -/
theorem AcceptedOpeningDisagreement.toOpeningDisagreesWithTree
    [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    {attempt : OpeningAttempt Query Y config tag}
    (hdisagreement : AcceptedOpeningDisagreement model.view attempt) :
    MerkleTreeBatchExtractability.OpeningDisagreesWithTree attempt.opening
      (Checkpoint.extractedTree model.view attempt.checkpoint) := by
  rcases attempt with ⟨checkpoint, ⟨selector, values, proof⟩, accepted⟩
  simp only [AcceptedOpeningDisagreement] at hdisagreement
  by_contra hnot
  simp only [MerkleTreeBatchExtractability.OpeningDisagreesWithTree, not_or] at hnot
  apply hdisagreement.2
  simp only [Checkpoint.extractedOpening, InductiveMerkleTree.BatchOpening.map,
    MerkleTreeBatchExtractability.extractedOpening] at hnot ⊢
  have hvalues := not_ne_iff.mp hnot.1
  have hproof := not_ne_iff.mp hnot.2
  congr
  · exact hvalues.symm
  · exact hproof.symm

/-- Honest batch verification always supplies the selected-path cache evidence required by the
deterministic terminal extraction kernel. -/
theorem Adversary.terminalOpeningEvidenceProperty
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) :
    adversary.TerminalOpeningEvidenceProperty model := by
  intro privateState state cache z tag attempt hz hattempt _hcheckpoint hdisagreement
  let tree := Checkpoint.extractedTree model.view attempt.checkpoint
  let nodeHash := MerkleTreeBatchExtractability.cacheNodeHash model
    (config.addressKey tag) z.2 attempt.checkpoint.root
  have hrun := adversary.batchRunInCache_of_terminalExecution_support model
    privateState state cache z hz tag attempt hattempt hdisagreement.1
  have hopeningDisagrees :
      MerkleTreeBatchExtractability.OpeningDisagreesWithTree attempt.opening tree :=
    hdisagreement.toOpeningDisagreesWithTree model
  obtain ⟨index, selected, hpath⟩ :=
    hopeningDisagrees.exists_selectedValue_or_path_disagreement
      nodeHash attempt.opening tree
  refine ⟨{
    index := index
    selected := selected
    proof := batchToSingleProofAddressed nodeHash attempt.opening.values
      attempt.opening.proof index selected
    chain := ?_
    disagrees := ?_ }⟩
  · exact
      MerkleTreeBatchExtractability.chainInCache_batchToSingleProofAddressed_cacheNodeHash model
        (config.addressKey tag) z.2 attempt.checkpoint.root attempt.opening.values
        attempt.opening.proof attempt.checkpoint.root hrun index selected
  · exact hpath

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

/-- Pointwise terminal ROM estimate at the exact residual adversarial budget.  This is the
terminal interface needed by global sequential accounting: earlier commitment phases may leave a
different residual budget on every supported branch. -/
theorem Adversary.probEvent_terminalExecution_le_of_freshTarget
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead terminalRemaining terminalCached : ℕ)
    (privateState : adversary.committer.State)
    (state : ExtractorState Cfg Query Address Y config)
    (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
    (hbound : IsTotalQueryBound (adversary.terminalExecution model privateState state)
      (terminalRemaining + verifierOverhead))
    (hfresh : adversary.TerminalFreshTargetProperty model)
    (hstateLog : state.cumulativeLog = log)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ terminalCached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt model.view log)
    (hnodeBudget : state.totalNodeBudget ≤ nodeBudget)
    (hcheckpointCount : state.checkpoints.length ≤ checkpointCount) :
    Pr[ fun z => StrongFailure model z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (adversary.terminalExecution model privateState state)).run cache] ≤
      (multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        terminalRemaining terminalCached : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
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
    (terminalRemaining + verifierOverhead) hbound targets cache hno
  refine hhit.trans (hprob.trans ?_)
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Nat.mul_le_mul_right (terminalRemaining + verifierOverhead) htargets).trans
      (multiExtractabilitySafePotential_terminal_le nodeBudget checkpointCount verifierOverhead
        terminalRemaining terminalCached)
  · exact zero_le

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
  exact adversary.probEvent_terminalExecution_le_of_freshTarget model nodeBudget checkpointCount
    verifierOverhead terminalQueryBound terminalCached privateState state cache log
    (hbound privateState state) hfresh hstateLog hno hcacheBound hlogCache hcacheLog hstable
    hnodeBudget hcheckpointCount

/-- A public phase schedule plus a uniform terminal-opening bound implies one whole-adversary
query bound. This is the resource bridge used to derive the legacy scheduled theorem from the
global-`q` owner statement. -/
theorem Adversary.isAdversaryPrefixQueryBound_of_schedule
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (rounds : ℕ) (phaseQueryBound : ℕ → ℕ) (terminalQueryBound : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound) :
    adversary.IsAdversaryPrefixQueryBound rounds
      (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) := by
  unfold Adversary.IsAdversaryPrefixQueryBound Adversary.prefixProgram
  apply isTotalQueryBound_bind
  · exact adversary.committer.runCommitments_isTotalQueryBound_schedule phaseQueryBound hcommit
      rounds 0 adversary.committer.initialState
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config)
  · rintro ⟨privateState, extractorState⟩
    exact isTotalQueryBound_bind (n₁ := terminalQueryBound) (n₂ := 0)
      (hopening privateState extractorState) fun _ => trivial

/-- **Strongest executable multi-extractability theorem (one global adversarial budget).**

The single `queryBound` covers every adaptive commitment phase and terminal opening production
along each complete adversarial execution. Honest batch verification is excluded from that budget
and charged separately through `verifierOverhead`. The conclusion bounds the full three-branch
strong failure event under one shared cached homogeneous random oracle. -/
theorem strongFailure_rom_bound_global
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  have hraw := adversary.committer.probEvent_runFromEmptyThen_logged_le model.view config
    (adversary.terminalExecution model) adversary.openingAccountingFinish
    (StrongFailure model) nodeBudget checkpointCount verifierOverhead perCheckpoint hconfig
    (by
      intro privateState state terminalRemaining terminalCached cache log hopening hstateLog hno
        hcacheBound hlogCache hcacheLog hstable hnodeBudget hcheckpointCount
      have hopening' : IsTotalQueryBound
          (adversary.opening privateState state) terminalRemaining := by
        have hmapped : IsTotalQueryBound
            ((fun _ => ()) <$> adversary.opening privateState state) terminalRemaining := by
          simpa [Adversary.openingAccountingFinish, map_eq_bind_pure_comp] using hopening
        exact (isQueryBound_map_iff (adversary.opening privateState state) (fun _ => ())
          terminalRemaining _ _).mp hmapped
      exact adversary.probEvent_terminalExecution_le_of_freshTarget model nodeBudget
        checkpointCount verifierOverhead terminalRemaining terminalCached privateState state cache
        log
        (adversary.terminalExecution_isTotalQueryBound_of_opening model privateState state
          terminalRemaining verifierOverhead hopening' hverifier)
        (adversary.terminalFreshTargetProperty_of_openingEvidence model
          (adversary.terminalOpeningEvidenceProperty model))
        hstateLog hno hcacheBound hlogCache hcacheLog hstable hnodeBudget hcheckpointCount)
    rounds queryBound
    (by
      rw [adversary.runCommitmentsThenAccounting_opening_eq_prefixProgram rounds]
      exact hquery)
    hnodes hcheckpoints
  rw [extractabilityGame, OracleSpec.withCacheOverlay, StateT.run'_eq,
    extractabilityInner_eq_runFromEmptyThen, probEvent_map]
  simpa [Function.comp_def] using hraw

/-- Finite-opening specialization of the global theorem. At most `openingCount` claims whose
paths cost at most `perClaim` yield the explicit verifier overhead
`openingCount * perClaim`. -/
theorem strongFailure_rom_bound_global_of_openingCountBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount openingCount perClaim perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hopeningCount : adversary.HasOpeningCountBound openingCount)
    (hperClaim : ∀ tag, (config.skeleton tag).leafCount - 1 ≤ perClaim)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount
        (openingCount * perClaim) queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_global model config rounds adversary queryBound nodeBudget
    checkpointCount (openingCount * perClaim) perCheckpoint hquery
    (adversary.hasVerifierQueryBound_of_openingCountBound openingCount perClaim
      hopeningCount hperClaim)
    hconfig hnodes hcheckpoints

/-- Exact structural specialization of the global theorem: one checkpoint per round and at most
`perCheckpoint` nodes contributed by each selected configuration. -/
theorem strongFailure_rom_bound_global_exact
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator (rounds * perCheckpoint) rounds verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_global model config rounds adversary queryBound
    (rounds * perCheckpoint) rounds verifierOverhead perCheckpoint hquery hverifier hconfig
    le_rfl le_rfl

/-- **Scheduled game-level finite-maximum theorem.**

The adversary may choose configuration tags, roots, and terminal batch selectors adaptively.
Every phase shares one cached homogeneous random oracle.  The hypotheses expose exactly the
uniform structural resources required for a finite public bound. -/
theorem strongFailure_rom_bound_schedule
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount)
    (hterminal : adversary.TerminalStrongBound model nodeBudget checkpointCount
      verifierOverhead terminalQueryBound) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  have hraw := adversary.committer.probEvent_runFromEmptyThen_le model.view config
    (adversary.terminalExecution model) (StrongFailure model) paddingQuery
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
    hcommit perCheckpoint hconfig hterminal rounds hnodes hcheckpoints
  rw [extractabilityGame, OracleSpec.withCacheOverlay, StateT.run'_eq,
    extractabilityInner_eq_runFromEmptyThen, probEvent_map]
  simpa [Function.comp_def] using hraw

/-- Uniform-phase specialization of `strongFailure_rom_bound_schedule`. -/
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
  simpa using strongFailure_rom_bound_schedule model config rounds adversary paddingQuery
    (fun _ => phaseQueryBound) terminalQueryBound nodeBudget checkpointCount verifierOverhead
    perCheckpoint hcommit hconfig hnodes hcheckpoints hterminal

/-- Uniform-phase game theorem with no probabilistic terminal premise. A structural query bound
and the support-wise fresh-target reduction imply the finite-maximum ROM bound. -/
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

/-- Verifier-evidence interface retained as a reusable decomposition boundary. Honest batch
verification discharges this premise unconditionally below. -/
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

/-- Evidence-parameterized scheduled decomposition retained for callers that supply a custom
terminal kernel. It follows the legacy reserved-budget route; the fully discharged theorem below
instead derives the schedule from `strongFailure_rom_bound_global`. -/
theorem strongFailure_rom_bound_schedule_of_openingEvidence_and_queryBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount)
    (hevidence : adversary.TerminalOpeningEvidenceProperty model) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_schedule model config rounds adversary paddingQuery phaseQueryBound
    terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint hcommit hconfig
    hnodes hcheckpoints
    (adversary.terminalStrongBound_of_freshTarget model nodeBudget checkpointCount
      verifierOverhead terminalQueryBound
      (adversary.terminalExecution_isTotalQueryBound model terminalQueryBound verifierOverhead
        hopening hverifier)
      (adversary.terminalFreshTargetProperty_of_openingEvidence model hevidence))

/-- Fully discharged scheduled corollary of the single global-adversarial-`q` theorem. Commitment
rounds may have heterogeneous public budgets; their exact sum plus the terminal opening budget is
used only to discharge the owner theorem's whole-program query predicate. `_paddingQuery` is
retained for source compatibility with the evidence-parameterized scheduled API and is ignored. -/
theorem strongFailure_rom_bound_schedule_of_queryBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (_paddingQuery : Query)
    (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  exact strongFailure_rom_bound_global model config rounds adversary
    (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound)
    nodeBudget checkpointCount verifierOverhead perCheckpoint
    (adversary.isAdversaryPrefixQueryBound_of_schedule rounds phaseQueryBound terminalQueryBound
      hcommit hopening)
    hverifier hconfig hnodes hcheckpoints

/-- Finite-opening specialization: at most `openingCount` claims, each with path cost at most
`perClaim`, gives verifier overhead `openingCount * perClaim`. -/
theorem strongFailure_rom_bound_schedule_of_openingCountBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query) (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount openingCount perClaim perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hopeningCount : adversary.HasOpeningCountBound openingCount)
    (hperClaim : ∀ tag, (config.skeleton tag).leafCount - 1 ≤ perClaim)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount (openingCount * perClaim)
        (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_schedule_of_queryBounds model config rounds adversary paddingQuery
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount (openingCount * perClaim)
    perCheckpoint hcommit hopening
    (adversary.hasVerifierQueryBound_of_openingCountBound openingCount perClaim
      hopeningCount hperClaim)
    hconfig hnodes hcheckpoints

/-- Uniform-phase corollary of the fully discharged scheduled theorem. -/
theorem strongFailure_rom_bound_of_queryBounds
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
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  simpa using strongFailure_rom_bound_schedule_of_queryBounds model config rounds adversary
    paddingQuery (fun _ => phaseQueryBound) terminalQueryBound nodeBudget checkpointCount
    verifierOverhead perCheckpoint hcommit hopening hverifier hconfig hnodes hcheckpoints

/-- Exact uniform-shape specialization of the scheduled game-level theorem. -/
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

/-- Fully discharged exact uniform-shape corollary: one checkpoint per round and a uniform
per-checkpoint node envelope. -/
theorem strongFailure_rom_bound_exact_of_queryBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState) phaseQueryBound)
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator (rounds * perCheckpoint) rounds verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_of_queryBounds model config rounds adversary paddingQuery
    phaseQueryBound terminalQueryBound (rounds * perCheckpoint) rounds verifierOverhead
    perCheckpoint hcommit hopening hverifier hconfig le_rfl le_rfl

/-- The public textbook failure event inherits the finite-maximum bound. -/
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

/-- Coarse binomial corollary of the finite-maximum bound. -/
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

/-- Quadratic corollary of the finite-maximum bound. -/
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

/-- The textbook two-branch event as a direct corollary of the global-adversarial-`q` owner
theorem. -/
theorem publicFailure_rom_bound_global
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ PublicFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  publicFailure_rom_bound model config rounds adversary nodeBudget checkpointCount
    verifierOverhead queryBound
    (strongFailure_rom_bound_global model config rounds adversary queryBound nodeBudget
      checkpointCount verifierOverhead perCheckpoint hquery hverifier hconfig hnodes hcheckpoints)

/-- Coarse binomial relaxation of the global-adversarial-`q` theorem. -/
theorem strongFailure_rom_bound_global_coarse
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      ((queryBound.choose 2 + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_coarse model config rounds adversary nodeBudget checkpointCount
    verifierOverhead queryBound
    (strongFailure_rom_bound_global model config rounds adversary queryBound nodeBudget
      checkpointCount verifierOverhead perCheckpoint hquery hverifier hconfig hnodes hcheckpoints)

/-- Quadratic relaxation of the global-adversarial-`q` theorem. -/
theorem strongFailure_rom_bound_global_quadratic
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      ((queryBound * queryBound + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_quadratic model config rounds adversary nodeBudget checkpointCount
    verifierOverhead queryBound
    (strongFailure_rom_bound_global model config rounds adversary queryBound nodeBudget
      checkpointCount verifierOverhead perCheckpoint hquery hverifier hconfig hnodes hcheckpoints)

/-- The public/textbook two-branch event is a direct corollary of the fully discharged scheduled
strong theorem. -/
theorem publicFailure_rom_bound_schedule_of_queryBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query) (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ PublicFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  publicFailure_rom_bound model config rounds adversary nodeBudget checkpointCount
    verifierOverhead (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound)
    (strongFailure_rom_bound_schedule_of_queryBounds model config rounds adversary paddingQuery
      phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
      perCheckpoint hcommit hopening hverifier hconfig hnodes hcheckpoints)

/-- Coarse binomial relaxation derived from the fully discharged scheduled theorem. -/
theorem strongFailure_rom_bound_schedule_coarse_of_queryBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query) (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (((commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound).choose 2 +
          nodeBudget * (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound +
            verifierOverhead) : ℕ) : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_coarse model config rounds adversary nodeBudget checkpointCount
    verifierOverhead (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound)
    (strongFailure_rom_bound_schedule_of_queryBounds model config rounds adversary paddingQuery
      phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
      perCheckpoint hcommit hopening hverifier hconfig hnodes hcheckpoints)

/-- Quadratic relaxation derived from the fully discharged scheduled theorem. -/
theorem strongFailure_rom_bound_schedule_quadratic_of_queryBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query) (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (((commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) *
          (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) +
        nodeBudget * (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound +
          verifierOverhead) : ℕ) : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound_quadratic model config rounds adversary nodeBudget checkpointCount
    verifierOverhead (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound)
    (strongFailure_rom_bound_schedule_of_queryBounds model config rounds adversary paddingQuery
      phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
      perCheckpoint hcommit hopening hverifier hconfig hnodes hcheckpoints)

end MerkleTreeMultiExtractability
