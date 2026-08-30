/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Evolution
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Targets

/-!
# Online Stability Invariant for Stateful Merkle Extraction

The predictable-target stopping theorem needs a semantic good-state invariant. `StableAt` says
that every immutable checkpoint still extracts the same partial tree at the current cumulative
log. It is true initially, is preserved by re-querying a cached entry, and is preserved by a fresh
response outside the live target union computed before that response was sampled. At a phase
boundary, recording the newly emitted root establishes stability for the new checkpoint as well.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open BinaryTree

variable {Cfg Query Address Y : Type}

/-- Every recorded checkpoint extraction agrees with re-extraction at `log`. -/
def ExtractorState.StableAt [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  ∀ tag checkpoint, ⟨tag, checkpoint⟩ ∈ state.checkpoints →
    checkpoint.extractedTree view =
      MerkleTreeExtractor.tree view (config.skeleton tag) (config.addressKey tag)
        log checkpoint.root

/-- The empty checkpoint history is stable at every log. -/
theorem ExtractorState.stableAt_empty [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (config : Configuration Cfg Address)
    (log : MerkleTreeExtractor.QueryLog Query Y) :
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config).StableAt view log := by
  intro tag checkpoint hcheckpoint
  simp at hcheckpoint

/-- A cached log append preserves stability because the exact entry already appeared in the log. -/
theorem ExtractorState.StableAt.append_cached
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log)
    (query : Query) (response : Y)
    (hmem : (⟨query, response⟩ : (_query : Query) × Y) ∈ log) :
    state.StableAt view (log ++ [⟨query, response⟩]) := by
  intro tag checkpoint hcheckpoint
  rw [hstable tag checkpoint hcheckpoint]
  exact (tree_append_singleton_eq_of_mem view (config.skeleton tag)
    (config.addressKey tag) log checkpoint.root ⟨query, response⟩ hmem).symm

/-- A fresh response outside the pre-sample live target union cannot change any recorded
checkpoint extraction. -/
theorem ExtractorState.StableAt.append_of_not_mem_liveTargetSet
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log)
    (query : Query) (response : Y)
    (hresponse : response ∉ state.liveTargetSet view log) :
    state.StableAt view (log ++ [⟨query, response⟩]) := by
  intro tag checkpoint hcheckpoint
  rw [hstable tag checkpoint hcheckpoint]
  apply not_ne_iff.mp
  intro hchanged
  apply hresponse
  simp only [ExtractorState.liveTargetSet, List.mem_toFinset,
    ExtractorState.liveTargetList, List.mem_flatMap]
  refine ⟨⟨tag, checkpoint⟩, hcheckpoint, ?_⟩
  exact tree_ne_append_singleton_implies_response_mem_targets view
    (config.skeleton tag) (config.addressKey tag) log checkpoint.root query response hchanged

/-- Recording a root at a stable phase boundary preserves all old equalities and makes the new
checkpoint stable by construction. -/
theorem ExtractorState.StableAt.record
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    (hstable : state.StableAt view (state.cumulativeLog ++ phaseLog)) :
    (state.record tag phaseLog root).StableAt view
      (state.cumulativeLog ++ phaseLog) := by
  intro recordedTag checkpoint hcheckpoint
  rw [ExtractorState.record_checkpoints] at hcheckpoint
  rcases List.mem_append.mp hcheckpoint with hold | hnew
  · exact hstable recordedTag checkpoint hold
  · simp only [List.mem_singleton] at hnew
    cases hnew
    rfl

/-- Proof-facing cumulative-log form of `StableAt.record`. -/
theorem ExtractorState.StableAt.recordCumulative
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    (tag : Cfg) (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    (hstable : state.StableAt view cumulativeLog) :
    (state.recordCumulative tag cumulativeLog root).StableAt view cumulativeLog := by
  intro recordedTag checkpoint hcheckpoint
  rw [ExtractorState.recordCumulative_checkpoints] at hcheckpoint
  rcases List.mem_append.mp hcheckpoint with hold | hnew
  · exact hstable recordedTag checkpoint hold
  · simp only [List.mem_singleton] at hnew
    cases hnew
    rfl

/-- Stability rules out the checkpoint-versus-terminal branch at the same log. -/
theorem ExtractorState.StableAt.not_hasCheckpointTerminalExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : state.StableAt view (state.terminalLog terminalSuffix)) :
    ¬ HasCheckpointTerminalExtractionDisagreement view state terminalSuffix := by
  rintro ⟨tag, checkpoint, hcheckpoint, hdisagreement⟩
  exact hdisagreement (hstable tag checkpoint hcheckpoint)

/-- At a common stable log, two checkpoints with the same configuration and root necessarily
extract the same tree. -/
theorem ExtractorState.StableAt.not_hasEqualRootExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log) :
    ¬ HasEqualRootExtractionDisagreement view state := by
  rintro ⟨tag, left, right, hleft, hright, hroot, hne⟩
  apply hne
  rw [hstable tag left hleft, hstable tag right hright, hroot]

/-- Under terminal stability, the strongest three-branch event reduces exactly to accepted-opening
disagreement. This is stronger than the public two-branch reduction: equal-root inconsistency is
also impossible at one common stable log. -/
theorem failure_iff_hasAcceptedOpeningDisagreement_of_stableAt
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : state.StableAt view (state.terminalLog terminalSuffix)) :
    Failure view state attempts terminalSuffix ↔
      HasAcceptedOpeningDisagreement view state attempts := by
  simp only [Failure]
  have hnoEqual := hstable.not_hasEqualRootExtractionDisagreement view
  have hnoTerminal :=
    hstable.not_hasCheckpointTerminalExtractionDisagreement view terminalSuffix
  tauto

/-- The textbook two-branch event has the same accepted-opening normal form under stability. -/
theorem textbookFailure_iff_hasAcceptedOpeningDisagreement_of_stableAt
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : state.StableAt view terminalLog) :
    TextbookFailure view state attempts ↔
      HasAcceptedOpeningDisagreement view state attempts := by
  simp only [TextbookFailure]
  have hnoEqual := hstable.not_hasEqualRootExtractionDisagreement view
  tauto

end MerkleTreeMultiExtractability
