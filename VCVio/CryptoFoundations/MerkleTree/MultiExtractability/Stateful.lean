/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Opening

/-!
# Stateful transcript extraction for Merkle batch openings

This module defines the deterministic state carried by a multi-commitment Merkle extractor.
Commitment phases contribute query-log segments to one cumulative transcript.  At each commitment,
the extractor records the cumulative log and the claimed root, tagged by the tree configuration in
force for that commitment.  The extracted partial tree is a pure projection of that immutable
checkpoint through `MerkleTreeExtractor.tree`.

A batch opening is the existing intrinsic, path-pruned `InductiveMerkleTree.BatchProof`, packaged
with its dependent selector and selected values.  The package does not carry a separate nonempty
hypothesis: existence of its `proof` field already implies that its selector contains a selected
leaf.

The three failure predicates are deliberately deterministic:

* `AcceptedOpeningDisagreement` says that an accepted claimed opening differs from the canonical
  opening obtained from its commitment checkpoint;
* `EqualRootExtractionDisagreement` says that two checkpoints for the same configuration and root
  yield different partial trees;
* `CheckpointTerminalExtractionDisagreement` says that a checkpoint extraction changes when the
  terminal transcript is used, covering queries made after the final commitment.

The aggregate `Failure` predicate is the disjunction used by a future random-oracle probability
theorem.  This file does not call these predicates unlikely, does not assign a query bound, and does
not claim that different configuration tags use independent random oracles.  Those are separate
game and resource-accounting obligations.

Failure events relate an opening or pair of checkpoints only within the same configuration tag.
Reuse of one root across distinct tags is outside the modeled event, even though the tags may select
different skeletons or address maps.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open BinaryTree InductiveMerkleTree

universe u v w

variable {Cfg : Type u} {Query : Type v} {Address : Type w} {Y Z : Type}
variable {s : Skeleton}

/-! ## Configurations and commitment checkpoints -/

/-- A family of Merkle configurations over a shared query view and response type.

Indexing the shape and address map by `Cfg` makes a tag determine its dependent tree type.  The
structure intentionally contains no oracle-independence assertion; domain separation between tags
must be supplied by a later oracle model. -/
structure Configuration (Cfg : Type u) (Address : Type w) where
  /-- Shape of commitments made under each configuration tag. -/
  skeleton : Cfg → Skeleton
  /-- Address assigned to every internal position under a configuration tag. -/
  addressKey : (tag : Cfg) → SkeletonInternalIndex (skeleton tag) → Address

/-- Immutable extraction input captured immediately after one commitment phase.

The `config` and `tag` parameters are phantom in the stored `root` and `cumulativeLog` fields, but
they determine the skeleton and address map used by `Checkpoint.extractedTree`. -/
structure Checkpoint (Query : Type v) (Y : Type) (config : Configuration Cfg Address)
    (tag : Cfg) where
  /-- Root emitted by the commitment phase. -/
  root : Y
  /-- Complete cumulative transcript through the end of this commitment phase. -/
  cumulativeLog : MerkleTreeExtractor.QueryLog Query Y

/-- Reconstruct the partial tree recorded by a commitment checkpoint. -/
def Checkpoint.extractedTree [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) :
    FullData (Option Y) (config.skeleton tag) :=
  MerkleTreeExtractor.tree view (config.skeleton tag) (config.addressKey tag)
    checkpoint.cumulativeLog checkpoint.root

/-- Canonical extracted opening for the selector carried by a claimed opening. -/
def Checkpoint.extractedOpening [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag)
    (opening : BatchOpening Y (config.skeleton tag)) :
    BatchOpening (Option Y) (config.skeleton tag) where
  selector := opening.selector
  values := selectedValues (Checkpoint.extractedTree view checkpoint).toLeafData opening.selector
  proof := generateBatchProof (Checkpoint.extractedTree view checkpoint)
    opening.selector opening.anySelected

/-- A checkpoint paired with the configuration that determines its dependent tree shape. -/
abbrev AnyCheckpoint (Cfg : Type u) (Query : Type v) (Address : Type w) (Y : Type)
    (config : Configuration Cfg Address) :=
  (tag : Cfg) ×' Checkpoint Query Y config tag

/-- Stateful accumulator for sequential commitment phases.

`cumulativeLog` contains all completed commitment-phase segments.  `checkpoints` retains an
immutable snapshot after every recorded root. -/
structure ExtractorState (Cfg : Type u) (Query : Type v) (Address : Type w) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- Transcript accumulated across all recorded commitment phases. -/
  cumulativeLog : MerkleTreeExtractor.QueryLog Query Y
  /-- Configuration-tagged checkpoint history, in commitment order. -/
  checkpoints : List (AnyCheckpoint Cfg Query Address Y config)

/-- Empty state before any commitment phase has run. -/
def ExtractorState.empty {config : Configuration Cfg Address} :
    ExtractorState Cfg Query Address Y config where
  cumulativeLog := []
  checkpoints := []

/-- Append one phase-local query log and record the resulting cumulative checkpoint. -/
def ExtractorState.record {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    ExtractorState Cfg Query Address Y config :=
  let cumulativeLog := state.cumulativeLog ++ phaseLog
  { cumulativeLog
    checkpoints := state.checkpoints ++ [⟨tag, { root, cumulativeLog }⟩] }

/-- Record a checkpoint from an already accumulated log. This is the proof-facing form used when
the caching/logging interpreter returns the full current log rather than a phase-local suffix. -/
def ExtractorState.recordCumulative {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    ExtractorState Cfg Query Address Y config where
  cumulativeLog := cumulativeLog
  checkpoints := state.checkpoints ++ [⟨tag, { root, cumulativeLog }⟩]

/-- `recordCumulative` agrees with the executable phase-suffix transition. -/
theorem ExtractorState.recordCumulative_append
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    state.recordCumulative tag (state.cumulativeLog ++ phaseLog) root =
      state.record tag phaseLog root := rfl

@[simp]
theorem ExtractorState.recordCumulative_cumulativeLog
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.recordCumulative tag cumulativeLog root).cumulativeLog = cumulativeLog := rfl

@[simp]
theorem ExtractorState.recordCumulative_checkpoints
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.recordCumulative tag cumulativeLog root).checkpoints =
      state.checkpoints ++ [⟨tag, { root, cumulativeLog }⟩] := rfl

@[simp]
theorem ExtractorState.empty_cumulativeLog :
    ∀ {config : Configuration Cfg Address},
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config).cumulativeLog = [] := rfl

@[simp]
theorem ExtractorState.empty_checkpoints :
    ∀ {config : Configuration Cfg Address},
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config).checkpoints = [] := rfl

@[simp]
theorem ExtractorState.record_cumulativeLog
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).cumulativeLog = state.cumulativeLog ++ phaseLog := rfl

@[simp]
theorem ExtractorState.record_checkpoints
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).checkpoints =
      state.checkpoints ++
        [⟨tag, { root, cumulativeLog := state.cumulativeLog ++ phaseLog }⟩] := rfl

/-- Recording one commitment adds exactly one checkpoint. -/
@[simp]
theorem ExtractorState.record_checkpoints_length
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).checkpoints.length = state.checkpoints.length + 1 := by
  simp

/-- Every recorded checkpoint transcript is a prefix of the state's current transcript. -/
def ExtractorState.WellFormed {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : Prop :=
  ∀ tag checkpoint, ⟨tag, checkpoint⟩ ∈ state.checkpoints →
    checkpoint.cumulativeLog <+: state.cumulativeLog

/-- The empty extractor state satisfies the checkpoint-prefix invariant. -/
theorem ExtractorState.wellFormed_empty {config : Configuration Cfg Address} :
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config).WellFormed := by
  intro tag checkpoint hmem
  simp at hmem

/-- Recording one commitment preserves the checkpoint-prefix invariant. -/
theorem ExtractorState.WellFormed.record {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config} (hstate : state.WellFormed)
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).WellFormed := by
  intro recordedTag checkpoint hmem
  rw [ExtractorState.record_checkpoints] at hmem
  rcases List.mem_append.mp hmem with hprevious | hnew
  · exact (hstate recordedTag checkpoint hprevious).trans
      (List.prefix_append state.cumulativeLog phaseLog)
  · simp only [List.mem_singleton] at hnew
    cases hnew
    exact List.prefix_rfl

/-- The checkpoint added by `record` occurs in the resulting history. -/
theorem ExtractorState.recorded_checkpoint_mem {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (⟨tag, { root, cumulativeLog := state.cumulativeLog ++ phaseLog }⟩ :
      AnyCheckpoint Cfg Query Address Y config) ∈
      (state.record tag phaseLog root).checkpoints := by
  simp

/-- Append a terminal phase log after all commitment checkpoints have been recorded. -/
def ExtractorState.terminalLog {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) :
    MerkleTreeExtractor.QueryLog Query Y :=
  state.cumulativeLog ++ phaseLog

/-- The commitment transcript is a prefix of the terminal transcript built from a suffix log. -/
theorem ExtractorState.prefix_terminalLog {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) :
    state.cumulativeLog <+: state.terminalLog phaseLog :=
  List.prefix_append _ _

/-! ## Opening attempts and deterministic failure events -/

/-- One verifier decision for a claimed opening against a recorded commitment checkpoint. -/
structure OpeningAttempt (Query : Type v) (Y : Type)
    (config : Configuration Cfg Address) (tag : Cfg) where
  /-- Checkpoint whose root the opening claims to open. -/
  checkpoint : Checkpoint Query Y config tag
  /-- Dependent nonempty pruned batch opening. -/
  opening : BatchOpening Y (config.skeleton tag)
  /-- Result returned by the verifier. -/
  accepted : Bool

/-- An opening attempt paired with its dependent configuration. -/
abbrev AnyOpeningAttempt (Cfg : Type u) (Query : Type v) (Address : Type w) (Y : Type)
    (config : Configuration Cfg Address) :=
  (tag : Cfg) ×' OpeningAttempt Query Y config tag

/-- An accepted opening disagrees with the canonical partial opening extracted at commitment time.

The comparison maps every adversarial value and proof hash through `some`; consequently `none` in
the extracted tree is observable and causes disagreement. -/
def AcceptedOpeningDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (attempt : OpeningAttempt Query Y config tag) : Prop :=
  attempt.accepted = true ∧
    attempt.checkpoint.extractedOpening view attempt.opening ≠ attempt.opening.map some

/-- Two checkpoints for the same configuration and root reconstruct different partial trees. -/
def EqualRootExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (left right : Checkpoint Query Y config tag) : Prop :=
  left.root = right.root ∧
    Checkpoint.extractedTree view left ≠ Checkpoint.extractedTree view right

@[simp]
theorem not_equalRootExtractionDisagreement_self [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) :
    ¬ EqualRootExtractionDisagreement view checkpoint checkpoint := by
  simp [EqualRootExtractionDisagreement]

/-- A commitment-time extraction changes when reconstructed from the terminal cumulative log.

This is distinct from equal-root inconsistency between two commitment checkpoints: a terminal
opening phase may extend the transcript even when it emits no new commitment. -/
def CheckpointTerminalExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag)
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  Checkpoint.extractedTree view checkpoint ≠
    MerkleTreeExtractor.tree view (config.skeleton tag) (config.addressKey tag)
      terminalLog checkpoint.root

@[simp]
theorem not_checkpointTerminalExtractionDisagreement_self
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) :
    ¬ CheckpointTerminalExtractionDisagreement view checkpoint checkpoint.cumulativeLog := by
  simp [CheckpointTerminalExtractionDisagreement, Checkpoint.extractedTree]

/-- Some accepted, recorded opening attempt disagrees with its checkpoint extraction.

The attempt and recorded checkpoint must carry the same configuration tag; cross-tag root reuse is
outside this event. -/
def HasAcceptedOpeningDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config)) : Prop :=
  ∃ tag attempt,
    ⟨tag, attempt⟩ ∈ attempts ∧
    ⟨tag, attempt.checkpoint⟩ ∈ state.checkpoints ∧
    AcceptedOpeningDisagreement view attempt

/-- Two recorded checkpoints for one configuration and root have inconsistent extractions.

Both checkpoints must carry the same configuration tag; cross-tag root reuse is outside this
event. -/
def HasEqualRootExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : Prop :=
  ∃ tag left right,
    ⟨tag, left⟩ ∈ state.checkpoints ∧
    ⟨tag, right⟩ ∈ state.checkpoints ∧
    EqualRootExtractionDisagreement view left right

/-- Some recorded checkpoint extraction changes under the terminal transcript. -/
def HasCheckpointTerminalExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  ∃ tag checkpoint,
    ⟨tag, checkpoint⟩ ∈ state.checkpoints ∧
    CheckpointTerminalExtractionDisagreement view checkpoint
      (state.terminalLog terminalSuffix)

/-- Deterministic bad event for stateful multi-commitment batch extraction.

Its opening and equal-root branches compare checkpoints only within one configuration tag;
cross-tag root reuse is outside the event. -/
def Failure [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  HasAcceptedOpeningDisagreement view state attempts ∨
    HasEqualRootExtractionDisagreement view state ∨
      HasCheckpointTerminalExtractionDisagreement view state terminalSuffix

/-- The textbook-facing failure event: an accepted chosen opening disagrees with its checkpoint
extraction, or two equal roots at checkpoints of the same configuration have inconsistent
extractions. Checkpoint-to-terminal evolution is an internal strengthening used in the proof, not
part of this public event. Both branches compare checkpoints only within one configuration tag;
cross-tag root reuse is outside the event. -/
def TextbookFailure [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config)) : Prop :=
  HasAcceptedOpeningDisagreement view state attempts ∨
    HasEqualRootExtractionDisagreement view state

/-- The stronger three-branch proof event subsumes the textbook-facing failure event. -/
theorem TextbookFailure.toFailure [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : TextbookFailure view state attempts) :
    Failure view state attempts terminalSuffix := by
  rcases h with hopening | hequalRoot
  · exact Or.inl hopening
  · exact Or.inr (Or.inl hequalRoot)

/-- If checkpoint extraction is stable under the terminal suffix, the strong and textbook events
coincide. This is a deterministic specialization, independent of any probability semantics. -/
theorem failure_iff_textbookFailure_of_noTerminalDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : ¬ HasCheckpointTerminalExtractionDisagreement
      view state terminalSuffix) :
    Failure view state attempts terminalSuffix ↔
      TextbookFailure view state attempts := by
  simp only [Failure, TextbookFailure]
  tauto

theorem Failure.ofAcceptedOpeningDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasAcceptedOpeningDisagreement view state attempts) :
    Failure view state attempts terminalSuffix :=
  Or.inl h

theorem Failure.ofEqualRootExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasEqualRootExtractionDisagreement view state) :
    Failure view state attempts terminalSuffix :=
  Or.inr (Or.inl h)

theorem Failure.ofCheckpointTerminalExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasCheckpointTerminalExtractionDisagreement view state terminalSuffix) :
    Failure view state attempts terminalSuffix :=
  Or.inr (Or.inr h)

/-- With no recorded commitments, none of the three deterministic failure branches can occur. -/
theorem not_failure_empty [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y) :
    ¬ Failure view (ExtractorState.empty : ExtractorState Cfg Query Address Y config)
      attempts terminalSuffix := by
  simp [Failure, HasAcceptedOpeningDisagreement, HasEqualRootExtractionDisagreement,
    HasCheckpointTerminalExtractionDisagreement]

/-! ## Ordered-query canary -/

private def canaryView :
    MerkleTreeExtractor.QueryView (Bool × (Nat × Nat)) Bool Nat where
  address := Prod.fst
  input := Prod.snd

private def canaryConfig : Configuration Unit Bool where
  skeleton _ := .internal .leaf .leaf
  addressKey _ _ := false

private def canaryCheckpoint : Checkpoint (Bool × (Nat × Nat)) Nat canaryConfig () where
  root := 7
  cumulativeLog := [⟨(true, (11, 13)), 7⟩, ⟨(false, (2, 3)), 7⟩]

/-- The checkpoint extractor uses the matching address and preserves ordered query children.

This concrete producer canary rejects swapping the left/right query inputs, ignoring the address,
or failing to follow a logged root response. -/
example : Checkpoint.extractedTree canaryView canaryCheckpoint =
    FullData.internal (some 7) (FullData.leaf (some 2)) (FullData.leaf (some 3)) := by
  rfl

end MerkleTreeMultiExtractability
