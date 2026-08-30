/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Uniqueness

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
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open BinaryTree InductiveMerkleTree

universe u v w

variable {Cfg : Type u} {Query : Type v} {Address : Type w} {Y Z : Type}
variable {s : Skeleton}

/-! ## Dependent batch openings -/

/-- A nonempty, intrinsically path-pruned batch opening for a fixed skeleton.

The selector determines both dependent payload fields.  No explicit nonemptiness proof is stored:
`BatchProof` has no constructor at a selector whose `anySelected` value is `false`. -/
structure BatchOpening (Y : Type) (s : Skeleton) where
  /-- Dense selector for the leaves opened by this claim. -/
  selector : LeafData Bool s
  /-- Claimed values at exactly the selected leaves. -/
  values : SelectedValues Y selector
  /-- Canonical-shape pruned authentication data. -/
  proof : BatchProof Y selector

/-- Every packaged batch opening selects at least one leaf. -/
theorem BatchOpening.anySelected (opening : BatchOpening Y s) :
    opening.selector.anySelected = true :=
  opening.proof.anySelected_of_batchProof

/-- Map a selected-value payload without changing its selector. -/
def mapSelectedValues (f : Y → Z) : {s : Skeleton} → (sel : LeafData Bool s) →
    SelectedValues Y sel → SelectedValues Z sel
  | _, .leaf true, value => f value
  | _, .leaf false, _ => ⟨⟩
  | _, .internal left right, values =>
      (mapSelectedValues f left values.1, mapSelectedValues f right values.2)

/-- Map every stored hash in an intrinsic pruned batch proof. -/
def mapBatchProof (f : Y → Z) : {s : Skeleton} → {sel : LeafData Bool s} →
    BatchProof Y sel → BatchProof Z sel
  | _, _, .leaf => .leaf
  | _, _, .internalBoth left right =>
      .internalBoth (mapBatchProof f left) (mapBatchProof f right)
  | _, _, .pruneRight h rightRoot left =>
      .pruneRight h (f rightRoot) (mapBatchProof f left)
  | _, _, .pruneLeft h leftRoot right =>
      .pruneLeft h (f leftRoot) (mapBatchProof f right)

/-- Map both observable payloads of a batch opening, preserving its selector. -/
def BatchOpening.map (f : Y → Z) (opening : BatchOpening Y s) : BatchOpening Z s where
  selector := opening.selector
  values := mapSelectedValues f opening.selector opening.values
  proof := mapBatchProof f opening.proof

@[simp]
theorem BatchOpening.map_selector (f : Y → Z) (opening : BatchOpening Y s) :
    (opening.map f).selector = opening.selector := rfl

@[simp]
theorem mapSelectedValues_id {sel : LeafData Bool s} (values : SelectedValues Y sel) :
    mapSelectedValues id sel values = values := by
  induction sel with
  | leaf selected =>
      cases selected
      · change (⟨⟩ : PUnit) = values
        cases values
        rfl
      · rfl
  | internal left right ihLeft ihRight =>
      exact Prod.ext (ihLeft values.1) (ihRight values.2)

@[simp]
theorem mapBatchProof_id {sel : LeafData Bool s} (proof : BatchProof Y sel) :
    mapBatchProof id proof = proof := by
  induction proof with
  | leaf => rfl
  | internalBoth left right ihLeft ihRight => simp only [mapBatchProof, ihLeft, ihRight]
  | pruneRight h rightRoot left ih => simp only [mapBatchProof, ih, id_eq]
  | pruneLeft h leftRoot right ih => simp only [mapBatchProof, ih, id_eq]

@[simp]
theorem BatchOpening.map_id (opening : BatchOpening Y s) :
    opening.map id = opening := by
  cases opening
  simp only [BatchOpening.map, mapSelectedValues_id, mapBatchProof_id]

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

/-- Immutable extraction input captured immediately after one commitment phase. -/
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

/-- Some accepted, recorded opening attempt disagrees with its checkpoint extraction. -/
def HasAcceptedOpeningDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config)) : Prop :=
  ∃ tag attempt,
    ⟨tag, attempt⟩ ∈ attempts ∧
    ⟨tag, attempt.checkpoint⟩ ∈ state.checkpoints ∧
    AcceptedOpeningDisagreement view attempt

/-- Two recorded checkpoints for one configuration and root have inconsistent extractions. -/
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
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  ∃ tag checkpoint,
    ⟨tag, checkpoint⟩ ∈ state.checkpoints ∧
    CheckpointTerminalExtractionDisagreement view checkpoint terminalLog

/-- Deterministic bad event for stateful multi-commitment batch extraction. -/
def Failure [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  HasAcceptedOpeningDisagreement view state attempts ∨
    HasEqualRootExtractionDisagreement view state ∨
      HasCheckpointTerminalExtractionDisagreement view state terminalLog

theorem Failure.ofAcceptedOpeningDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasAcceptedOpeningDisagreement view state attempts) :
    Failure view state attempts terminalLog :=
  Or.inl h

theorem Failure.ofEqualRootExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasEqualRootExtractionDisagreement view state) :
    Failure view state attempts terminalLog :=
  Or.inr (Or.inl h)

theorem Failure.ofCheckpointTerminalExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasCheckpointTerminalExtractionDisagreement view state terminalLog) :
    Failure view state attempts terminalLog :=
  Or.inr (Or.inr h)

/-- With no recorded commitments, none of the three deterministic failure branches can occur. -/
theorem not_failure_empty [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (attempts : List (AnyOpeningAttempt Cfg Query Address Y config))
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y) :
    ¬ Failure view (ExtractorState.empty : ExtractorState Cfg Query Address Y config)
      attempts terminalLog := by
  simp [Failure, HasAcceptedOpeningDisagreement, HasEqualRootExtractionDisagreement,
    HasCheckpointTerminalExtractionDisagreement]

end MerkleTreeMultiExtractability
