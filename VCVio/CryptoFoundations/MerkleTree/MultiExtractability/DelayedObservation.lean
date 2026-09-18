/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Game

/-!
# Delayed observation of Merkle commitment checkpoints

Comparing frozen checkpoint extraction with extraction from the terminal adversarial log
requires an explicit drift event. Without drift, the original public failure event agrees
with the delayed opening event; in general its probability is bounded by their union.
The transcript layer lives in `Type 0`, as does the executable multi-extractability game.
-/

public section

open OracleComp OracleSpec MeasureTheory
open BinaryTree InductiveMerkleTree

namespace MerkleTreeMultiExtractability.DelayedObservation

section General

variable {Cfg Query Address Y : Type} {config : Configuration Cfg Address}

/-- A deliberately delayed observation. It retains the original root but lets the
extractor see the terminal adversarial log, including queries after commitment. -/
@[expose]
def atTerminal (tr : Transcript Cfg Query Address Y config) {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) : Checkpoint Query Y config tag :=
  { root := checkpoint.root
    cumulativeLog := tr.extractorState.terminalLog tr.terminalSuffix }

/-- Check membership using the original checkpoint. Only the extraction input is
changed: neither adversary behavior nor verification nor admissibility is changed. -/
@[expose]
def LateOpeningFailure [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (tr : Transcript Cfg Query Address Y config) : Prop :=
  ∃ tag attempt, ⟨tag, attempt⟩ ∈ tr.attempts ∧
    ⟨tag, attempt.checkpoint⟩ ∈ tr.extractorState.checkpoints ∧
    AcceptedOpeningDisagreement view
      { attempt with checkpoint := atTerminal tr attempt.checkpoint }

/-- Some recorded checkpoint extracts a different tree from the terminal log. -/
abbrev Drift [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (tr : Transcript Cfg Query Address Y config) : Prop :=
  HasCheckpointTerminalExtractionDisagreement view tr.extractorState tr.terminalSuffix

/-- Reconstructing both equal-root checkpoints from one final log erases this
branch of the original public failure event, even if the frozen trees differed. -/
theorem terminal_equalRoot_consistent [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (tr : Transcript Cfg Query Address Y config) {tag : Cfg}
    (left right : Checkpoint Query Y config tag) (hroot : left.root = right.root) :
    ¬ EqualRootExtractionDisagreement view (atTerminal tr left) (atTerminal tr right) := by
  simp [EqualRootExtractionDisagreement, atTerminal, Checkpoint.extractedTree, hroot]

/-- Equal reconstructed trees supply equal batch openings. -/
theorem extractedOpening_congr [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {tag : Cfg} (left right : Checkpoint Query Y config tag)
    (h : left.extractedTree view = right.extractedTree view)
    (opening : BatchOpening Y (config.skeleton tag)) :
    left.extractedOpening view opening = right.extractedOpening view opening := by
  simp only [Checkpoint.extractedOpening, h]

/-- Every recorded checkpoint agrees with its terminal reconstruction in the absence of drift. -/
theorem recorded_tree_stable [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (tr : Transcript Cfg Query Address Y config) (hstable : ¬ Drift view tr)
    {tag : Cfg} (checkpoint : Checkpoint Query Y config tag)
    (hmem : ⟨tag, checkpoint⟩ ∈ tr.extractorState.checkpoints) :
    checkpoint.extractedTree view = (atTerminal tr checkpoint).extractedTree view := by
  by_contra hne
  exact hstable ⟨tag, checkpoint, hmem, hne⟩

/-- Stable checkpoint trees preserve the accepted-opening disagreement event. -/
theorem openingFailure_iff_late_of_noDrift [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (tr : Transcript Cfg Query Address Y config) (hstable : ¬ Drift view tr) :
    HasAcceptedOpeningDisagreement view tr.extractorState tr.attempts ↔
      LateOpeningFailure view tr := by
  unfold HasAcceptedOpeningDisagreement LateOpeningFailure
  constructor
  · rintro ⟨tag, attempt, hattempt, hmem, haccept, hne⟩
    refine ⟨tag, attempt, hattempt, hmem, haccept, ?_⟩
    rwa [← extractedOpening_congr view _ _
      (recorded_tree_stable view tr hstable attempt.checkpoint hmem)]
  · rintro ⟨tag, attempt, hattempt, hmem, haccept, hne⟩
    refine ⟨tag, attempt, hattempt, hmem, haccept, ?_⟩
    rwa [extractedOpening_congr view _ _
      (recorded_tree_stable view tr hstable attempt.checkpoint hmem)]

/-- Stable equal-root checkpoints reconstruct the same tree from the common terminal log. -/
theorem no_equalRootFailure_of_noDrift [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (tr : Transcript Cfg Query Address Y config) (hstable : ¬ Drift view tr) :
    ¬ HasEqualRootExtractionDisagreement view tr.extractorState := by
  rintro ⟨tag, left, right, hl, hr, hroot, hne⟩
  apply hne
  rw [recorded_tree_stable view tr hstable left hl,
    recorded_tree_stable view tr hstable right hr]
  simp only [atTerminal, Checkpoint.extractedTree, hroot]

/-- If no checkpoint tree changes, terminal extraction recovers the original
public event. Terminal equal-root comparison is automatically consistent. -/
theorem publicFailure_iff_late_of_noDrift [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (tr : Transcript Cfg Query Address Y config) (hstable : ¬ Drift view tr) :
    OpeningOrEqualRootDisagreement view tr.extractorState tr.attempts ↔
      LateOpeningFailure view tr := by
  rw [OpeningOrEqualRootDisagreement,
    or_iff_left (no_equalRootFailure_of_noDrift view tr hstable)]
  exact openingFailure_iff_late_of_noDrift view tr hstable

/-- A delayed observer is sound only with an explicit charge for extraction drift. -/
theorem publicFailure_subset_late_union_drift [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y) :
    {tr : Transcript Cfg Query Address Y config |
      OpeningOrEqualRootDisagreement view tr.extractorState tr.attempts} ⊆
    {tr | LateOpeningFailure view tr} ∪ {tr | Drift view tr} := by
  intro tr h
  by_cases hd : Drift view tr
  · exact Or.inr hd
  · exact Or.inl ((publicFailure_iff_late_of_noDrift view tr hd).mp h)

/-- The terminal-observer probability bound retains an explicit extraction-drift charge. -/
theorem delayedObserver_bound [DecidableEq Address] [DecidableEq Y]
    [MeasurableSpace (Transcript Cfg Query Address Y config)]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (μ : Measure (Transcript Cfg Query Address Y config)) :
    μ {tr | OpeningOrEqualRootDisagreement view tr.extractorState tr.attempts} ≤
      μ {tr | LateOpeningFailure view tr} + μ {tr | Drift view tr} :=
  (measure_mono (publicFailure_subset_late_union_drift view)).trans (measure_union_le _ _)

end General

end MerkleTreeMultiExtractability.DelayedObservation
