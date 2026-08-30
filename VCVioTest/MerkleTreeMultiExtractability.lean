/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.StrongBound

/-!
# Stateful Merkle Multi-Extractability Canaries

Small compile-time instantiations of the fully discharged game theorem. These examples pin the
scheduled zero/one/multiple-round API, finite-opening resource composition, and the proof-only
branch of full batch-opening disagreement without evaluating a probability distribution.
-/

@[expose] public section

open OracleComp OracleSpec

namespace VCVioTest.MerkleTreeMultiExtractabilityCanary

open BinaryTree InductiveMerkleTree _root_.MerkleTreeMultiExtractability

abbrev Query := Bool × Bool

noncomputable local instance : IsUniformSpec (Query →ₒ Bool) :=
  IsUniformSpec.ofFintypeInhabited (Query →ₒ Bool)

/-- Unaddressed Boolean hashes packaged through the query-parametric node interface. -/
def model : MerkleTreeExtractability.NodeQueryModel Query Unit Bool where
  view := {
    address := fun _ => ()
    input := id }
  mkQuery _ input := input
  address_mkQuery := by intros; rfl
  input_mkQuery := by intros; rfl

def skeleton : Skeleton :=
  .internal .leaf .leaf

def config : Configuration Unit Unit where
  skeleton _ := skeleton
  addressKey _ _ := ()

/-- Query-free commitments make the theorem canary about API composition rather than arithmetic. -/
abbrev committer : SequentialCommitter Unit Query Bool where
  State := Unit
  initialState := ()
  commit _ _ := pure ((), false, ())

/-- The terminal phase emits no claims; the finite-opening specialization therefore has zero
honest-verifier overhead. -/
abbrev adversary : Adversary Unit Query Unit Bool config where
  committer := committer
  opening _ _ := pure []

private theorem commit_query_bound (round : ℕ) (state : committer.State) :
    IsTotalQueryBound (committer.commit round state) round := by
  trivial

private theorem opening_query_bound (state : committer.State)
    (extractorState : ExtractorState Unit Query Unit Bool config) :
    IsTotalQueryBound (adversary.opening state extractorState) 0 := by
  trivial

private theorem opening_count_bound : adversary.HasOpeningCountBound 0 := by
  intro state extractorState claims hclaims
  simpa [adversary] using hclaims

private theorem per_claim_bound :
    ∀ tag, (config.skeleton tag).leafCount - 1 ≤ 1 := by
  intro tag
  cases tag
  decide

private theorem per_checkpoint_bound :
    ∀ tag, config.nodeBudget tag ≤ 3 := by
  intro tag
  cases tag
  decide

/-- One theorem instantiation covers every round count while exercising a genuinely
heterogeneous public schedule (`round` itself bounds phase `round`). -/
theorem scheduledStrongBound (rounds : ℕ) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator (rounds * 3) rounds (0 * 1)
        (commitmentQueryBudget (fun round => round) rounds 0 + 0) : ENNReal) *
          (Nat.card Bool : ENNReal)⁻¹ := by
  exact strongFailure_rom_bound_schedule_of_openingCountBounds model config rounds adversary
    (false, false) (fun round => round) 0 (rounds * 3) rounds 0 1 3
    commit_query_bound opening_query_bound opening_count_bound per_claim_bound
    per_checkpoint_bound le_rfl le_rfl

/-! The three specializations make accidental zero/successor/index-shift API regressions visible. -/

example :
    Pr[ StrongFailure model | extractabilityGame model config 0 adversary] ≤
      (multiExtractabilitySafeNumerator (0 * 3) 0 (0 * 1)
        (commitmentQueryBudget (fun round => round) 0 0 + 0) : ENNReal) *
          (Nat.card Bool : ENNReal)⁻¹ :=
  scheduledStrongBound 0

example :
    Pr[ StrongFailure model | extractabilityGame model config 1 adversary] ≤
      (multiExtractabilitySafeNumerator (1 * 3) 1 (0 * 1)
        (commitmentQueryBudget (fun round => round) 1 0 + 0) : ENNReal) *
          (Nat.card Bool : ENNReal)⁻¹ :=
  scheduledStrongBound 1

example :
    Pr[ StrongFailure model | extractabilityGame model config 3 adversary] ≤
      (multiExtractabilitySafeNumerator (3 * 3) 3 (0 * 1)
        (commitmentQueryBudget (fun round => round) 3 0 + 0) : ENNReal) *
          (Nat.card Bool : ENNReal)⁻¹ :=
  scheduledStrongBound 3

/-! ## Proof-only full-opening disagreement -/

def selectRight : LeafData Bool skeleton :=
  .internal (.leaf false) (.leaf true)

def proofOnlyValues : SelectedValues Bool selectRight :=
  (PUnit.unit, true)

/-- The stored left sibling is deliberately wrong; the selected right value is correct. -/
def proofOnlyOpening : BatchOpening Bool skeleton where
  selector := selectRight
  values := proofOnlyValues
  proof := .pruneLeft rfl true .leaf

def extractedTree : FullData (Option Bool) skeleton :=
  .internal (some false) (.leaf (some false)) (.leaf (some true))

private theorem proof_only_disagreement :
    MerkleTreeBatchExtractability.OpeningDisagreesWithTree proofOnlyOpening extractedTree := by
  apply Or.inr
  simp only [MerkleTreeBatchExtractability.extractedOpening, proofOnlyOpening, extractedTree,
    selectRight, proofOnlyValues, FullData.toLeafData, generateBatchProof,
    FullData.getRootValue, BatchProof.map]
  intro heq
  injection heq with _ _ _ _ hroot _
  change some true = some false at hroot
  simp at hroot

/-- The full-opening witness theorem accepts a proof-frontier-only mismatch, not merely unequal
selected leaf values. -/
example :
    ∃ index : SkeletonLeafIndex skeleton,
      ∃ selected : proofOnlyOpening.selector.get index = true,
        some (selectedValueAt proofOnlyOpening.values index selected) ≠
            extractedTree.get index.toNodeIndex ∨
          (batchToSingleProofAddressed (fun _ _ _ => false) proofOnlyOpening.values
            proofOnlyOpening.proof index selected).toList.map some ≠
            (generateProof extractedTree index).toList :=
  proof_only_disagreement.exists_selectedValue_or_path_disagreement
    (fun _ _ _ => false) proofOnlyOpening extractedTree

end VCVioTest.MerkleTreeMultiExtractabilityCanary
