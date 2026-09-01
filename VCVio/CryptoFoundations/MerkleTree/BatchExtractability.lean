/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractability
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Opening
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.QueryBound
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.ToSingle
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Uniqueness

/-!
# Query-parametric batch openings for Merkle extractability

This module defines the batch-opening surface used by Merkle multi-extractability.  The
authentication data is the intrinsic path-pruned `InductiveMerkleTree.BatchProof`; no tuple of
single authentication paths is introduced.  Verification uses the same
`MerkleTreeExtractability.NodeQueryModel` as the single-opening game, so ordinary and addressed
Merkle trees are specializations of one computation.

The probability theorem is deliberately downstream of this module.  Here the dependent opening
package, query-parametric verifier, and two-phase adversary are executable definitions.  Keeping
this layer deterministic makes the later event decomposition state its security boundary
explicitly.
-/

@[expose] public section

namespace MerkleTreeBatchExtractability

open OracleSpec OracleComp BinaryTree InductiveMerkleTree

universe u

variable {Query Y : Type} {Address : Type u}

/-- Local compatibility name for the neutral packaged batch-opening abstraction. -/
abbrev Opening := InductiveMerkleTree.BatchOpening

/-- Recompute the putative root of a path-pruned batch opening through the complete queries
specified by `model`.  Internal positions are mapped to their actual oracle addresses by
`addressKey`. -/
def getPutativeBatchRoot (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) :
    {s : Skeleton} → (addressKey : SkeletonInternalIndex s → Address) →
      {selector : LeafData Bool s} → SelectedValues Y selector → BatchProof Y selector →
        OracleComp (Query →ₒ Y) Y
  | _, _, _, values, .leaf => pure values
  | _, addressKey, _, values, .internalBoth leftProof rightProof => do
      let leftRoot ← getPutativeBatchRoot model
        (fun position => addressKey (.ofLeft position)) values.1 leftProof
      let rightRoot ← getPutativeBatchRoot model
        (fun position => addressKey (.ofRight position)) values.2 rightProof
      liftM ((Query →ₒ Y).query
        (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)))
  | _, addressKey, _, values, .pruneRight _ rightRoot leftProof => do
      let leftRoot ← getPutativeBatchRoot model
        (fun position => addressKey (.ofLeft position)) values.1 leftProof
      liftM ((Query →ₒ Y).query
        (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)))
  | _, addressKey, _, values, .pruneLeft _ leftRoot rightProof => do
      let rightRoot ← getPutativeBatchRoot model
        (fun position => addressKey (.ofRight position)) values.2 rightProof
      liftM ((Query →ₒ Y).query
        (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)))

/-- Verify one packaged path-pruned batch opening against a claimed root. -/
def verifyOpening [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (root : Y) (opening : Opening Y s) :
    OracleComp (Query →ₒ Y) Bool := do
  let putativeRoot ← getPutativeBatchRoot model addressKey opening.values opening.proof
  return putativeRoot == root

/-- A two-phase adversary that commits to a root and later returns a dynamically selected,
path-pruned batch opening. -/
structure Adversary (Query Y : Type) (s : Skeleton) where
  /-- State transferred from the commitment phase to the opening phase. -/
  AuxState : Type
  /-- Produce a claimed Merkle root and continuation state. -/
  commit : OracleComp (Query →ₒ Y) (Y × AuxState)
  /-- Choose the selector, claimed values, and pruned proof after the commitment checkpoint. -/
  opening : AuxState → OracleComp (Query →ₒ Y) (Opening Y s)

/-- The adversary's two phases, excluding honest verification, have total query bound `qb`. -/
def Adversary.IsTwoPhaseTotalQueryBound {s : Skeleton}
    (adversary : Adversary Query Y s) (qb : ℕ) : Prop :=
  IsTotalQueryBound
    (do
      let (_root, aux) ← adversary.commit
      let _opening ← adversary.opening aux
      pure ())
    qb

/-- The batch-opening syntax and its commitment-phase query log.  This is the deterministic
program underlying the shared-cache ROM game; extraction and the winning event are layered on
top so that neither can be hidden in the adversary interface. -/
def openingInner {s : Skeleton} (adversary : Adversary Query Y s) :
    OracleComp (Query →ₒ Y)
      (Y × adversary.AuxState × (Query →ₒ Y).QueryLog × Opening Y s) := do
  let ((root, aux), queryLog) ← adversary.commit.withQueryLog
  let opening ← adversary.opening aux
  return (root, aux, queryLog, opening)

/-! ## Single-commitment batch extraction game -/

/-- The canonical batch opening read from a partial extracted tree, using exactly the selector
chosen by the adversary. Missing nodes remain explicit as `none`; this definition does not fill
or otherwise complete the extractor's output. -/
def extractedOpening {s : Skeleton} (tree : FullData (Option Y) s)
    (opening : Opening Y s) : Opening (Option Y) s where
  selector := opening.selector
  values := selectedValues tree.toLeafData opening.selector
  proof := generateBatchProof tree opening.selector opening.anySelected

/-- The adversary's concrete opening is not the `Option.some` image of the canonical opening
read from the commitment-checkpoint extraction. This is deliberately full-opening disagreement:
both selected leaf values and the entire pruned authentication frontier are covered. -/
def OpeningDisagreesWithTree {s : Skeleton} (opening : Opening Y s)
    (tree : FullData (Option Y) s) : Prop :=
  opening.values.map some ≠ (extractedOpening tree opening).values ∨
    opening.proof.map some ≠ (extractedOpening tree opening).proof

/-- Oracle syntax for the batch extractability experiment. The extractor sees only the query
log at the commitment checkpoint. The opening phase and honest batch verification execute after
that snapshot and therefore cannot retroactively populate the extracted tree. -/
def extractabilityInner [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (adversary : Adversary Query Y s) :
    OracleComp (Query →ₒ Y)
      (Y × adversary.AuxState × Opening Y s × FullData (Option Y) s × Bool) := do
  let ((root, aux), queryLog) ← adversary.commit.withQueryLog
  let tree := MerkleTreeExtractor.tree model.view s addressKey queryLog root
  let opening ← adversary.opening aux
  let verified ← verifyOpening model addressKey root opening
  return (root, aux, opening, tree, verified)

/-- The exact public failure event for one commitment and one dynamically selected batch
opening: the opening is accepted but differs from checkpoint extraction. Internal proof events
used to establish a ROM bound are intentionally not conflated with this public definition. -/
def AdversaryWinsExtractability {s : Skeleton} {AuxState : Type} :
    Y × AuxState × Opening Y s × FullData (Option Y) s × Bool → Prop
  | (_, _, opening, tree, verified) =>
      verified = true ∧ OpeningDisagreesWithTree opening tree

/-- Shared-cache random-oracle batch extractability game. Commitment, opening, and honest
verification use one lazy random function, while extraction remains pinned to the commitment
checkpoint log. -/
def extractabilityGame [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (adversary : Adversary Query Y s) :
    OracleComp (Query →ₒ Y)
      (Y × adversary.AuxState × Opening Y s × FullData (Option Y) s × Bool) :=
  (Query →ₒ Y).withCacheOverlay ∅
    (extractabilityInner model addressKey adversary)

end MerkleTreeBatchExtractability
