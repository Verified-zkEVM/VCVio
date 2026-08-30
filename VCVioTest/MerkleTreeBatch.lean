/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Completeness
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Addressed
public meta import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.MapToSingle
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Uniqueness

/-!
# Inductive Merkle Batch-Opening Canaries

Concrete examples that pin the public behavior of path-pruned batch openings: hash argument
order, pruning shape, the singleton reduction to an ordinary authentication path, the
all-selected and empty-selector boundaries, and cross-selector collision extraction.
-/

@[expose] public section

namespace VCVioTest.MerkleTreeBatch

open BinaryTree InductiveMerkleTree

def fourLeafSkeleton : Skeleton :=
  .internal (.internal .leaf .leaf) (.internal .leaf .leaf)

def leaves : LeafData Nat fourLeafSkeleton :=
  .internal (.internal (.leaf 1) (.leaf 2)) (.internal (.leaf 3) (.leaf 4))

/-- Deliberately noncommutative so the examples detect swapped left/right hash inputs. -/
def orderedHash (left right : Nat) : Nat :=
  2 * left + 3 * right + 1

def cache : FullData Nat fourLeafSkeleton :=
  buildMerkleTreeWithHash leaves orderedHash

def selectFirst : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf true) (.leaf false)) (.internal (.leaf false) (.leaf false))

def selectOuter : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf true) (.leaf false)) (.internal (.leaf false) (.leaf true))

def selectAll : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf true) (.leaf true)) (.internal (.leaf true) (.leaf true))

def selectNone : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf false) (.leaf false)) (.internal (.leaf false) (.leaf false))

def firstIndex : SkeletonLeafIndex fourLeafSkeleton :=
  .ofLeft (.ofLeft .ofLeaf)

theorem firstSelected : selectFirst.get firstIndex = true := by decide

theorem firstNonempty : selectFirst.anySelected = true := by decide

def firstProof : BatchProof Nat selectFirst :=
  generateBatchProof cache selectFirst firstNonempty

theorem outerNonempty : selectOuter.anySelected = true := by decide

def outerProof : BatchProof Nat selectOuter :=
  generateBatchProof cache selectOuter outerNonempty

theorem allNonempty : selectAll.anySelected = true := by decide

def allProof : BatchProof Nat selectAll :=
  generateBatchProof cache selectAll allNonempty

example : orderedHash 9 19 = 76 := rfl

example : orderedHash 9 19 ≠ orderedHash 19 9 := by decide

example : cache.getRootValue = 76 := rfl

/-- A singleton batch proof is exactly the ordinary authentication path at that index. -/
example :
    batchToSingleProof orderedHash (selectedValues leaves selectFirst) firstProof
      firstIndex firstSelected = generateProof cache firstIndex := by
  rfl

example : selectedValueAt (selectedValues leaves selectFirst) firstIndex firstSelected = 1 := rfl

/-- Both pruning directions occur, with the roots of precisely the unselected siblings. -/
example :
    outerProof =
      .internalBoth (.pruneRight (by decide) 2 .leaf) (.pruneLeft (by decide) 3 .leaf) := by
  rfl

example :
    getPutativeBatchRootWithHash orderedHash (selectedValues leaves selectOuter) outerProof =
      cache.getRootValue := by
  exact functional_batch_completeness leaves selectOuter outerNonempty orderedHash

example :
    getPutativeBatchRootWithHash orderedHash (selectedValues leaves selectOuter) outerProof = 76 :=
  rfl

/-- Opening every leaf carries no stored authentication hash. -/
example :
    allProof =
      .internalBoth (.internalBoth .leaf .leaf) (.internalBoth .leaf .leaf) := by
  rfl

/-- Mapping into a partial-tree value type preserves both pruning directions and maps only
the stored authentication frontier. -/
example :
    outerProof.map some =
      .internalBoth (.pruneRight (by decide) (some 2) .leaf)
        (.pruneLeft (by decide) (some 3) .leaf) := by
  rfl

/-- The all-selected proof contains no stored value for mapping to change. -/
example :
    allProof.map some =
      .internalBoth (.internalBoth .leaf .leaf) (.internalBoth .leaf .leaf) := by
  rfl

/-- Structural query counting is exact on singleton, outer-pair, and all-selected traversals. -/
example : firstProof.queryCount = 2 ∧ outerProof.queryCount = 3 ∧ allProof.queryCount = 3 := by
  decide

/-! ## Addressed traversal order -/

/-- Observable tags for the three typed internal positions of `fourLeafSkeleton`. -/
inductive DepthTwoAddress where
  | rootNode
  | leftNode
  | rightNode
deriving DecidableEq, Repr

/-- Collapse the dependent internal-node index to a traceable address tag. -/
def depthTwoAddress : SkeletonInternalIndex fourLeafSkeleton → DepthTwoAddress
  | .ofInternal => .rootNode
  | .ofLeft .ofInternal => .leftNode
  | .ofRight .ofInternal => .rightNode

/-- One effectful addressed-hash call, retaining its ordered children. -/
structure AddressedHashEvent where
  address : DepthTwoAddress
  left : Nat
  right : Nat
deriving DecidableEq, Repr

abbrev AddressedTraceM := StateM (List AddressedHashEvent)

def addressWeight : DepthTwoAddress → Nat
  | .rootNode => 0
  | .leftNode => 100
  | .rightNode => 200

/-- Address-sensitive, noncommutative node hash with an observable append-only trace. -/
def tracedAddressedHash (address : SkeletonInternalIndex fourLeafSkeleton)
    (left right : Nat) : AddressedTraceM Nat := fun trace =>
  let tag := depthTwoAddress address
  (addressWeight tag + 2 * left + 3 * right + 1,
    trace ++ [{ address := tag, left, right }])

/-- The addressed batch fold visits left child, right child, then root; each recursive call
receives the correct reindexed typed address and preserves ordered hash inputs.  The numeric result
is also noncommutative, so neither swapping children nor merely repairing the trace can satisfy the
canary. -/
example : Id.run
    ((AddressedMerkleTree.getPutativeBatchRootAddressedM tracedAddressedHash
      (selectedValues leaves selectAll) allProof).run []) =
    (876,
      [{ address := .leftNode, left := 1, right := 2 },
       { address := .rightNode, left := 3, right := 4 },
       { address := .rootNode, left := 109, right := 219 }]) := by
  decide

/-- Opening no leaf is excluded by the dependent proof family. -/
example : IsEmpty (BatchProof Nat selectNone) :=
  ⟨fun proof => by
    have h := BatchProof.anySelected_of_batchProof proof
    simp [selectNone] at h⟩

example :
    getPutativeRootWithHash firstIndex
        (selectedValueAt (selectedValues leaves selectFirst) firstIndex firstSelected)
        (batchToSingleProof orderedHash (selectedValues leaves selectFirst) firstProof
          firstIndex firstSelected)
        orderedHash =
      getPutativeBatchRootWithHash orderedHash (selectedValues leaves selectFirst) firstProof := by
  exact getPutativeRootWithHash_batchToSingleProof orderedHash
    (selectedValues leaves selectFirst) firstProof firstIndex firstSelected

/-! ## Cross-selector collision extraction -/

def pairSkeleton : Skeleton :=
  .internal .leaf .leaf

def selectLeft : LeafData Bool pairSkeleton :=
  .internal (.leaf true) (.leaf false)

def selectBoth : LeafData Bool pairSkeleton :=
  .internal (.leaf true) (.leaf true)

def leftValues : SelectedValues Nat selectLeft := by
  change Nat × PUnit
  exact (1, ⟨⟩)

def bothValues : SelectedValues Nat selectBoth := by
  change Nat × Nat
  exact (2, 7)

def leftProof : BatchProof Nat selectLeft :=
  .pruneRight rfl 99 .leaf

def bothProof : BatchProof Nat selectBoth :=
  .internalBoth .leaf .leaf

def pairLeftIndex : SkeletonLeafIndex pairSkeleton :=
  .ofLeft .ofLeaf

theorem leftSelected : selectLeft.get pairLeftIndex = true := rfl

theorem bothLeftSelected : selectBoth.get pairLeftIndex = true := rfl

def constantHash (_left _right : Nat) : Nat :=
  0

theorem selectedValuesDiffer :
    selectedValueAt leftValues pairLeftIndex leftSelected ≠
      selectedValueAt bothValues pairLeftIndex bothLeftSelected := by
  native_decide

theorem putativeRootsAgree :
    getPutativeBatchRootWithHash constantHash leftValues leftProof =
      getPutativeBatchRootWithHash constantHash bothValues bothProof :=
  rfl

example :
    ∃ l₁ r₁ l₂ r₂,
      findCollision constantHash pairLeftIndex
          (batchToSingleProof constantHash leftValues leftProof pairLeftIndex leftSelected)
          (batchToSingleProof constantHash bothValues bothProof pairLeftIndex bothLeftSelected)
          (selectedValueAt leftValues pairLeftIndex leftSelected)
          (selectedValueAt bothValues pairLeftIndex bothLeftSelected) = some (l₁, r₁, l₂, r₂)
        ∧ Collision constantHash l₁ r₁ l₂ r₂ := by
  exact getPutativeBatchRootWithHash_binding constantHash
    leftValues leftProof bothValues bothProof pairLeftIndex leftSelected bothLeftSelected
    selectedValuesDiffer putativeRootsAgree

end VCVioTest.MerkleTreeBatch
