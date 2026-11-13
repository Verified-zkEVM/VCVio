/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import VCVio.CryptoFoundations.VectorCommitment.Monadic
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Completeness

/-!
# Inductive Merkle trees as monad-generic vector commitments

This file realizes the inductive Merkle tree of
`VCVio.CryptoFoundations.MerkleTree.Inductive.Defs` against the abstract positional commitment
interfaces of `VCVio.CryptoFoundations.VectorCommitment.Monadic`:

- `InductiveMerkleTree.monadicVectorCommitment` — the Merkle `MonadicVectorCommitment`
  (single-position opening);
- `InductiveMerkleTree.naiveBatchOpenMerkleTree` — a `MonadicBatchVectorCommitment` obtained from
  the above via `MonadicVectorCommitment.toBatchOpening`. It is *naive* in that a batch opening is
  just the list of individual leaf authentication paths, with no sharing of common interior
  hashes; the path-pruned `InductiveMerkleTree.BatchProof` is more succinct.

The construction is in the standard-model / collision-resistant-hash formulation: hashing is a pure
two-to-one function `hashFn`, so all commitment operations are pure and the instances live in any
monad. Positions are laid out on a caller-supplied skeleton `s` via a position-to-leaf equivalence
`e : ι ≃ SkeletonLeafIndex s`; an opening is the authentication path (the sibling hashes along the
leaf's branch), carried as a plain `List` of hashes.
-/

public section

open OracleComp OracleSpec BinaryTree

namespace InductiveMerkleTree

variable {α : Type}

/-- The inductive Merkle tree as a `MonadicVectorCommitment`.

Positions `ι` are mapped to the leaves of skeleton `s` by the equivalence `e`, and `hashFn` is the
two-to-one compression function. Committing builds the full tree and exposes its root; an opening
for a position is its authentication path (`generateProof`), carried as a `List`; verification
recomputes the putative root from the leaf value and path (`getPutativeRootWithHash`) and compares
it to the commitment. The operations are pure, so the instance is available in any monad `m`. -/
@[expose]
def monadicVectorCommitment {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    MonadicVectorCommitment m ι α α (FullData α s) (List α) where
  commit data :=
    let tree := buildMerkleTreeWithHash (LeafData.ofFn s fun i => data (e.symm i)) hashFn
    pure (tree.getRootValue, tree)
  openAt tree i := pure (generateProof tree (e i)).toList
  verifyOpen root i v op :=
    if h : op.length = (e i).depth then
      decide (getPutativeRootWithHash (e i) v ⟨op, h⟩ hashFn = root)
    else false

/-- The inductive Merkle tree as a `MonadicBatchVectorCommitment`, obtained from
`InductiveMerkleTree.monadicVectorCommitment` via `MonadicVectorCommitment.toBatchOpening`.

A batch opening for a list of positions is simply the list of their individual authentication paths
(each as `(position, path)`); verification checks each claimed position/value against its path
independently. This shares no interior hashes between paths, hence *naive* — a dedicated multi-leaf
Merkle proof could compress the common prefixes — but it is correct and requires nothing beyond the
single-position instance. -/
@[expose]
def naiveBatchOpenMerkleTree {ι : Type} {m : Type → Type} [Monad m]
    [DecidableEq ι] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    MonadicBatchVectorCommitment m ι α α (FullData α s) (List (ι × List α)) :=
  (monadicVectorCommitment s e hashFn).toBatchOpening

/-! ### Correctness -/

/-- Rebuilding a tree from leaf data `ld` and reading its leaves back recovers `ld`. -/
theorem toLeafData_buildMerkleTreeWithHash {s : Skeleton}
    (ld : LeafData α s) (hashFn : α → α → α) :
    (buildMerkleTreeWithHash ld hashFn).toLeafData = ld := by
  induction ld with
  | leaf a => rfl
  | internal left right ihl ihr =>
      simp only [buildMerkleTreeWithHash, populateUp_internal, FullData.toLeafData_internal] at *
      rw [ihl, ihr]

/-- **Perfect correctness of the Merkle vector commitment.** Every position opened honestly against
an honestly built tree verifies the committed value against the committed root. The opening's
authentication path is `generateProof`, and the check reduces to
`InductiveMerkleTree.functional_completeness`. -/
theorem monadicVectorCommitment_perfectlyCorrect {ι : Type} {m : Type → Type} [Monad m]
    [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    (monadicVectorCommitment (m := m) s e hashFn).PerfectlyCorrect := by
  intro data i c st hcst op hop
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (LawfulMonadAttach.eq_of_canReturn_pure hcst).symm
  obtain rfl := LawfulMonadAttach.eq_of_canReturn_pure hop
  simp only [monadicVectorCommitment, List.Vector.toList_length, dite_true,
    decide_eq_true_eq, List.Vector.mk_toList]
  simpa [LeafData.get_ofFn] using
    functional_completeness (e i) (LeafData.ofFn s fun j => data (e.symm j)) hashFn

/-! Per-field reductions for the Merkle vector commitment, letting proofs unfold `commit` /
`openAt` without also unfolding `verifyOpen` into its `dite`. -/

@[simp]
theorem monadicVectorCommitment_openAt {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α)
    (st : FullData α s) (i : ι) :
    (monadicVectorCommitment (m := m) s e hashFn).openAt st i =
      pure (generateProof st (e i)).toList := rfl

theorem monadicVectorCommitment_commit {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) (data : ι → α) :
    (monadicVectorCommitment (m := m) s e hashFn).commit data =
      pure (let t := buildMerkleTreeWithHash (LeafData.ofFn s fun i => data (e.symm i)) hashFn;
        (t.getRootValue, t)) := rfl

/-- **Perfect correctness of the naive batch-opening Merkle commitment**: immediate from
single-position correctness, since `MonadicVectorCommitment.toBatchOpening` preserves it
(`MonadicVectorCommitment.PerfectlyCorrect.toBatchOpening`). -/
theorem naiveBatchOpenMerkleTree_perfectlyCorrect {ι : Type} {m : Type → Type}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    [DecidableEq α] [DecidableEq ι]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    (naiveBatchOpenMerkleTree (m := m) s e hashFn).PerfectlyCorrect :=
  (monadicVectorCommitment_perfectlyCorrect (m := m) s e hashFn).toBatchOpening

end InductiveMerkleTree
