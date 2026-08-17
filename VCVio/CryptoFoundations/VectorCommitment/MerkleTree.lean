/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import VCVio.CryptoFoundations.VectorCommitment.Basic
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Completeness

/-!
# Inductive Merkle trees as (batch-opening) vector commitments

This file realizes the inductive Merkle tree of
`VCVio.CryptoFoundations.MerkleTree.Inductive.Defs` against the abstract positional commitment
interfaces of `VCVio.CryptoFoundations.VectorCommitment.Basic`:

- `InductiveMerkleTree.vectorCommitment` — the Merkle `VectorCommitment` (single-position opening);
- `InductiveMerkleTree.naiveBatchOpenMerkleTree` — a `BatchOpeningVectorCommitment` obtained from
  the above via `VectorCommitment.toBatchOpening`. It is *naive* in that a batch opening is just the
  list of individual leaf authentication paths, with no sharing of common interior hashes; a
  purpose-built batch proof could be more succinct.

These instances are what a consumer such as the Kilian transformation
(`VCVio.CryptoFoundations.Kilian`) is meant to be supplied with; that file depends on the abstract
commitment interface only, not on this concrete Merkle realization.

The construction is in the standard-model / collision-resistant-hash formulation: hashing is a pure
two-to-one function `hashFn`, so all commitment operations are pure and the instances live in any
monad. Positions are laid out on a caller-supplied skeleton `s` via a position-to-leaf equivalence
`e : ι ≃ SkeletonLeafIndex s`; an opening is the authentication path (the sibling hashes along the
leaf's branch), carried as a plain `List` of hashes.
-/

@[expose] public section

open OracleComp OracleSpec BinaryTree

namespace InductiveMerkleTree

variable {α : Type}

/-- Build the leaf data of a Merkle tree of skeleton `s` from a function assigning a value to each
leaf position. -/
def leafDataOfFn : (s : Skeleton) → (SkeletonLeafIndex s → α) → LeafData α s
  | Skeleton.leaf, f => LeafData.leaf (f SkeletonLeafIndex.ofLeaf)
  | Skeleton.internal _ _, f =>
      LeafData.internal
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofLeft i))
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofRight i))

/-- The inductive Merkle tree as a `VectorCommitment`.

Positions `ι` are mapped to the leaves of skeleton `s` by the equivalence `e`, and `hashFn` is the
two-to-one compression function. Committing builds the full tree and exposes its root; an opening
for a position is its authentication path (`generateProof`), carried as a `List`; verification
recomputes the putative root from the leaf value and path (`getPutativeRootWithHash`) and compares
it to the commitment. The operations are pure, so the instance is available in any monad `m`. -/
def vectorCommitment {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    VectorCommitment m ι α α (FullData α s) (List α) where
  commit data :=
    let tree := buildMerkleTreeWithHash (leafDataOfFn s fun i => data (e.symm i)) hashFn
    pure (tree.getRootValue, tree)
  openAt tree i := pure (generateProof tree (e i)).toList
  verifyOpen root i v op :=
    if h : op.length = (e i).depth then
      decide (getPutativeRootWithHash (e i) v ⟨op, h⟩ hashFn = root)
    else false

/-- The inductive Merkle tree as a `BatchOpeningVectorCommitment`, obtained from
`InductiveMerkleTree.vectorCommitment` via `VectorCommitment.toBatchOpening`.

A batch opening for a list of positions is simply the list of their individual authentication paths
(each as `(position, path)`); verification checks each claimed position/value against its path
independently. This shares no interior hashes between paths, hence *naive* — a dedicated multi-leaf
Merkle proof could compress the common prefixes — but it is correct and requires nothing beyond the
single-position instance. -/
def naiveBatchOpenMerkleTree {ι : Type} {m : Type → Type} [Monad m]
    [DecidableEq ι] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    BatchOpeningVectorCommitment m ι α α (FullData α s) (List (ι × List α)) :=
  (vectorCommitment s e hashFn).toBatchOpening

/-! ### Correctness -/

/-- Eta for `List.Vector`: rebuilding the subtype from `v.toList` returns `v`. -/
@[simp]
theorem vector_mk_toList {n : ℕ} (v : List.Vector α n) (h : v.toList.length = n) :
    (⟨v.toList, h⟩ : List.Vector α n) = v :=
  List.Vector.toList_injective (List.Vector.toList_mk _ _)

/-- Rebuilding a tree from leaf data `ld` and reading its leaves back recovers `ld`. -/
@[simp]
theorem toLeafData_buildMerkleTreeWithHash {s : Skeleton}
    (ld : LeafData α s) (hashFn : α → α → α) :
    (buildMerkleTreeWithHash ld hashFn).toLeafData = ld := by
  induction ld with
  | leaf a => rfl
  | internal left right ihl ihr =>
      simp only [buildMerkleTreeWithHash, populateUp_internal, FullData.toLeafData_internal] at *
      rw [ihl, ihr]

/-- Reading a leaf of the leaf data built from a function recovers the function's value there. -/
@[simp]
theorem get_leafDataOfFn : ∀ {s : Skeleton} (f : SkeletonLeafIndex s → α)
    (l : SkeletonLeafIndex s), (leafDataOfFn s f).get l = f l
  | Skeleton.leaf, _, SkeletonLeafIndex.ofLeaf => rfl
  | Skeleton.internal _ _, f, SkeletonLeafIndex.ofLeft il =>
      get_leafDataOfFn (fun i => f (SkeletonLeafIndex.ofLeft i)) il
  | Skeleton.internal _ _, f, SkeletonLeafIndex.ofRight ir =>
      get_leafDataOfFn (fun i => f (SkeletonLeafIndex.ofRight i)) ir

/-- **Perfect correctness of the Merkle vector commitment.** Every position opened honestly against
an honestly built tree verifies the committed value against the committed root. The opening's
authentication path is `generateProof`, and the check reduces to
`InductiveMerkleTree.functional_completeness`. -/
theorem vectorCommitment_perfectlyCorrect {ι : Type} {m : Type → Type} [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    (vectorCommitment (m := m) s e hashFn).PerfectlyCorrect := by
  intro data i c st hcst op hop
  simp only [vectorCommitment, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcst
  obtain ⟨rfl, rfl⟩ := hcst
  simp only [vectorCommitment, support_pure, Set.mem_singleton_iff] at hop
  subst hop
  simp only [vectorCommitment, List.Vector.toList_length, dite_true,
    decide_eq_true_eq, vector_mk_toList]
  simpa [get_leafDataOfFn] using
    functional_completeness (e i) (leafDataOfFn s fun j => data (e.symm j)) hashFn

/-! Per-field reductions for the Merkle vector commitment, letting proofs unfold `commit` /
`openAt` without also unfolding `verifyOpen` into its `dite`. -/

@[simp]
theorem vectorCommitment_openAt {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α)
    (st : FullData α s) (i : ι) :
    (vectorCommitment (m := m) s e hashFn).openAt st i =
      pure (generateProof st (e i)).toList := rfl

theorem vectorCommitment_commit {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) (data : ι → α) :
    (vectorCommitment (m := m) s e hashFn).commit data =
      pure (let t := buildMerkleTreeWithHash (leafDataOfFn s fun i => data (e.symm i)) hashFn;
        (t.getRootValue, t)) := rfl

/-- **Perfect correctness of the naive batch-opening Merkle commitment**: immediate from
single-position correctness, since `VectorCommitment.toBatchOpening` preserves it
(`VectorCommitment.PerfectlyCorrect.toBatchOpening`). -/
theorem naiveBatchOpenMerkleTree_perfectlyCorrect {ι : Type} {m : Type → Type}
    [Monad m] [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [DecidableEq α] [DecidableEq ι]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    (naiveBatchOpenMerkleTree (m := m) s e hashFn).PerfectlyCorrect :=
  (vectorCommitment_perfectlyCorrect (m := m) s e hashFn).toBatchOpening

end InductiveMerkleTree
