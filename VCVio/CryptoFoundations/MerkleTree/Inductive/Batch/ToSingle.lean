/-
Copyright (c) 2026 IAOM / Equation Capital dba Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abraxas1010 (IAOM / Apoth3osis)
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Defs
import VCVio.CryptoFoundations.MerkleTree.Inductive.Binding

/-!
# Reduction of Batch Openings to Single-Index Openings

This file constructs, for every leaf selected by a batch opening, a *single-index*
authentication path whose putative root (in the sense of `getPutativeRootWithHash`) equals
the batch opening's putative root. The construction reads the sibling hash at each level
either directly off the batch proof (when the sibling subtree is pruned) or by recomputing
the sibling's putative subroot from the batch data (when the sibling subtree contains
selected leaves).

This is the deterministic kernel for transferring the single-index security results to batch
openings:

* **Binding transfers now.** `getPutativeBatchRootWithHash_binding` shows that two batch
  openings — under *possibly different selectors* — that both select some leaf index, claim
  distinct values there, and produce the same putative root, yield a concrete hash collision
  via the constructive `findCollision` kernel of `Binding.lean`. (Note this is strictly more
  general than the same-selector uniqueness of `BatchUniqueness.lean`, which needs an
  injective hash; here the hash is arbitrary and the output is a collision as data.)
* **A deterministic kernel for a future extractability transfer.** This file does *not*
  prove batch extractability. What it provides is the deterministic core such a proof will
  consume: `batchToSingleProof` maps any verifying batch opening, at any *selected* leaf, to
  a single-index opening for that leaf recomputing the very same putative root
  (`getPutativeRootWithHash_batchToSingleProof`). The game-level transfer remains future
  work and still has to: package the adversary's *dynamic* choice of selector, preserve the
  commitment-phase extraction log across the reduction, account for the root-recomputation
  query costs, and transfer the winning event itself.

## Main definitions

* `InductiveMerkleTree.selectedValueAt`: the claimed value of a batch opening at a selected
  leaf index.
* `InductiveMerkleTree.batchToSingleProof`: the single-index authentication path extracted
  from a batch opening at a selected leaf index.

## Main results

* `getPutativeRootWithHash_batchToSingleProof` — the extracted single-index opening
  recomputes exactly the batch putative root.
* `getPutativeBatchRootWithHash_binding` — cross-selector batch binding, with the collision
  exhibited by `findCollision`.
-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

/-- The claimed value of a batch opening at a selected leaf index. This is the batch
analogue of the single-index claimed leaf value. -/
def selectedValueAt : {s : Skeleton} → {sel : LeafData Bool s} → SelectedValues α sel →
    (idx : SkeletonLeafIndex s) → sel.get idx = true → α
  | _, .leaf true, v, .ofLeaf, _ => v
  | _, .leaf false, _, .ofLeaf, h => by simp at h
  | _, .internal _ _, v, .ofLeft idxL, h => selectedValueAt v.1 idxL (by simpa using h)
  | _, .internal _ _, v, .ofRight idxR, h => selectedValueAt v.2 idxR (by simpa using h)

/--
Extract a single-index authentication path from a batch opening at a selected leaf index.
At each level, the sibling hash is either stored in the batch proof (pruned sibling) or
recomputed as the sibling's putative batch subroot (sibling with selected leaves).
-/
def batchToSingleProof (hashFn : α → α → α) : {s : Skeleton} → {sel : LeafData Bool s} →
    SelectedValues α sel → BatchProof α sel → (idx : SkeletonLeafIndex s) →
    sel.get idx = true → List.Vector α idx.depth
  | _, _, _, .leaf, .ofLeaf, _ => List.Vector.nil
  | _, _, v, .internalBoth pl pr, .ofLeft idxL, h =>
    List.Vector.cons (getPutativeBatchRootWithHash hashFn v.2 pr)
      (batchToSingleProof hashFn v.1 pl idxL (by simpa using h))
  | _, _, v, .internalBoth pl pr, .ofRight idxR, h =>
    List.Vector.cons (getPutativeBatchRootWithHash hashFn v.1 pl)
      (batchToSingleProof hashFn v.2 pr idxR (by simpa using h))
  | _, _, v, .pruneRight _ rightRoot pl, .ofLeft idxL, h =>
    List.Vector.cons rightRoot (batchToSingleProof hashFn v.1 pl idxL (by simpa using h))
  | _, _, _, .pruneRight hr _ _, .ofRight idxR, h =>
    absurd (LeafData.anySelected_of_get idxR (by simpa using h)) (by simp [hr])
  | _, _, v, .pruneLeft _ leftRoot pr, .ofRight idxR, h =>
    List.Vector.cons leftRoot (batchToSingleProof hashFn v.2 pr idxR (by simpa using h))
  | _, _, _, .pruneLeft hl _ _, .ofLeft idxL, h =>
    absurd (LeafData.anySelected_of_get idxL (by simpa using h)) (by simp [hl])

/--
**Root preservation.** The single-index opening extracted from a batch opening at any
selected leaf recomputes exactly the batch opening's putative root. Consequently a batch
opening that verifies against a root yields, at every selected leaf, a single-index opening
that verifies against the same root.
-/
theorem getPutativeRootWithHash_batchToSingleProof (hashFn : α → α → α)
    {s : Skeleton} {sel : LeafData Bool s}
    (v : SelectedValues α sel) (p : BatchProof α sel)
    (idx : SkeletonLeafIndex s) (hidx : sel.get idx = true) :
    getPutativeRootWithHash idx (selectedValueAt v idx hidx)
      (batchToSingleProof hashFn v p idx hidx) hashFn
    = getPutativeBatchRootWithHash hashFn v p := by
  induction p with
  | leaf =>
    cases idx with
    | ofLeaf => rfl
  | internalBoth pl pr ihl ihr =>
    cases idx with
    | ofLeft idxL =>
      exact congrArg₂ hashFn (ihl v.1 idxL (by simpa using hidx)) rfl
    | ofRight idxR =>
      exact congrArg₂ hashFn rfl (ihr v.2 idxR (by simpa using hidx))
  | pruneRight hr rightRoot pl ih =>
    cases idx with
    | ofLeft idxL =>
      exact congrArg₂ hashFn (ih v.1 idxL (by simpa using hidx)) rfl
    | ofRight idxR =>
      exact absurd (LeafData.anySelected_of_get idxR (by simpa using hidx)) (by simp [hr])
  | pruneLeft hl leftRoot pr ih =>
    cases idx with
    | ofRight idxR =>
      exact congrArg₂ hashFn rfl (ih v.2 idxR (by simpa using hidx))
    | ofLeft idxL =>
      exact absurd (LeafData.anySelected_of_get idxL (by simpa using hidx)) (by simp [hl])

/--
**Cross-selector batch binding.** Two batch openings — under possibly *different* selectors
that both select the leaf index `idx` — which claim distinct values at `idx` yet produce the
same putative root, yield a concrete hash collision, exhibited by the constructive
`findCollision` kernel applied to the two extracted single-index openings.

This strengthens `BatchUniqueness.getPutativeBatchRootWithHash_unique` in two directions:
the two selectors need not be equal, and the hash function is arbitrary (the conclusion is a
collision as data rather than an agreement under an injectivity hypothesis).
-/
theorem getPutativeBatchRootWithHash_binding [DecidableEq α] (hashFn : α → α → α)
    {s : Skeleton} {sel₁ sel₂ : LeafData Bool s}
    (v₁ : SelectedValues α sel₁) (p₁ : BatchProof α sel₁)
    (v₂ : SelectedValues α sel₂) (p₂ : BatchProof α sel₂)
    (idx : SkeletonLeafIndex s) (h₁ : sel₁.get idx = true) (h₂ : sel₂.get idx = true)
    (hne : selectedValueAt v₁ idx h₁ ≠ selectedValueAt v₂ idx h₂)
    (hroot : getPutativeBatchRootWithHash hashFn v₁ p₁
           = getPutativeBatchRootWithHash hashFn v₂ p₂) :
    ∃ l₁ r₁ l₂ r₂,
      findCollision hashFn idx
        (batchToSingleProof hashFn v₁ p₁ idx h₁) (batchToSingleProof hashFn v₂ p₂ idx h₂)
        (selectedValueAt v₁ idx h₁) (selectedValueAt v₂ idx h₂) = some (l₁, r₁, l₂, r₂)
      ∧ Collision hashFn l₁ r₁ l₂ r₂ :=
  getPutativeRootWithHash_binding_collision hashFn idx _ _ _ _ hne
    ((getPutativeRootWithHash_batchToSingleProof hashFn v₁ p₁ idx h₁).trans
      (hroot.trans (getPutativeRootWithHash_batchToSingleProof hashFn v₂ p₂ idx h₂).symm))

end InductiveMerkleTree
