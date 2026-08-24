/-
Copyright (c) 2026 Richard Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Basic

/-! # Level-Separated Merkle Trees, as an instance of the addressed engine

Per-**level** domain separation — every node at the same subtree depth hashes under
the same tweak — obtained by specializing the node-addressed engine's `nodeHash`
through `SkeletonInternalIndex.subtreeDepth`. Nothing here is proven from scratch: building,
completeness, and the (oriented) collision kernel are the engine's theorems at
`levelNodeHash`.

This is deliberately **not** the XMSS / SLH-DSA layout, which separates by full node
address; that is the engine itself (`addressedNodeHash`), of which this file is the
depth-collapsed special case (`levelNodeHash_eq_addressed`).
-/

@[expose] public section

namespace AddressedMerkleTree

open BinaryTree InductiveMerkleTree

variable {PkSeed Tweak Y : Type} [DecidableEq Y]

/-- Build a level-separated Merkle tree: node at subtree-depth `d` hashes under
`tweakAt d`. -/
def buildMerkleTreeLevel (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed)
    (tweakAt : ℕ → Tweak) {s : Skeleton} (ld : LeafData Y s) : FullData Y s :=
  buildMerkleTreeAddressedWithHash ld (levelNodeHash th pk tweakAt)

/-- Putative-root recomputation for the level-separated tree. -/
def getPutativeRootLevel (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed)
    (tweakAt : ℕ → Tweak) {s : Skeleton} (idx : SkeletonLeafIndex s) (leafValue : Y)
    (proof : List.Vector Y idx.depth) : Y :=
  getPutativeRootAddressedWithHash (levelNodeHash th pk tweakAt) idx leafValue proof

omit [DecidableEq Y] in
/-- Completeness for the level-separated tree — the engine's completeness at
`levelNodeHash`. -/
theorem level_functional_completeness (th : TweakableHash PkSeed Tweak (Y × Y) Y)
    (pk : PkSeed) (tweakAt : ℕ → Tweak) {s : Skeleton}
    (idx : SkeletonLeafIndex s) (ld : LeafData Y s) :
    getPutativeRootLevel th pk tweakAt idx (ld.get idx)
      (generateProof (buildMerkleTreeLevel th pk tweakAt ld) idx)
    = (buildMerkleTreeLevel th pk tweakAt ld).getRootValue := by
  let : DecidableEq Y := Classical.decEq Y
  exact addressed_functional_completeness idx ld (levelNodeHash th pk tweakAt)

omit [DecidableEq Y] in
/-- **Oriented binding** for the level-separated tree — the engine's oriented
binding at `levelNodeHash`: an adversarial opening verifying against an honestly
built root with a different leaf yields two distinct pairs with equal digest under
the tweak of the collision's level, the first pair being the honestly-precommitted
one at the tagged address. -/
theorem level_oriented_binding (th : TweakableHash PkSeed Tweak (Y × Y) Y)
    (pk : PkSeed) (tweakAt : ℕ → Tweak) {s : Skeleton} (ld : LeafData Y s)
    (idx : SkeletonLeafIndex s) (y : Y) (proof₂ : List.Vector Y idx.depth)
    (hroot : getPutativeRootLevel th pk tweakAt idx y proof₂
      = (buildMerkleTreeLevel th pk tweakAt ld).getRootValue)
    (hne : ld.get idx ≠ y) :
    ∃ (a : SkeletonInternalIndex s) (c : Y × Y),
      (childPairAt (buildMerkleTreeLevel th pk tweakAt ld) a) ≠ c ∧
      th.eval pk (tweakAt a.subtreeDepth)
          ((childPairAt (buildMerkleTreeLevel th pk tweakAt ld) a).1,
           (childPairAt (buildMerkleTreeLevel th pk tweakAt ld) a).2)
        = th.eval pk (tweakAt a.subtreeDepth) (c.1, c.2) := by
  let : DecidableEq Y := Classical.decEq Y
  exact addressed_oriented_binding (levelNodeHash th pk tweakAt) ld idx y proof₂ hroot hne

end AddressedMerkleTree
