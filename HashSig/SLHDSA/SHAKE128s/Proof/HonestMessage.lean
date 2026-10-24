/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.WotsResidueReduction
public import HashSig.SLHDSA.SHAKE128s.Proof.GraphStakes

/-!
# The message a hypertree key signs, as a function of the key

`GraphStakes.honestMessage` is *defined* as the honest node one layer down, read off the key's
own coordinates. That definition is only worth something if it is the message the hypertree
actually threads into that key, and this file proves it, against
`WotsResidueReduction.revealedAt` — the recursion the residue reduction itself produces.

The content is one piece of index arithmetic. The residue threads, as the message for the key
reached after `i + 1` steps, the honest node of the subtree the previous step was looking at;
that subtree's coordinates are `(layerAt layer i, treeAt tree i)`. The key reached after `i + 1`
steps sits at layer `layerAt layer (i + 1)` with subtree index `treeAt tree (i + 1)` and leaf
`leafAt leaf tree (i + 1)`, and those two recombine to the previous subtree index exactly:
dividing by `2 ^ subtreeHeight` and taking the remainder is what the step does, so putting them
back together is `Nat.div_add_mod`.

So the message is a function of the key and the seeds alone, which is what the whole WOTS clause
rests on — each hypertree key signs one message, fixed before the adversary runs.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestMessage

open CanonicalGraph WotsResidueReduction

/-- **The step's subtree index and leaf recombine to the subtree the step came from.** -/
theorem treeAt_succ_add_leafAt (tree : Nat) :
    ∀ (i : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex),
      treeAt tree (i + 1) * 2 ^ subtreeHeight + (leafAt leaf tree (i + 1)).val =
        treeAt tree i := by
  intro i
  induction i generalizing tree with
  | zero =>
    intro leaf
    change tree / 2 ^ subtreeHeight * 2 ^ subtreeHeight + tree % 2 ^ subtreeHeight = tree
    rw [Nat.mul_comm]
    exact Nat.div_add_mod tree (2 ^ subtreeHeight)
  | succ i ih =>
    intro leaf
    exact ih (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)

attribute [local irreducible] Extraction.HypertreeChain.honestNode CanonicalGraph.value

variable [HasQuery HashSpec Id]

/-- **The message the residue threads at step `i + 1`** is the honest node of the subtree the
previous step was looking at. -/
theorem revealedAt_succ (secretSeed publicSeed : Digest) :
    ∀ (i : Nat) (expectedInput : Digest) (layer tree : Nat),
      revealedAt secretSeed publicSeed expectedInput layer tree (i + 1) =
        Extraction.HypertreeChain.honestNode secretSeed publicSeed (layerAt layer i)
          (treeAt tree i) := by
  intro i
  induction i with
  | zero =>
    intro expectedInput layer tree
    simp only [revealedAt, layerAt, treeAt]
  | succ i ih =>
    intro expectedInput layer tree
    rw [show revealedAt secretSeed publicSeed expectedInput layer tree (i + 1 + 1) =
        revealedAt secretSeed publicSeed
          (Extraction.HypertreeChain.honestNode secretSeed publicSeed layer tree) (layer + 1)
          (tree / 2 ^ subtreeHeight) (i + 1) from rfl,
      ih _ (layer + 1) (tree / 2 ^ subtreeHeight)]
    simp only [layerAt, treeAt]

/-- Above the bottom layer, the message a key signs is the honest node of the subtree its own
coordinates name. -/
theorem honestMessage_succ (secretSeed publicSeed : Digest) (key : WotsKey) (layer : Nat)
    (hlayer : key.tree.layer.val = layer + 1) :
    GraphStakes.honestMessage secretSeed publicSeed key =
      Extraction.HypertreeChain.honestNode secretSeed publicSeed layer
        (key.tree.tree.val * 2 ^ subtreeHeight + key.leaf.val) := by
  rw [GraphStakes.honestMessage, hlayer]

/-- **The message the residue threads is the message the key signs.** -/
theorem honestMessage_eq_revealedAt (secretSeed publicSeed expectedInput : Digest)
    (layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (i : Nat) (key : WotsKey)
    (hlayer : key.tree.layer.val = layerAt layer (i + 1))
    (htree : key.tree.tree.val = treeAt tree (i + 1))
    (hleaf : key.leaf.val = (leafAt leaf tree (i + 1)).val) :
    GraphStakes.honestMessage secretSeed publicSeed key =
      revealedAt secretSeed publicSeed expectedInput layer tree (i + 1) := by
  rw [honestMessage_succ secretSeed publicSeed key (layerAt layer i) (by
      rw [hlayer, layerAt_eq, layerAt_eq]; omega),
    revealedAt_succ secretSeed publicSeed i expectedInput layer tree, htree, hleaf,
    treeAt_succ_add_leafAt tree i leaf]

/-- **The revealed digit is the digit of the message the residue threads.** The instantiation
the WOTS clause asks for: `GraphStakes.honestRevealed` really is the digit that key's own
signature discloses. -/
theorem honestRevealed_eq (secretSeed publicSeed expectedInput : Digest)
    (layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (i : Nat) (key : WotsKey)
    (hlayer : key.tree.layer.val = layerAt layer (i + 1))
    (htree : key.tree.tree.val = treeAt tree (i + 1))
    (hleaf : key.leaf.val = (leafAt leaf tree (i + 1)).val) (chain : Fin chains) :
    GraphStakes.honestRevealed secretSeed publicSeed key chain =
      (Checksum.encode (revealedAt secretSeed publicSeed expectedInput layer tree (i + 1))
        chain).val := by
  rw [GraphStakes.honestRevealed,
    honestMessage_eq_revealedAt secretSeed publicSeed expectedInput layer tree leaf i key
      hlayer htree hleaf]

end SlhDsaSecurity.HonestMessage
