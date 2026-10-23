/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CollisionToDeviating
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalCells

/-!
# A Merkle path collision, charged

This is the first full composition of the forgery decomposition: it takes the object the
extraction chain actually produces — a `BinaryPath.Collision` inside a `LayerCollision` — and
lands on the object the charge actually consumes, a `StructuralTerm.DeviatingCollision`.

Three facts meet here.

* `BinaryPath.canonical_step` says the canonical pair at a path position recombines to the
  honest node above it, so the collision's shared hash value *is* that honest node.
* `CacheReplay.tweakable_replayQuery` says the `Id`-level `combine` the extraction reasons
  with is the truncation of whatever the cache holds at the corresponding byte input — so the
  shared value is a cache entry's truncation.
* `CollisionToDeviating.deviatingCollision_of_tree_pair` converts a differing child pair whose
  input is cached into the charged event.

What is carried as hypotheses rather than derived is the index bookkeeping: `BinaryPath`
indexes a path by `Nat` and divides by powers of two, while the canonical graph indexes nodes
by `Fin`. Matching the two is arithmetic with no cryptographic content, and keeping it in the
hypotheses lets the actual argument be stated once rather than per layer.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.MerkleCharge

open CanonicalGraph Extraction

/-! ## The canonical pair is the pair of graph children

The one place the Merkle case needs arithmetic rather than unfolding. `BinaryPath` names a
path position by an index and a height and reaches the sibling by `xor … 1`, ordering the two
so the one on the path keeps its side; the canonical graph names the two children of a node
directly as `2 * i` and `2 * i + 1`. The two descriptions agree, and the proof is the parity
split: at an even position the node is the left child and its sibling the right, at an odd
position the other way round, and in both cases `2 * (index / 2 ^ (height + 1))` is the left
child's index.
-/

theorem canonicalPair_fst (nodes : Nat → Nat → Digest) (index height : Nat) :
    (BinaryPath.canonicalPair nodes index height).1 =
      nodes height (2 * (index / 2 ^ (height + 1))) := by
  have hhalf : index / 2 ^ (height + 1) = (index / 2 ^ height) / 2 :=
    Correctness.div_pow_succ index height
  by_cases heven : index / 2 ^ height % 2 = 0
  · simp only [BinaryPath.canonicalPair, BinaryPath.ordered, if_pos heven]
    congr 1
    omega
  · have hxor : Nat.xor (index / 2 ^ height) 1 = index / 2 ^ height - 1 :=
      Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))
    simp only [BinaryPath.canonicalPair, BinaryPath.ordered, if_neg heven, hxor]
    congr 1
    omega

theorem canonicalPair_snd (nodes : Nat → Nat → Digest) (index height : Nat) :
    (BinaryPath.canonicalPair nodes index height).2 =
      nodes height (2 * (index / 2 ^ (height + 1)) + 1) := by
  have hhalf : index / 2 ^ (height + 1) = (index / 2 ^ height) / 2 :=
    Correctness.div_pow_succ index height
  by_cases heven : index / 2 ^ height % 2 = 0
  · have hxor : Nat.xor (index / 2 ^ height) 1 = index / 2 ^ height + 1 :=
      Nat.xor_one_of_even (Nat.even_iff.mpr heven)
    simp only [BinaryPath.canonicalPair, BinaryPath.ordered, if_pos heven, hxor]
    congr 1
    omega
  · simp only [BinaryPath.canonicalPair, BinaryPath.ordered, if_neg heven]
    congr 1
    omega

/-- **A path collision is a charged structural event.** -/
theorem deviatingCollision_of_pathCollision {α : Type} (publicSeed : Digest) (cells : Cells)
    (cache : QueryCache HashSpec) (address : Address) (nodes : Nat → Nat → Digest)
    (index height : Nat) (leaf : Digest) (siblings : Nat → Digest)
    (location : Tree) (parentHeight : Fin subtreeHeight)
    (parentIndex : Fin (2 ^ (subtreeHeight - (parentHeight.val + 1))))
    -- the combination rule the extraction uses, answered from this cache
    (combine : Nat → Nat → Digest → Digest → Digest)
    (hcombine : ∀ h i l r, combine h i l r =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
        (SlhDsaSecurity.Merkle.nodeAddress address h i) (BinaryPath.pairBytes (l, r)))
    (hnodes : ∀ h i, nodes (h + 1) i =
      combine (h + 1) i (nodes h (2 * i)) (nodes h (2 * i + 1)))
    -- how this path position sits in the canonical graph
    (haddress : (StructuralNode.tree location parentHeight parentIndex).address =
      SlhDsaSecurity.Merkle.nodeAddress address (height + 1) (index / 2 ^ (height + 1)))
    (hchildren : (StructuralNode.tree location parentHeight parentIndex).children =
      [.structural (merkleChild location parentHeight parentIndex 0),
        .structural (merkleChild location parentHeight parentIndex 1)])
    (hdistinct : (Node.structural (merkleChild location parentHeight parentIndex 0)) ≠
      .structural (merkleChild location parentHeight parentIndex 1))
    (hparentCell : cells (.structural (.tree location parentHeight parentIndex)) =
      nodes (height + 1) (index / 2 ^ (height + 1)))
    (hleftCell : cells (.structural (merkleChild location parentHeight parentIndex 0)) =
      (BinaryPath.canonicalPair nodes index height).1)
    (hrightCell : cells (.structural (merkleChild location parentHeight parentIndex 1)) =
      (BinaryPath.canonicalPair nodes index height).2)
    -- the collision, and the cache entry its own query left behind
    (hcollision : BinaryPath.Collision nodes combine index leaf siblings height)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
        (StructuralNode.tree location parentHeight parentIndex).address
        (BinaryPath.pairBytes
          (BinaryPath.ordered index height
            (BinaryPath.value combine index leaf siblings height) (siblings height)))) =
      some output) :

    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hdiffers, hjoins⟩ := hcollision
  set actual := BinaryPath.ordered index height
    (BinaryPath.value combine index leaf siblings height) (siblings height) with hactualDef
  -- The canonical pair recombines to the honest node, so the shared value is that node.
  have hcanonical := BinaryPath.canonical_step nodes combine hnodes index height
  -- The shared value is also the truncation of the cached answer at the actual pair.
  have hactual : combine (height + 1) (index / 2 ^ (height + 1)) actual.1 actual.2 =
      Hashing.truncate output := by
    rw [hcombine, ← haddress]
    exact CacheReplay.tweakable_replayQuery cache publicSeed _ _ output hentry
  refine CollisionToDeviating.deviatingCollision_of_tree_pair publicSeed cells location
    parentHeight parentIndex actual.1 actual.2 hchildren hdistinct ?_ result output ?_ ?_
  · -- The actual pair differs from the honest one.
    rw [hleftCell, hrightCell]
    exact fun hsame =>
      hdiffers (Prod.ext (congrArg Prod.fst hsame) (congrArg Prod.snd hsame))
  · rw [hcache]
    exact hentry
  · -- and its answer truncates to the parent's honest cell.
    rw [hparentCell, ← hcanonical, ← hjoins]
    exact hactual.symm

/-! ## Without the graph-side bookkeeping

With `canonicalPair_fst` and `canonicalPair_snd` in hand, every hypothesis about *where the
node sits* is discharged by the graph's definitions: a tree node's children are its two
`merkleChild`s, its address is `Merkle.nodeAddress` at the height above, and the children's
honest cells are the canonical pair. What a caller still supplies is the extraction's own
content — that `combine` is the tweakable hash answered from this cache, that `nodes` satisfies
the Merkle recursion, and that the path index names this node — all definitional where the
layer is known. -/

/-- **A Merkle path collision is charged, with the graph-side bookkeeping discharged.** -/
theorem deviatingCollision_of_pathCollision_canonical {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (location : Tree)
    (index : Nat) (parentHeight : Fin subtreeHeight)
    (parentIndex : Fin (2 ^ (subtreeHeight - (parentHeight.val + 1))))
    (leaf : Digest) (siblings : Nat → Digest)
    (combine : Nat → Nat → Digest → Digest → Digest)
    (hcombine : ∀ h i l r, combine h i l r =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
        (SlhDsaSecurity.Merkle.nodeAddress location.address h i)
        (BinaryPath.pairBytes (l, r)))
    (hnodes : ∀ h i,
      @SlhDsaSecurity.Merkle.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
          location.address (h + 1) i =
        combine (h + 1) i
          (@SlhDsaSecurity.Merkle.node Id _ (CacheReplay.replayQuery cache) secretSeed
            publicSeed location.address h (2 * i))
          (@SlhDsaSecurity.Merkle.node Id _ (CacheReplay.replayQuery cache) secretSeed
            publicSeed location.address h (2 * i + 1)))
    (hindex : parentIndex.val = index / 2 ^ (parentHeight.val + 1))
    (hcollision : BinaryPath.Collision
      (@SlhDsaSecurity.Merkle.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
        location.address)
      combine index leaf siblings parentHeight.val)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
        (StructuralNode.tree location parentHeight parentIndex).address
        (BinaryPath.pairBytes
          (BinaryPath.ordered index parentHeight.val
            (BinaryPath.value combine index leaf siblings parentHeight.val)
            (siblings parentHeight.val)))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  refine deviatingCollision_of_pathCollision publicSeed
    (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) cache location.address
    (@SlhDsaSecurity.Merkle.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
      location.address)
    index parentHeight.val leaf siblings location parentHeight parentIndex combine hcombine
    hnodes ?_ rfl ?_ ?_ ?_ ?_ hcollision result output hcache hentry
  · rw [StructuralNode.address, hindex]
  · -- The two children are distinct nodes.
    intro hsame
    have hval := congrArg (fun node : Node => match node with
      | .structural (.tree _ _ idx) => idx.val
      | .structural (.wotsPk key) => key.leaf.val
      | _ => 0) hsame
    by_cases hzero : parentHeight.val = 0 <;>
      simp [merkleChild, merkleNode, hzero] at hval
  · simp only [value, structuralValue]
    rw [hindex]
  · rw [@value_merkleChild (CacheReplay.replayQuery cache), canonicalPair_fst, hindex]
    simp
  · rw [@value_merkleChild (CacheReplay.replayQuery cache), canonicalPair_snd, hindex]
    simp

/-! ## The path branch of a layer collision

`LayerCollision`'s first disjunct, as the extraction produces it: a height below `subtreeHeight`
and a `BinaryPath.Collision` on the authentication path, with the nodes being the honest Merkle
nodes of this layer's tree and the leaf the WOTS public key recovered from the signature.

Everything the canonical lemma needs is definitional here. The nodes satisfy the Merkle
recursion because that is how `Merkle.node` is defined; the combination is the tweakable hash
at this tree's address; and the node the collision sits at is the one whose index is the path
index divided by the height's power of two, which is how `Fin` is built below. -/

/-- **The path branch of a layer collision is charged.** -/
theorem deviatingCollision_of_pathBranch {α : Type} (secretSeed publicSeed : Digest)
    (cache : QueryCache HashSpec) (location : Tree) (leafIndex : Nat)
    (_hleafIndex : leafIndex < 2 ^ subtreeHeight) (leaf : Digest) (siblings : Nat → Digest)
    (pathHeight : Fin subtreeHeight)
    (hcollision : BinaryPath.Collision
      (@SlhDsaSecurity.Merkle.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
        location.address)
      (fun height nodeIndex left right =>
        @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
          (SlhDsaSecurity.Merkle.nodeAddress location.address height nodeIndex)
          (BinaryPath.pairBytes (left, right)))
      leafIndex leaf siblings pathHeight.val)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hbound : leafIndex / 2 ^ (pathHeight.val + 1) < 2 ^ (subtreeHeight - (pathHeight.val + 1)))
    (hentry : cache (Hashing.tweakableInput publicSeed
        (StructuralNode.tree location pathHeight
          ⟨leafIndex / 2 ^ (pathHeight.val + 1), hbound⟩).address
        (BinaryPath.pairBytes
          (BinaryPath.ordered leafIndex pathHeight.val
            (BinaryPath.value
              (fun height nodeIndex left right =>
                @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
                  (SlhDsaSecurity.Merkle.nodeAddress location.address height nodeIndex)
                  (BinaryPath.pairBytes (left, right)))
              leafIndex leaf siblings pathHeight.val)
            (siblings pathHeight.val)))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  refine deviatingCollision_of_pathCollision_canonical secretSeed publicSeed cache location
    leafIndex pathHeight ⟨leafIndex / 2 ^ (pathHeight.val + 1), hbound⟩ leaf siblings _
    (fun _ _ _ _ => rfl) (fun _ _ => rfl) rfl ?_ result output hcache ?_
  · exact hcollision
  · exact hentry

end SlhDsaSecurity.MerkleCharge
