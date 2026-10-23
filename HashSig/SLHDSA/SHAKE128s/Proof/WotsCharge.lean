/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CollisionToDeviating
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Wots
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.WotsPreimage
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalCells
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Correspondence

/-!
# A WOTS chain collision, charged

The third composition, and the one whose shape is a chain rather than a tree.

`Extraction.WotsPreimage.exists_preimage_witness` hands back a preimage, not a collision: on
some chain the forged value, hashed forward a positive number of steps, reaches the honestly
revealed value. `Extraction.Wots.chain_eq_or_collision` already turns that into the dichotomy
the charge needs — either the two chains started equal, in which case the adversary holds a
chain value no signature revealed and the win is on the secret side, or they differ somewhere
and then join, which is a `ChainCollision`.

A `ChainCollision` is the single-child shape: two different values hashed under the same
position address give the same result. So the composition below is the chain analogue of
`MerkleCharge`, resting on `CollisionToDeviating.deviatingCollision_of_single_child`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.WotsCharge

open CanonicalGraph Extraction

/-- **A WOTS chain collision is a charged structural event.** -/
theorem deviatingCollision_of_chainCollision {α : Type} (publicSeed : Digest)
    (cells : Cells) (cache : QueryCache HashSpec) (parent : StructuralNode) (child : Node)
    (address : Address) (start offset : Nat) (actual canonical : Digest)
    -- how this chain position sits in the canonical graph
    (hchildren : parent.children = [child])
    (haddress : parent.address =
      { address with hashOrIndex := BitVec.ofNat 32 (start + offset) })
    (hchildCell : cells child =
      @SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed address
        start offset canonical)
    (hparentCell : cells (.structural parent) =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed parent.address
        (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
          address start offset canonical)))
    -- the collision, and the cache entry its own query left behind
    (hcollision : @Wots.ChainCollision (CacheReplay.replayQuery cache) publicSeed address
      start actual canonical offset)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
      (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        address start offset actual))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hdiffers, hjoins⟩ := hcollision
  refine CollisionToDeviating.deviatingCollision_of_single_child publicSeed cells parent child
    (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed address
      start offset actual) hchildren ?_ result output ?_ ?_
  · rw [hchildCell]
    exact hdiffers
  · rw [hcache]
    exact hentry
  · have hcached := CacheReplay.tweakable_replayQuery cache publicSeed parent.address
      (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        address start offset actual)) output hentry
    rw [hparentCell, ← hcached, haddress]
    exact hjoins

/-! ## Without the bookkeeping

A chain position's node is `CanonicalGraph.wotsPosition`, and the graph's definitions supply
every hypothesis: the node at position `p + 1` has the node at position `p` as its only child
(whether or not `p` is the chain's start), its address carries `p` in `hashOrIndex`, and its
child's honest cell is the chain value at `p` by
`CanonicalGraph.value_wotsPosition`. -/

/-! ## The fifth shape: WOTS public-key compression

`LayerCollision` offers three ways for a layer to fault, and the middle one is a collision at
the node that compresses the thirty-five chain endpoints into the WOTS public key. That is the
array shape again — the same as FORS root compression, but over `chains` rather than
`forsTrees`, and with the children being chain tops rather than tree roots.

The honest children are the chain values at position `w - 1`, which
`CanonicalGraph.value_wotsPosition` identifies, and the honest parent is the WOTS public key,
which `CanonicalGraph.wots_publicKey_cell` identifies with the `wotsPk` cell. -/

open scoped Classical in
/-- **A WOTS public-key compression collision is a charged structural event.** -/
theorem deviatingCollision_of_compressionCollision {α : Type} (publicSeed : Digest)
    (cells : Cells) (cache : QueryCache HashSpec) (parent : StructuralNode)
    (children : Fin chains → Node) (actualEndpoints canonicalEndpoints : Fin chains → Digest)
    (address : Address)
    (hchildren : parent.children = List.ofFn children)
    (hinj : Function.Injective children)
    (haddress : parent.address = SlhDsaSecurity.Wots.publicKeyAddress address)
    (hchildCells : ∀ chainIndex, cells (children chainIndex) = canonicalEndpoints chainIndex)
    (hparentCell : cells (.structural parent) =
      @Hashing.shortHash Id _ (CacheReplay.replayQuery cache)
        (Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
          (digestArrayBytes canonicalEndpoints)))
    (hinputs : Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Wots.publicKeyAddress address) (digestArrayBytes actualEndpoints) ≠
      Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Wots.publicKeyAddress address) (digestArrayBytes canonicalEndpoints))
    (hjoins : @Hashing.shortHash Id _ (CacheReplay.replayQuery cache)
        (Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
          (digestArrayBytes actualEndpoints)) =
      @Hashing.shortHash Id _ (CacheReplay.replayQuery cache)
        (Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
          (digestArrayBytes canonicalEndpoints)))
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
      (digestArrayBytes actualEndpoints)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  have harrays : actualEndpoints ≠ canonicalEndpoints := by
    intro hsame
    exact hinputs (by rw [hsame])
  obtain ⟨chainIndex, hchain⟩ := Function.ne_iff.mp harrays
  refine CollisionToDeviating.deviatingCollision_of_array publicSeed cells parent children
    actualEndpoints hchildren hinj ⟨chainIndex, ?_⟩ result output ?_ ?_
  · rw [hchildCells chainIndex]
    exact hchain
  · rw [hcache]
    exact hentry
  · rw [hparentCell, ← hjoins]
    exact (CacheReplay.shortHash_replayQuery cache _ output (haddress ▸ hentry)).symm

/-! ## The collision as the layer actually hands it over

`Extraction.Hypertree.LayerCollision` reports a chain collision starting at the signed digit,
with the honest side being the *signed* value rather than the chain's start — the adversary
advances from where the signature left off. The canonical lemma above fixed the start at zero,
which does not fit.

This variant takes the collision at an arbitrary start, with the honest side the chain value
there, and lands on the node at `start + offset`. The step that makes it work is
`Correctness.Wots.chain_add`: advancing `offset` from the signed value is the same as
advancing `start + offset` from the derived secret, so the honest side really is the cell at
that position. -/

/-- **A chain collision at the signed digit is charged, unconditionally.** -/
theorem deviatingCollision_of_chainCollision_canonical_at {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (key : WotsKey)
    (chainIndex : Fin chains) (start offset : Nat) (hposition : start + offset < w - 1)
    (actual : Digest)
    (hcollision : @Wots.ChainCollision (CacheReplay.replayQuery cache) publicSeed
      { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } start actual
      (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0 start
        (@Hashing.derive Id _ (CacheReplay.replayQuery cache) publicSeed secretSeed
          (SlhDsaSecurity.Wots.secretAddress key.address chainIndex))) offset)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
      (StructuralNode.wotsHash key chainIndex ⟨start + offset, hposition⟩).address
      (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } start offset
        actual))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  have hinw : start + offset < w := by have := hposition; omega
  have hchildren : (StructuralNode.wotsHash key chainIndex ⟨start + offset, hposition⟩).children =
      [.structural (wotsPosition key chainIndex ⟨start + offset, hinw⟩)] := by
    by_cases hzero : start + offset = 0 <;>
      simp only [wotsPosition, StructuralNode.children] <;> split <;> simp_all
  have hchild : @value (CacheReplay.replayQuery cache) secretSeed publicSeed
        (.structural (wotsPosition key chainIndex ⟨start + offset, hinw⟩)) =
      @SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } start offset
        (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
          { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0 start
          (@Hashing.derive Id _ (CacheReplay.replayQuery cache) publicSeed secretSeed
            (SlhDsaSecurity.Wots.secretAddress key.address chainIndex))) := by
    rw [@value_wotsPosition (CacheReplay.replayQuery cache)]
    have hadd := @Correctness.Wots.chain_add (CacheReplay.replayQuery cache) publicSeed
      { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0 start offset
      (@Hashing.derive Id _ (CacheReplay.replayQuery cache) publicSeed secretSeed
        (SlhDsaSecurity.Wots.secretAddress key.address chainIndex))
    rw [Nat.zero_add] at hadd
    exact hadd
  refine deviatingCollision_of_chainCollision publicSeed
    (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) cache
    (.wotsHash key chainIndex ⟨start + offset, hposition⟩)
    (.structural (wotsPosition key chainIndex ⟨start + offset, hinw⟩))
    { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } start offset
    actual _ hchildren ?_ hchild ?_ hcollision result output hcache hentry
  · simp [StructuralNode.address]
  · rw [CanonicalCells.parentCell_tweakable cache secretSeed publicSeed, hchildren,
      CollisionToDeviating.childBytes_single, hchild]

/-! ## The chain branch of a layer collision

`LayerCollision`'s third disjunct, spelled exactly as the extraction produces it: a chain
index, an offset below the room left by the signed digit, and a collision whose honest side is
the *signed* WOTS value. `Extraction.WotsPreimage.sign_eq_chain` rewrites that signed value as
the chain from the derived secret, which is the form the charge takes. -/

/-- **The chain branch of a layer collision is charged.** -/
theorem deviatingCollision_of_chainBranch {α : Type} (secretSeed publicSeed message : Digest)
    (cache : QueryCache HashSpec) (key : WotsKey) (chainIndex : Fin chains)
    (forged : Digest) (offset : Nat)
    (_hoffset : offset < w - 1 - (Checksum.encode message chainIndex).val)
    (hcollision : @Wots.ChainCollision (CacheReplay.replayQuery cache) publicSeed
      { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val }
      (Checksum.encode message chainIndex).val forged
      (@SlhDsaSecurity.Wots.sign Id _ (CacheReplay.replayQuery cache) message secretSeed
        publicSeed key.address chainIndex) offset)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hposition : (Checksum.encode message chainIndex).val + offset < w - 1)
    (hentry : cache (Hashing.tweakableInput publicSeed
      (StructuralNode.wotsHash key chainIndex
        ⟨(Checksum.encode message chainIndex).val + offset, hposition⟩).address
      (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val }
        (Checksum.encode message chainIndex).val offset forged))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  refine deviatingCollision_of_chainCollision_canonical_at secretSeed publicSeed cache key
    chainIndex _ offset hposition forged ?_ result output hcache hentry
  rwa [@Extraction.WotsPreimage.sign_eq_chain (CacheReplay.replayQuery cache) message secretSeed
    publicSeed key.address chainIndex] at hcollision

/-! ## The compression branch, without the bookkeeping

The `wotsPk` node's children are the thirty-five chain tops at position `w - 1`, and its
address is `Wots.publicKeyAddress`. Both are definitional, so the lemma below states the honest
side of the collision directly as those chain-top cells.

The caller is left to say that `Extraction.Wots.endpoints` of the canonical signature reproduces
them — advancing from the signed digit to the top being the same as advancing from the derived
secret all the way, by `Correctness.Wots.chain_add`. That is
`FaultCharge.endpoints_sign_eq_cells`; this lemma does not perform it. -/

/-- **A WOTS public-key compression collision is charged, unconditionally.** -/
theorem deviatingCollision_of_compressionCollision_canonical {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (key : WotsKey)
    (actualEndpoints : Fin chains → Digest)
    (hinputs : Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Wots.publicKeyAddress key.address)
        (digestArrayBytes actualEndpoints) ≠
      Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Wots.publicKeyAddress key.address)
        (digestArrayBytes (fun chainIndex =>
          @value (CacheReplay.replayQuery cache) secretSeed publicSeed
            (.structural (.wotsHash key chainIndex ⟨w - 2, by decide⟩)))))
    (hjoins : @Hashing.shortHash Id _ (CacheReplay.replayQuery cache)
        (Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress key.address)
          (digestArrayBytes actualEndpoints)) =
      @Hashing.shortHash Id _ (CacheReplay.replayQuery cache)
        (Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress key.address)
          (digestArrayBytes (fun chainIndex =>
            @value (CacheReplay.replayQuery cache) secretSeed publicSeed
              (.structural (.wotsHash key chainIndex ⟨w - 2, by decide⟩))))))
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed (StructuralNode.wotsPk key).address
      (digestArrayBytes actualEndpoints)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  refine deviatingCollision_of_compressionCollision publicSeed
    (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) cache (.wotsPk key)
    (fun chainIndex : Fin chains => .structural (.wotsHash key chainIndex ⟨w - 2, by decide⟩))
    actualEndpoints _ key.address rfl ?_ rfl (fun _ => rfl) ?_ hinputs hjoins result output
    hcache hentry
  · -- Distinct chains name distinct nodes.
    intro left right hsame
    have hval := congrArg (fun node : Node => match node with
      | .structural (.wotsHash _ chainIndex _) => chainIndex.val
      | _ => 0) hsame
    exact Fin.ext (by simpa using hval)
  · rw [CanonicalCells.parentCell_tweakable cache secretSeed publicSeed]
    simp [StructuralNode.children, childBytes_ofFn, Hashing.tweakable,
      StructuralNode.address, SlhDsaSecurity.Wots.publicKeyAddress]

end SlhDsaSecurity.WotsCharge
