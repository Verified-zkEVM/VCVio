/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CollisionToDeviating
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Fors
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalCells

/-!
# A FORS leaf collision, charged

The last of the four node shapes. `Extraction.Fors.LeafCollision` says a forged secret differs
from the honest one at a FORS leaf yet hashes to the same leaf value under that leaf's
address — already the single-child shape, so the composition is the direct analogue of
`WotsCharge`.

`Extraction.Fors.recoveredLeaf_canonical_secret_or_collision` is what produces it, and its
other branch is the one that matters for the budget: if there is no collision then the forged
secret *is* the honest secret.

That branch is not by itself the coverage avenue, and the difference is not a formality.
Holding the honest secret is possession, not disclosure: `Fors.secret` is the oracle's answer at
an input carrying `SK.seed` in the clear, so a run can hold it by asking for it rather than by
being given it. The step from possession to "that FORS position was signed" is a *disjunction* —
signed, or the run made a sensitive query — and the second branch belongs to the input half.
It is the FORS counterpart of the WOTS residue, and nothing in this file proves it.

Granting the disclosure branch, the coverage avenue is charged on the message class and the
collision avenue on the structural one, which is why the per-class accounting is what makes the
target reachable.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.ForsLeafCharge

open CanonicalGraph Extraction

/-- **A FORS leaf collision is a charged structural event.** -/
theorem deviatingCollision_of_leafCollision {α : Type} (publicSeed secretSeed : Digest)
    (cells : Cells) (cache : QueryCache HashSpec) (parent : StructuralNode) (child : Node)
    (address : Address) (index : Nat) (forgedSecret : Digest)
    -- how this leaf sits in the canonical graph
    (hchildren : parent.children = [child])
    (haddress : parent.address = SLHDSA.SHAKE128s.Fors.nodeAddress address 0 index)
    (hchildCell : cells child =
      @SLHDSA.SHAKE128s.Fors.secret Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
        address index)
    (hparentCell : cells (.structural parent) =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed parent.address
        (bytesBE n (@SLHDSA.SHAKE128s.Fors.secret Id _ (CacheReplay.replayQuery cache)
          secretSeed publicSeed address index)))
    -- the collision, and the cache entry its own query left behind
    (hcollision : @Fors.LeafCollision (CacheReplay.replayQuery cache) secretSeed publicSeed
      address index forgedSecret)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
      (bytesBE n forgedSecret)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hdiffers, hjoins⟩ := hcollision
  refine CollisionToDeviating.deviatingCollision_of_single_child publicSeed cells parent child
    forgedSecret hchildren ?_ result output ?_ ?_
  · rw [hchildCell]
    exact hdiffers
  · rw [hcache]
    exact hentry
  · have hcached := CacheReplay.tweakable_replayQuery cache publicSeed parent.address
      (bytesBE n forgedSecret) output hentry
    rw [hparentCell, ← hcached, haddress]
    exact hjoins

/-! ## Without the bookkeeping

At a FORS leaf every hypothesis above is discharged by the graph's own definitions: the leaf's
children list is the single `forsPrf` node, its address is `Fors.nodeAddress` at height zero
by definition, its child's honest cell is the FORS secret by definition, and the parent-cell
equation is `CanonicalCells.parentCell_tweakable`. So the charge applies with nothing left to
supply but the collision and the cache entry it left behind. -/

/-- **A FORS leaf collision is charged, unconditionally.** -/
theorem deviatingCollision_of_leafCollision_canonical {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (key : ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) (forgedSecret : Digest)
    (hcollision : @Fors.LeafCollision (CacheReplay.replayQuery cache) secretSeed publicSeed
      key.address index.val forgedSecret)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
      (SLHDSA.SHAKE128s.Fors.nodeAddress key.address 0 index.val)
      (bytesBE n forgedSecret)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  have hindex : index.val < forsTrees * 2 ^ (forsHeight - (0 : Fin (forsHeight + 1)).val) := by
    simp
  refine deviatingCollision_of_leafCollision publicSeed secretSeed
    (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) cache
    (.forsTree key 0 ⟨index.val, hindex⟩) (.structural (.forsPrf key index))
    key.address index.val forgedSecret ?_ rfl rfl ?_ hcollision result output hcache hentry
  · simp [StructuralNode.children]
  · rw [CanonicalCells.parentCell_tweakable cache secretSeed publicSeed]
    simp [StructuralNode.children, childBytes, value, structuralValue]

end SLHDSA.SHAKE128s.ForsLeafCharge
