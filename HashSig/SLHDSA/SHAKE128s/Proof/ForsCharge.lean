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
# A FORS root-compression collision, charged

The companion to `MerkleCharge` for the other node shape the extraction chain produces.
`Extraction.Fors.CompressionCollision` says two different root arrays hash to the same value
under the FORS root address; the charge wants a differing child together with a cache entry
whose answer truncates to the parent's honest cell.

The derivation is short because the collision already carries both halves. That the arrays
differ follows from the byte inputs differing, since they share a seed and an address and so
can only differ in their payloads. That the shared hash value is the parent's honest cell is
the FORS public key being that cell — `CanonicalGraph.Correspondence.fors_publicKey_cell` —
and `CacheReplay.shortHash_replayQuery` turns the `Id`-level hash into the cached answer's
truncation.

As in `MerkleCharge`, the correspondence between the extraction's indices and the canonical
graph's nodes is carried as hypotheses: it is bookkeeping, discharged where the layer is
known, and stating it here would tie the argument to one layer.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ForsCharge

open CanonicalGraph Extraction

/-- **A FORS root-compression collision is a charged structural event.** -/
theorem deviatingCollision_of_compressionCollision {α : Type} (publicSeed : Digest)
    (cells : Cells) (cache : QueryCache HashSpec) (parent : StructuralNode)
    (children : Fin forsTrees → Node) (actualRoots canonicalRoots : Fin forsTrees → Digest)
    (address : Address)
    -- how this compression node sits in the canonical graph
    (hchildren : parent.children = List.ofFn children)
    (hinj : Function.Injective children)
    (haddress : parent.address = Extraction.Fors.rootAddress address)
    (hchildCells : ∀ tree, cells (children tree) = canonicalRoots tree)
    (hparentCell : cells (.structural parent) =
      @Hashing.shortHash Id _ (CacheReplay.replayQuery cache)
        (Hashing.tweakableInput publicSeed (Extraction.Fors.rootAddress address)
          (digestArrayBytes canonicalRoots)))
    -- the collision, and the cache entry its own query left behind
    (hcollision : @Extraction.Fors.CompressionCollision (CacheReplay.replayQuery cache)
      actualRoots canonicalRoots publicSeed address)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
      (digestArrayBytes actualRoots)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hinputs, hjoins⟩ := hcollision
  -- Sharing a seed and an address, the inputs can differ only in their payloads.
  have harrays : actualRoots ≠ canonicalRoots := by
    intro hsame
    exact hinputs (by rw [hsame])
  obtain ⟨tree, htree⟩ := Function.ne_iff.mp harrays
  refine CollisionToDeviating.deviatingCollision_of_array publicSeed cells parent children
    actualRoots hchildren hinj ⟨tree, ?_⟩ result output ?_ ?_
  · rw [hchildCells tree]
    exact htree
  · rw [hcache]
    exact hentry
  · -- The shared hash value is the parent's honest cell, read out of the cache.
    rw [hparentCell, ← hjoins]
    exact (CacheReplay.shortHash_replayQuery cache _ output (haddress ▸ hentry)).symm

/-! ## Without the bookkeeping

As at the leaf, every hypothesis is discharged by the graph's own definitions. The compression
node's children are the fourteen `forsTree` nodes at full height, given by `List.ofFn`; the
map is injective because the constructor is and `Fin.val` determines the index; its address is
`Extraction.Fors.rootAddress` by definition; the children's honest cells are
`Extraction.Fors.canonicalRoots` by definition; and the parent-cell equation is
`CanonicalCells.parentCell_tweakable`. -/

/-- **A FORS root-compression collision is charged, unconditionally.** -/
theorem deviatingCollision_of_compressionCollision_canonical {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (key : ForsKey)
    (actualRoots : Fin forsTrees → Digest)
    (hcollision : @Extraction.Fors.CompressionCollision (CacheReplay.replayQuery cache)
      actualRoots (@Extraction.Fors.canonicalRoots (CacheReplay.replayQuery cache)
        secretSeed publicSeed key.address) publicSeed key.address)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
      (StructuralNode.forsRoots key).address (digestArrayBytes actualRoots)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  refine deviatingCollision_of_compressionCollision publicSeed
    (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) cache (.forsRoots key)
    (fun tree : Fin forsTrees =>
      .structural (.forsTree key ⟨forsHeight, by omega⟩ ⟨tree.val, by simp [tree.isLt]⟩))
    actualRoots _ key.address rfl ?_ rfl (fun _ => rfl) ?_ hcollision result output
    hcache hentry
  · -- Distinct trees name distinct nodes.
    intro left right hsame
    have hval := congrArg (fun node : Node => match node with
      | .structural (.forsTree _ _ idx) => idx.val
      | _ => 0) hsame
    exact Fin.ext (by simpa using hval)
  · rw [CanonicalCells.parentCell_tweakable cache secretSeed publicSeed]
    simp [StructuralNode.children, childBytes_ofFn, value, structuralValue,
      Hashing.tweakable, StructuralNode.address, Extraction.Fors.rootAddress]

end SlhDsaSecurity.ForsCharge
