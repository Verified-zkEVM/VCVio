/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.BinaryPath
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Merkle

/-!
# Collision extraction from XMSS verification

Extraction from the height-nine XMSS verifier. `root_eq_canonical_or_collision` shows that a
signature whose recovered root is the genuine subtree root either reproduces the genuine WOTS
public key and all nine authentication siblings, or exhibits a `BinaryPath.Collision` at a
concrete height of its authentication path.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Extraction.Merkle

variable [HasQuery HashSpec Id]

/-- The authentication siblings of an XMSS signature, padded with zero past the subtree height. -/
@[expose] def siblings (signature : XmssSignature) (height : Nat) : Digest :=
  if h : height < subtreeHeight then signature.authentication ⟨height, h⟩ else 0

set_option maxRecDepth 10000 in
-- `congr 1` on the nine-step verifier fold recurses past the default depth
/-- Reaching the genuine root with changed authentication data gives a collision
on this verifier path. Otherwise its recovered WOTS key and all nine siblings
are exactly the genuine values. -/
theorem root_eq_canonical_or_collision (secretSeed publicSeed message : Digest)
    (address : Address) (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (hroot : SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) index signature
      message publicSeed address = SlhDsaSecurity.Merkle.node (m := Id)
        secretSeed publicSeed address subtreeHeight 0) :
    let nodes : Nat → Nat → Digest :=
      SlhDsaSecurity.Merkle.node (m := Id) secretSeed publicSeed address
    let combine : Nat → Nat → Digest → Digest → Digest := fun height nodeIndex left right =>
      Hashing.tweakable (m := Id) publicSeed
        (SlhDsaSecurity.Merkle.nodeAddress address height nodeIndex)
        (BinaryPath.pairBytes (left, right))
    let leaf : Digest := Wots.publicKeyFromSignature (m := Id) signature.wots message publicSeed
      (SlhDsaSecurity.Merkle.wotsAddress address index.val)
    (leaf = nodes 0 index.val ∧ ∀ j, signature.authentication j =
      nodes j.val (Nat.xor (index.val / 2 ^ j.val) 1)) ∨
    ∃ j < subtreeHeight,
      BinaryPath.Collision nodes combine index.val leaf (siblings signature) j := by
  dsimp only
  let nodes : Nat → Nat → Digest :=
    SlhDsaSecurity.Merkle.node (m := Id) secretSeed publicSeed address
  let combine : Nat → Nat → Digest → Digest → Digest := fun height nodeIndex left right =>
    Hashing.tweakable (m := Id) publicSeed
      (SlhDsaSecurity.Merkle.nodeAddress address height nodeIndex)
      (BinaryPath.pairBytes (left, right))
  let leaf : Digest := Wots.publicKeyFromSignature (m := Id) signature.wots message publicSeed
    (SlhDsaSecurity.Merkle.wotsAddress address index.val)
  have hfold : BinaryPath.value combine index.val leaf (siblings signature) subtreeHeight =
      SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) index signature
        message publicSeed address := by
    rw [BinaryPath.value_eq_fold]
    simp only [SlhDsaSecurity.Merkle.publicKeyFromSignature, bind, Correctness.foldlM_id]
    congr 1
    funext current j
    simp only [siblings, dite_eq_left j.isLt, BinaryPath.ordered]
    split <;> rfl
  have hpath := BinaryPath.canonical_or_collision nodes combine (fun _ _ => rfl)
    index.val leaf (siblings signature) subtreeHeight (by
      rw [hfold, hroot, Nat.div_eq_of_lt index.isLt])
  rcases hpath with ⟨hleaf, hsiblings⟩ | hcollision
  · refine Or.inl ⟨hleaf, fun j => ?_⟩
    simpa only [siblings, dite_eq_left j.isLt] using hsiblings j.val j.isLt
  · exact Or.inr hcollision

end SlhDsaSecurity.Extraction.Merkle
