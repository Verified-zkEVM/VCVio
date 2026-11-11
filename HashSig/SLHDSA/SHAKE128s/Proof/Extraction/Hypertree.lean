/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Merkle
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Wots
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-!
# Extraction from one hypertree layer

Recovering the canonical root of a single XMSS subtree from a forged layer signature
either reproduces, for the incoming message, the canonical WOTS signature and all nine
canonical authentication siblings, or exhibits a concrete collision at one of this
layer's own queried hash calls: a Merkle authentication-path collision, the WOTS
public-key compression collision, or a WOTS chain collision. This composes the Merkle
and WOTS extractions for a single layer; chaining all seven layers and discharging the
checksum-antichain argument is handled separately. No collision resistance is assumed. -/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Extraction.Hypertree

variable [HasQuery HashSpec Id]

/-- The WOTS key-pair address of leaf `l` in the subtree at `(layer, tree)`. -/
@[expose] def wotsAddress (layer tree : Nat) (l : SLHDSA.SHAKE128s.Hypertree.LeafIndex) : Address :=
  SLHDSA.SHAKE128s.Merkle.wotsAddress (SLHDSA.SHAKE128s.Hypertree.address layer tree) l.val

/-- A concrete collision inside one layer's verification: a Merkle authentication-path
collision, the WOTS compression collision, or a WOTS chain collision. Each witness
names a specific queried oracle input. -/
@[expose] def LayerCollision (secretSeed publicSeed message : Digest) (layer tree : Nat)
    (l : SLHDSA.SHAKE128s.Hypertree.LeafIndex) (xsig : XmssSignature) : Prop :=
  let address := SLHDSA.SHAKE128s.Hypertree.address layer tree
  let wa := wotsAddress layer tree l
  let nodes : Nat → Nat → Digest :=
    SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed address
  let combine : Nat → Nat → Digest → Digest → Digest := fun height nodeIndex left right =>
    Hashing.tweakable (m := Id) publicSeed
      (SLHDSA.SHAKE128s.Merkle.nodeAddress address height nodeIndex)
      (BinaryPath.pairBytes (left, right))
  let leaf : Digest :=
    SLHDSA.SHAKE128s.Wots.publicKeyFromSignature (m := Id) xsig.wots message publicSeed wa
  let canonicalWots : WotsSignature :=
    SLHDSA.SHAKE128s.Wots.sign (m := Id) message secretSeed publicSeed wa
  (∃ j < subtreeHeight,
      BinaryPath.Collision nodes combine l.val leaf (Merkle.siblings xsig) j) ∨
    Wots.CompressionCollision xsig.wots canonicalWots message publicSeed wa ∨
    ∃ i : Fin chains, ∃ offset < w - 1 - (Checksum.encode message i).val,
      Wots.ChainCollision publicSeed { wa with chainOrHeight := BitVec.ofNat 32 i.val }
        (Checksum.encode message i).val (xsig.wots i) (canonicalWots i) offset

/-- A forged layer signature recovering the canonical subtree root either equals, for
its incoming message, the canonical WOTS signature with all canonical authentication
siblings, or contains a concrete collision at one of this layer's hash calls. -/
theorem layer_canonical_or_collision (secretSeed publicSeed message : Digest) (layer tree : Nat)
    (l : SLHDSA.SHAKE128s.Hypertree.LeafIndex) (xsig : XmssSignature)
    (hcanon : SLHDSA.SHAKE128s.Merkle.publicKeyFromSignature (m := Id) l xsig message publicSeed
        (SLHDSA.SHAKE128s.Hypertree.address layer tree) =
      SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed
        (SLHDSA.SHAKE128s.Hypertree.address layer tree) subtreeHeight 0) :
    (xsig.wots = SLHDSA.SHAKE128s.Wots.sign (m := Id) message secretSeed publicSeed
        (wotsAddress layer tree l) ∧
      ∀ j, xsig.authentication j = SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed
        (SLHDSA.SHAKE128s.Hypertree.address layer tree) j.val
          (Nat.xor (l.val / 2 ^ j.val) 1)) ∨
    LayerCollision secretSeed publicSeed message layer tree l xsig := by
  have hmerkle := Extraction.Merkle.root_eq_canonical_or_collision secretSeed publicSeed message
    (SLHDSA.SHAKE128s.Hypertree.address layer tree) l xsig hcanon
  dsimp only at hmerkle
  rcases hmerkle with ⟨hleaf, hsiblings⟩ | hcollision
  · -- Merkle path is canonical; `node 0 l.val` is defeq to the honest WOTS public key.
    have hwotspk : SLHDSA.SHAKE128s.Wots.publicKeyFromSignature (m := Id) xsig.wots message
        publicSeed (wotsAddress layer tree l) =
        SLHDSA.SHAKE128s.Wots.publicKey (m := Id) secretSeed publicSeed
          (wotsAddress layer tree l) :=
      hleaf
    have hwots := Extraction.Wots.publicKey_eq_canonical_or_collision xsig.wots message
      secretSeed publicSeed (wotsAddress layer tree l) hwotspk
    dsimp only at hwots
    rcases hwots with hcanonWots | hcompression | hchain
    · exact Or.inl ⟨hcanonWots, hsiblings⟩
    · exact Or.inr (Or.inr (Or.inl hcompression))
    · exact Or.inr (Or.inr (Or.inr hchain))
  · exact Or.inr (Or.inl hcollision)

end SLHDSA.SHAKE128s.Extraction.Hypertree
