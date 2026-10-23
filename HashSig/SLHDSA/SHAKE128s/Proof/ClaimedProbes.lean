/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GraphStakes
public import HashSig.SLHDSA.SHAKE128s.Proof.WotsResidueReduction
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitCharged

/-!
# Where the forgery's claimed chain values sit

`GraphStakes.claimedCandidates` records one candidate per cell the forgery claims, and for the
hypertree's WOTS values it needs to know *which* chain position each claimed value sits at. That
position is the digit the message that layer signs encodes on that chain, and
`WotsResidueReduction.forgedAt` names that message, so the position is a function of the
forgery.

One mismatch has to be absorbed. A digit lands in `Fin w`, while a chain-step node is indexed by
`Fin (w - 1)` — the endpoint has no step above it. So the position is **clamped**, and the clamp
is the identity exactly where it has to be: on the chain the residue names, the forged digit is
strictly below the digit that key reveals, hence strictly below `w - 1`.

Clamping is sound in the only direction that matters. The charge bounds the probability that
*some* entry of the record is sensitive, so a clamped entry on a chain the residue does not name
either fails to be sensitive and costs nothing, or is sensitive and is charged — which is what
the budget is for. What would be unsound is a record that misses the real claim, and that is the
direction the clamp cannot go.

Keeping the record indexed by every layer and chain, rather than only by the chain the residue
names, keeps its length a constant.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ClaimedProbes

open CanonicalGraph WotsResidueReduction

/-- A digit, clamped into the range a chain-step node is indexed by. -/
def clampStep (digit : Nat) : Fin (w - 1) :=
  ⟨min digit (w - 2), by simp only [w, winternitzBits]; omega⟩

/-- **Below the endpoint the clamp is the identity.** -/
theorem clampStep_val {digit : Nat} (hdigit : digit < w - 1) :
    (clampStep digit).val = digit := by
  simp only [clampStep, w, winternitzBits] at *
  omega

variable [HasQuery HashSpec Id]

/-- The position the forgery's chain value at the layer reached after `i` steps sits at. -/
def forgedStep (publicSeed : Digest) (remaining : Nat)
    (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (i : Nat)
    (chain : Fin chains) : Fin (w - 1) :=
  clampStep (Checksum.encode
    (forgedAt publicSeed remaining signatures layer tree leaf message i) chain).val

/-- **On the chain the residue names, the clamp changes nothing.** -/
theorem forgedStep_val (publicSeed : Digest) (remaining : Nat)
    (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (i : Nat)
    (chain : Fin chains) (bound : Nat) (hbound : bound ≤ w - 1)
    (hdigit : (Checksum.encode
      (forgedAt publicSeed remaining signatures layer tree leaf message i) chain).val < bound) :
    (forgedStep publicSeed remaining signatures layer tree leaf message i chain).val =
      (Checksum.encode
        (forgedAt publicSeed remaining signatures layer tree leaf message i) chain).val :=
  clampStep_val (by omega)

/-- The record's position function, read off the forgery: the hypertree runs from layer zero at
the subtree and leaf its digest selects, starting from the FORS public key it recovers. -/
def forgedSteps (publicSeed : Digest) (signature : Signature) (tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (forsKey : Digest) :
    Fin layers → Fin chains → Fin (w - 1) :=
  fun layer chain =>
    forgedStep publicSeed layers signature.hypertree 0 tree leaf forsKey layer.val chain

/-- **The claimed chain value really sits at the position the record names.** -/
theorem sensitive_forgedClaim (publicSeed : Digest) {State : Type}
    (revealed : WotsKey → Fin chains → Nat)
    (signedAt : State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (hrevealed : ∀ key chain, revealed key chain ≤ w - 1)
    (table : Cells) (state : State) (key : WotsKey) (chain : Fin chains)
    (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (i : Nat)
    (value : SensitiveQuery.Cell)
    (hdigit : (Checksum.encode
      (forgedAt publicSeed remaining signatures layer tree leaf message i) chain).val <
      revealed key chain)
    (hvalue : value = table (.structural (wotsPosition key chain
      (Checksum.encode
        (forgedAt publicSeed remaining signatures layer tree leaf message i) chain)))) :
    SensitiveQuery.Sensitive (GraphStakes.stakes publicSeed)
      (GraphStakes.unavailableAt revealed signedAt) table state
      (GraphStakes.inputOf publicSeed
        (GraphStakes.wotsHashNode key chain
          (forgedStep publicSeed remaining signatures layer tree leaf message i chain)) value) := by
  have hclamp := forgedStep_val publicSeed remaining signatures layer tree leaf message i chain
    (revealed key chain) (hrevealed key chain) hdigit
  refine GraphStakes.sensitive_wotsClaim publicSeed revealed signedAt table state key chain _
    value (by rw [hclamp]; exact hdigit) ?_
  refine hvalue.trans (congrArg (fun position : Fin w =>
    table (Node.structural (wotsPosition key chain position))) ?_)
  exact (Fin.val_injective hclamp).symm

/-! ## The record, read off the run

Everything `GraphStakes.claimedCandidates` needs is a function of the forgery and of the cache
the run ends with: the signature is parsed from the forgery's bytes, the digest is the one the
replayed verifier computes, and the digest selects the FORS key, the FORS indices, the subtree
and the leaf. The hypertree's own keys follow from the subtree and leaf by the same accumulators
the residue threads, so the record is determined rather than quantified. -/

/-- The WOTS key the forgery's path uses at a layer. -/
def forgedKey (tree : Fin (2 ^ (totalHeight - subtreeHeight)))
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (layer : Fin layers) : WotsKey :=
  ⟨⟨layer, ⟨treeAt tree.val layer.val,
      lt_of_le_of_lt (treeAt_le tree.val layer.val) tree.isLt⟩⟩,
    leafAt leaf tree.val layer.val⟩

/-- **The record the charge takes, as a function of the run's own result.** -/
def claimedCandidatesOf (publicSeed : Digest) (cache : QueryCache HashSpec) (pk : PublicKey)
    (message : Bytes) (parsed : Signature) : List Bytes :=
  GraphStakes.claimedCandidates publicSeed
    (SplitCharged.forsKeyOfDigest (VerifierProbes.digestOf cache pk message parsed))
    (MessageDigest.forsIndices (VerifierProbes.digestOf cache pk message parsed)) parsed
    (forgedKey (MessageDigest.treeIndex (VerifierProbes.digestOf cache pk message parsed)).toFin
      (MessageDigest.leafIndex (VerifierProbes.digestOf cache pk message parsed)).toFin)
    (forgedSteps publicSeed parsed
      (MessageDigest.treeIndex (VerifierProbes.digestOf cache pk message parsed)).toNat
      (MessageDigest.leafIndex (VerifierProbes.digestOf cache pk message parsed)).toFin
      (VerifierProbes.forsKeyOf cache pk message parsed))

end SlhDsaSecurity.ClaimedProbes
