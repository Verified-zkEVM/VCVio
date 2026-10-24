/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FaultCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.WotsPreimage

/-!
# What the WOTS residue leaves the forgery holding

`FaultCharge.WotsResidue` is what a hypertree fault comes to once its collisions are charged: at
some layer the forgery's WOTS signature is the *honest* signature of a message differing from the
honest input threaded into that layer. This file extracts the deterministic consequence.

The simplification that makes it short is that the hypertree's disclosures are not adaptive. Each
WOTS key of the hypertree signs exactly one message, and that message is a deterministic function
of the key — the honest node one layer down — so the `expectedInput` the recursion threads *is*
what that key revealed. `Checksum.exists_decreased_digit` then produces a chain whose forged digit
is strictly below the revealed one, and `Extraction.WotsPreimage.sign_eq_chain` says the signature
component there is the honest chain started from the honest secret and stopped at that digit. The
forgery therefore holds a value on that chain strictly earlier than anything the signature
disclosed.

`HoldsEarlyChainValue` records this with the same recursion as `WotsResidue`, so the address is
the address of the layer the recursion has reached, the secret is derived from `secretSeed` at
that address, and the disclosed position is the digit of the message that key signed. Nothing is
existentially quantified except the chain index, and that is pinned by the equation it appears in.

Two readings follow. `exists_held_value_of_residue` names the layer explicitly, through
accumulators that follow the recursion step for step, and names the message that layer signs
rather than quantifying it: the witness the recursion produces *is* `forgedAt`, which is what
lets the position a claimed chain value sits at be computed from the forgery.
`heldValue_eq_cell` reads the held value as a cell of the canonical graph, which is the
vocabulary the charge indexes by: the forgery holds
`wotsPosition key chainIndex (Checksum.encode forged chainIndex)`, a node strictly below the one
the honest signature revealed.

What that possession costs is a probabilistic question about the adversary's execution, charged
in `WotsCharge`; this file is the deterministic half.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.WotsResidueReduction

open Extraction CanonicalGraph

variable [HasQuery HashSpec Id]

/-- The value a forgery holds on one chain of one layer's WOTS key: the honest chain, started
from the honest secret at that key's address and advanced only as far as the forged digit. -/
@[expose] def heldValue (secretSeed publicSeed : Digest) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (forged : Digest) (chainIndex : Fin chains) :
    Digest :=
  SlhDsaSecurity.Wots.chain (m := Id) publicSeed
    (WotsPreimage.chainAddress (Extraction.Hypertree.wotsAddress layer tree leaf) chainIndex)
    0 (Checksum.encode forged chainIndex).val
    (Hashing.derive (m := Id) publicSeed secretSeed
      (SlhDsaSecurity.Wots.secretAddress (Extraction.Hypertree.wotsAddress layer tree leaf)
        chainIndex))

/-- At some layer the forgery holds a chain value strictly below the position that layer's key
disclosed. The recursion is `FaultCharge.WotsResidue`'s own, so the address is the address of
the layer the recursion has reached, the secret is derived from `secretSeed` at that address,
and the disclosed position is the digit of the message that key actually signed. -/
@[expose] def HoldsEarlyChainValue (secretSeed publicSeed : Digest) :
    (remaining : Nat) → (Fin remaining → XmssSignature) → (layer tree : Nat) →
      SlhDsaSecurity.Hypertree.LeafIndex → (message expectedInput : Digest) → Prop
  | 0, _, _, _, _, _, _ => False
  | remaining + 1, signatures, layer, tree, leaf, message, expectedInput =>
    (∃ chainIndex : Fin chains,
      (signatures 0).wots chainIndex =
          heldValue secretSeed publicSeed layer tree leaf message chainIndex ∧
        (Checksum.encode message chainIndex).val <
          (Checksum.encode expectedInput chainIndex).val) ∨
    HoldsEarlyChainValue secretSeed publicSeed remaining (fun i => signatures i.succ) (layer + 1)
      (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0) message
        publicSeed (SlhDsaSecurity.Hypertree.address layer tree))
      (Extraction.HypertreeChain.honestNode secretSeed publicSeed layer tree)

/-- **The WOTS residue puts the forgery in possession of an undisclosed chain value.** -/
theorem holds_early_chain_value_of_residue (secretSeed publicSeed : Digest) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message expectedInput : Digest),
      FaultCharge.WotsResidue secretSeed publicSeed remaining signatures layer tree leaf
          message expectedInput →
        HoldsEarlyChainValue secretSeed publicSeed remaining signatures layer tree leaf
          message expectedInput := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _ hresidue; exact hresidue.elim
  | succ remaining ih =>
    intro signatures layer tree leaf message expectedInput hresidue
    unfold FaultCharge.WotsResidue at hresidue
    rcases hresidue with ⟨hwots, hne⟩ | hrest
    · refine Or.inl ?_
      obtain ⟨chainIndex, hdigit⟩ := Checksum.exists_decreased_digit (Ne.symm hne)
      refine ⟨chainIndex, ?_, hdigit⟩
      rw [congrFun hwots chainIndex]
      exact WotsPreimage.sign_eq_chain message secretSeed publicSeed
        (Extraction.Hypertree.wotsAddress layer tree leaf) chainIndex
    · exact Or.inr (ih _ _ _ _ _ _ hrest)

/-! ## Naming the layer the residue reaches

The recursion above is faithful but implicit about *which* layer it stopped at. These five
accumulators follow the step exactly — each is the previous one applied to the arguments the
recursion passes on — so flattening the predicate to an explicit layer index is definitional.
Their closed forms are recorded below for the two cases a caller needs: the layer rises by one
per step, and the tree index only shrinks, which is what bounds the coordinates. -/

/-- The layer the recursion has reached after `i` steps. -/
@[expose] def layerAt (layer : Nat) : Nat → Nat
  | 0 => layer
  | i + 1 => layerAt (layer + 1) i

/-- The subtree index the recursion has reached after `i` steps. -/
@[expose] def treeAt (tree : Nat) : Nat → Nat
  | 0 => tree
  | i + 1 => treeAt (tree / 2 ^ subtreeHeight) i

/-- The leaf the recursion has reached after `i` steps. -/
@[expose] def leafAt (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (tree : Nat) :
    Nat → SlhDsaSecurity.Hypertree.LeafIndex
  | 0 => leaf
  | i + 1 => leafAt (SlhDsaSecurity.Hypertree.nextLeaf tree) (tree / 2 ^ subtreeHeight) i

/-- The message the honest key at the layer reached after `i` steps actually signed. Each WOTS
key of the hypertree signs exactly one message, and that message is the honest node one layer
down, so this is a function of the seeds alone. -/
@[expose] def revealedAt (secretSeed publicSeed expectedInput : Digest) (layer tree : Nat) :
    Nat → Digest
  | 0 => expectedInput
  | i + 1 => revealedAt secretSeed publicSeed
      (Extraction.HypertreeChain.honestNode secretSeed publicSeed layer tree) (layer + 1)
      (tree / 2 ^ subtreeHeight) i

/-- The message the forgery's key at the layer reached after `i` steps signs: the root its own
lower layers recover. Unlike `revealedAt` this follows the forgery rather than the seeds, and it
is the accumulator the residue's recursion threads — which is what lets the position a claimed
chain value sits at be named rather than quantified. -/
@[expose] def forgedAt (publicSeed : Digest) :
    (remaining : Nat) → (Fin remaining → XmssSignature) → (layer tree : Nat) →
      SlhDsaSecurity.Hypertree.LeafIndex → Digest → Nat → Digest
  | 0, _, _, _, _, message, _ => message
  | _ + 1, _, _, _, _, message, 0 => message
  | remaining + 1, signatures, layer, tree, leaf, message, i + 1 =>
      forgedAt publicSeed remaining (fun j => signatures j.succ) (layer + 1)
        (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
        (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0) message
          publicSeed (SlhDsaSecurity.Hypertree.address layer tree)) i

omit [HasQuery HashSpec Id] in
/-- The layer rises by one per step. -/
theorem layerAt_eq (layer : Nat) : ∀ i : Nat, layerAt layer i = layer + i := by
  intro i
  induction i generalizing layer with
  | zero => rfl
  | succ i ih => rw [layerAt, ih (layer + 1)]; omega

omit [HasQuery HashSpec Id] in
/-- The subtree index only shrinks along the recursion. -/
theorem treeAt_le (tree : Nat) : ∀ i : Nat, treeAt tree i ≤ tree := by
  intro i
  induction i generalizing tree with
  | zero => exact Nat.le_refl tree
  | succ i ih => exact (ih (tree / 2 ^ subtreeHeight)).trans (Nat.div_le_self _ _)

/-- **The residue, read at an explicit layer.** -/
theorem exists_held_value_of_residue (secretSeed publicSeed : Digest) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message expectedInput : Digest),
      HoldsEarlyChainValue secretSeed publicSeed remaining signatures layer tree leaf message
          expectedInput →
        ∃ (i : Fin remaining) (chainIndex : Fin chains),
          (signatures i).wots chainIndex =
              heldValue secretSeed publicSeed (layerAt layer i.val) (treeAt tree i.val)
                (leafAt leaf tree i.val)
                (forgedAt publicSeed remaining signatures layer tree leaf message i.val)
                chainIndex ∧
            (Checksum.encode
              (forgedAt publicSeed remaining signatures layer tree leaf message i.val)
              chainIndex).val <
              (Checksum.encode
                (revealedAt secretSeed publicSeed expectedInput layer tree i.val)
                chainIndex).val := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _ hholds; exact hholds.elim
  | succ remaining ih =>
    intro signatures layer tree leaf message expectedInput hholds
    rcases hholds with ⟨chainIndex, hvalue, hdigit⟩ | hrest
    · exact ⟨0, chainIndex, hvalue, hdigit⟩
    · obtain ⟨i, chainIndex, hvalue, hdigit⟩ := ih _ _ _ _ _ _ hrest
      exact ⟨i.succ, chainIndex, hvalue, hdigit⟩

/-! ## The held value is a canonical cell

Read at a bounded layer, the key the residue names is a `CanonicalGraph.WotsKey`, and the value
the forgery holds is that key's cell at the chain position the forged digit stops at — a cell
strictly below the one the honest signature disclosed, and therefore one no signature ever
revealed. This is the vocabulary `WotsCharge` indexes by. -/

/-- The held value is the canonical graph's cell at that chain position. -/
theorem heldValue_eq_cell (secretSeed publicSeed : Digest) (location : Tree)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (forged : Digest) (chainIndex : Fin chains) :
    heldValue secretSeed publicSeed location.layer.val location.tree.val leaf forged chainIndex =
      value secretSeed publicSeed
        (.structural (wotsPosition ⟨location, leaf⟩ chainIndex
          (Checksum.encode forged chainIndex))) :=
  (value_wotsPosition secretSeed publicSeed ⟨location, leaf⟩ chainIndex
    (Checksum.encode forged chainIndex)).symm

end SlhDsaSecurity.WotsResidueReduction
