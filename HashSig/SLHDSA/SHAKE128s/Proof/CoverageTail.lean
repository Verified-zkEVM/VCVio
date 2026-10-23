/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.DigestTape
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedCharges

/-!
# The FORS coverage event at the warmed tail

The coverage event: one recorded `H_msg`-class answer has its fourteen FORS leaves disclosed by
the other recorded answers. This file defines it (`CoveredAt`) and supplies the two facts about
the walk that let it be charged at the game.

* **The coordinates are the game's.** `parse_instance_eq_iff` checks that the FORS instance the
  event names packs exactly the tree and leaf indices `Scheme.forsAddress` is built from, so
  the event is the FORS branch's event rather than a near neighbour of it.
* **The freshness.** The walk programs only canonical inputs
  (`WarmedCharges.walk_cache_canonical`), and a canonical input is not a message input
  (`WarmedCharges.not_messageInput_canonical`), so `walk_cache_fresh` says no `H_msg` entry
  predates the tail. Every `H_msg` answer in the final cache was therefore drawn during the
  tail.

The event is a statement about *disclosure*: the covering digests are themselves cached answers
at message-class inputs, so the honest FORS secrets at the forgery's fourteen positions are
secrets some other message digest also selects. That is weaker than the FORS branch's conclusion
that the forgery *holds* those secrets, which a run could also reach by querying the
secret-bearing `PRF` input directly — an input-side event, charged elsewhere.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CoverageTail

open Security CanonicalGraph WarmedGame

/-! `afterSeeds` is the whole game after key generation's seeds are drawn. Nothing below takes
it apart, and left reducible it turns a defeq check between syntactically identical terms into
a full unfolding of the game. -/

attribute [local irreducible] WarmedGame.afterSeeds Scheme.keygenInternal Scheme.verify
  Scheme.sign Security.signingOracle Security.countQueries

/-! ## The event -/

/-- The digest `answer` has each of its fourteen FORS leaves also selected, at the same FORS
instance, by the digest cached at some *other* message-class input. -/
def CoveredAt (pk : PublicKey) (cache : QueryCache HashSpec) (target : Bytes)
    (answer : HashOutput) : Prop :=
  ∀ tree : MessageDigest.ForsTree, ∃ (other : Bytes) (otherAnswer : HashOutput),
    other ≠ target ∧ CombinedCharge.IsMessageInput pk other ∧
      cache other = some otherAnswer ∧
      (MessageDigest.parse otherAnswer).1 = (MessageDigest.parse answer).1 ∧
      (MessageDigest.parse otherAnswer).2 tree = (MessageDigest.parse answer).2 tree

/-! ## The coordinates are the game's

`CoveredAt` names a FORS position by the parsed digest's instance and its leaf at one tree.
Those are the same two coordinates the game names: the instance packs the tree and leaf
indices `Scheme.forsAddress` is built from, and the leaf at a tree is literally the digit
`Extraction.Fors.leafIndex` reads. Checking this is what makes the event the FORS branch's
event rather than a near neighbour of it. -/

/-- The parsed FORS instance is the packed pair of tree and leaf indices. -/
theorem parse_instance_eq_iff (left right : HashOutput) :
    (MessageDigest.parse left).1 = (MessageDigest.parse right).1 ↔
      (MessageDigest.treeIndex left = MessageDigest.treeIndex right ∧
        MessageDigest.leafIndex left = MessageDigest.leafIndex right) := by
  constructor
  · intro h
    have happend : MessageDigest.treeIndex left ++ MessageDigest.leafIndex left =
        MessageDigest.treeIndex right ++ MessageDigest.leafIndex right :=
      BitVec.toFin_injective h
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_getLsbD_eq
      intro bit _
      have hb : (MessageDigest.treeIndex left ++ MessageDigest.leafIndex left).getLsbD
            (bit + subtreeHeight) =
          (MessageDigest.treeIndex right ++ MessageDigest.leafIndex right).getLsbD
            (bit + subtreeHeight) := by rw [happend]
      rw [BitVec.getLsbD_append, BitVec.getLsbD_append,
        ite_eq_right (Nat.not_lt.mpr (Nat.le_add_left subtreeHeight bit)),
        ite_eq_right (Nat.not_lt.mpr (Nat.le_add_left subtreeHeight bit)),
        Nat.add_sub_cancel] at hb
      exact hb
    · apply BitVec.eq_of_getLsbD_eq
      intro bit hbit
      have hb : (MessageDigest.treeIndex left ++ MessageDigest.leafIndex left).getLsbD bit =
          (MessageDigest.treeIndex right ++ MessageDigest.leafIndex right).getLsbD bit := by
        rw [happend]
      rw [BitVec.getLsbD_append, BitVec.getLsbD_append, ite_eq_left hbit, ite_eq_left hbit] at hb
      exact hb
  · rintro ⟨htree, hleaf⟩
    unfold MessageDigest.parse
    rw [htree, hleaf]

/-! ## No message input predates the tail

The walk programs the canonical graph and nothing else, and a canonical input is a tweakable
input, which is a different byte format from an `H_msg` input unless `PK.seed ‖ PK.root`
happens to encode a valid address. That coincidence is `HashSeparation.Possible`, assumed away
here exactly as the combined charge assumes it away. -/

/-- The walk's cache holds no message-class entry. -/
theorem walk_cache_fresh (pk : PublicKey)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (input : Bytes)
    (hmessage : CombinedCharge.IsMessageInput pk input) : walk.2 input = none := by
  by_contra hpresent
  obtain ⟨parent, rfl⟩ := WarmedCharges.walk_cache_canonical hwalk input hpresent
  exact WarmedCharges.not_messageInput_canonical walk.1.1.2.2 walk.1.2 pk hpublic hbounds
    parent hmessage

end SlhDsaSecurity.CoverageTail
