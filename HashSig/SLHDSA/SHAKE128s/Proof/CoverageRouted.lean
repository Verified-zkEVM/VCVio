/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheAvailability
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitRouted
public import HashSig.SLHDSA.SHAKE128s.Proof.ServedLog

/-!
# The FORS branch's disclosed side, and the case it leaves open

`SplitRouted.signed_or_sensitive_of_secrets` sends each of the fourteen positions the forgery's
digest selects either to a sensitive claim or to membership of the disclosed set. This file
takes the second side to the event `CoverageTail` charges, and isolates exactly the case where
it cannot go there.

Membership of the disclosed set hands over a cached message-class input whose answer selects the
same position at the same FORS instance, and that is almost `CoverageTail.CoveredAt`. Three
reconciliations do the rest. A position determines the tree it sits in and the leaf inside it,
since the leaf is below `2 ^ forsHeight` and the position is `tree * 2 ^ forsHeight + leaf`, so a
witness at *some* tree is a witness at *that* tree. The FORS key a digest selects is its parsed
@[expose] instance, repackaged. And two message inputs are equal only when their randomiser, key and
message all are.

**The case that is left over.** `CoveredAt` asks for witnesses *other than the forgery's own*
message input, and the disclosed set does not supply that: the forgery's own digest query, if
the signer's randomiser made it, is itself a disclosing entry and it selects its own positions.
So whenever the only witness is the forgery's own input, the coverage event does not fire.

Under strong freshness that case is reachable — a forgery may repeat a signed message with the
signer's randomiser and change the signature elsewhere — and it is charged structurally rather
than by coverage. The disclosed set being the signer's own digests is what makes it so: the
witness being the forgery's input forces the forgery's randomiser to be the signer's, which is
the hypothesis `CanonicalSignature.eq_signInternal` needs to identify the forgery with the
signature a request returned.

`forgeryDisclosedCovered_or_only_self` is therefore stated as a fork rather than an implication,
with the leftover case named rather than assumed away.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.CoverageRouted

open Security CanonicalGraph

/-! ## A position names its tree and its leaf -/

/-- **A FORS position determines the tree it sits in and the leaf inside it.** -/
theorem forsIndex_inj {left right : SLHDSA.SHAKE128s.Fors.Indices}
    {treeLeft treeRight : Fin forsTrees}
    (hindex : GraphStakes.forsIndex left treeLeft = GraphStakes.forsIndex right treeRight) :
    treeLeft = treeRight ∧ left treeLeft = right treeRight := by
  have hval : treeLeft.val * 2 ^ forsHeight + (left treeLeft).val =
      treeRight.val * 2 ^ forsHeight + (right treeRight).val :=
    congrArg Fin.val hindex
  have hpow : (2 : Nat) ^ forsHeight = 4096 := by norm_num [forsHeight]
  have hvalues : treeLeft.val * 4096 + (left treeLeft).val =
      treeRight.val * 4096 + (right treeRight).val := by rw [← hpow]; exact hval
  have hleft : (left treeLeft).val < 4096 := by rw [← hpow]; exact (left treeLeft).isLt
  have hright : (right treeRight).val < 4096 := by rw [← hpow]; exact (right treeRight).isLt
  exact ⟨Fin.val_injective (by omega), Fin.val_injective (by omega)⟩

/-- **The FORS key a digest selects is its parsed instance.** -/
theorem parse_instance_eq_of_forsKeyOfDigest_eq {left right : HashOutput}
    (hkey : SplitCharged.forsKeyOfDigest left = SplitCharged.forsKeyOfDigest right) :
    (MessageDigest.parse left).1 = (MessageDigest.parse right).1 := by
  refine (CoverageTail.parse_instance_eq_iff left right).mpr ⟨?_, ?_⟩
  · exact BitVec.toFin_injective (congrArg ForsKey.tree hkey)
  · exact BitVec.toFin_injective (congrArg ForsKey.leaf hkey)

/-! ## Two message inputs that differ -/

/-! ## The coverage event -/

/-! ## Coverage by the digests that actually disclose

The witnesses this fork produces are not arbitrary message-class digests: each comes with
`ServedLog.servedLog`, because the disclosed set is read off the signing log. Keeping that is
what lets the coverage charge count the signer's own digests rather than every cached `H_msg`
answer — and the signer's are the requests it answered, capped by the signing limit, while the
others are not.

The notion is the log's, not the cache's: a digest discloses when the signer served the request
it belongs to, so an adversary that makes the `PRF_msg` query itself discloses nothing and there
is no fiction to charge. The narrow event implies the wide one, so a charge stated against
either applies. -/

/-- The digest `answer` has each of its fourteen FORS leaves also selected, at the same FORS
@[expose] instance, by a cached digest at a *disclosing* input other than the target. Which inputs
disclose is a parameter: the extraction reads it off the signing log, while the join that sends
the event into the two recordings reads it off the recorder's own test. -/
@[expose] def DisclosedCoveredBy (disclosing : Bytes → Prop) (cache : QueryCache HashSpec)
    (target : Bytes) (answer : HashOutput) : Prop :=
  ∀ tree : MessageDigest.ForsTree, ∃ (other : Bytes) (otherAnswer : HashOutput),
    other ≠ target ∧ disclosing other ∧ cache other = some otherAnswer ∧
      (MessageDigest.parse otherAnswer).1 = (MessageDigest.parse answer).1 ∧
      (MessageDigest.parse otherAnswer).2 tree = (MessageDigest.parse answer).2 tree

/-- **The coverage event at the forgery's own digest, counted on a disclosing class.** The
target is a digest that does *not* disclose: one that does is the replay case, which the split
sends elsewhere, and the charge counts targets outside the disclosing class. -/
@[expose] def ForgeryCoveredBy (disclosing : Bytes → Prop) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∃ (message : Bytes) (parsed : Signature) (answer : HashOutput),
    result.1.1.forgery.message.frame = some message ∧
      Signature.fromBytes? result.1.1.forgery.signature = some parsed ∧
        result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer ∧
          ¬ disclosing (Hashing.messageInput parsed.randomizer pk message) ∧
            DisclosedCoveredBy disclosing result.2
              (Hashing.messageInput parsed.randomizer pk message) answer

/-- **The coverage event at the forgery's own digest, counted on the served class.** -/
@[expose] def ForgeryDisclosedCovered (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ForgeryCoveredBy (ServedLog.servedLog pk result) pk result

/-- **The forgery's digest is covered by disclosing digests**, given a disclosing witness of its
own for every tree. -/
theorem forgeryDisclosedCovered_of_witnesses (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (message : Bytes) (parsed : Signature)
    (answer : HashOutput)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed)
    (hentry : result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer)
    (hfresh : ¬ ServedLog.servedLog pk result
      (Hashing.messageInput parsed.randomizer pk message))
    (hwitness : ∀ tree : MessageDigest.ForsTree,
      ∃ (other : Bytes) (otherAnswer : HashOutput),
        other ≠ Hashing.messageInput parsed.randomizer pk message ∧
          ServedLog.servedLog pk result other ∧
          result.2 other = some otherAnswer ∧
          SplitCharged.forsKeyOfDigest otherAnswer = SplitCharged.forsKeyOfDigest answer ∧
          MessageDigest.forsIndices otherAnswer tree = MessageDigest.forsIndices answer tree) :
    ForgeryDisclosedCovered pk result := by
  refine ⟨message, parsed, answer, hframe, hparsed, hentry, hfresh, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hsigner, hother, hkey, hleaf⟩ := hwitness tree
  exact ⟨other, otherAnswer, hne, hsigner, hother,
    parse_instance_eq_of_forsKeyOfDigest_eq hkey, hleaf⟩

/-- **The disclosed side goes to coverage, or the forgery is its own only witness.** The second
case is the one strong freshness permits: a forgery that repeats a signed message with the
signer's own randomiser shares its message input with the signature that disclosed the secrets,
and then there is no other input to cover it. -/
theorem forgeryDisclosedCovered_or_only_self (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (message : Bytes) (parsed : Signature)
    (answer : HashOutput)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed)
    (hentry : result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer)
    (hfresh : ¬ ServedLog.servedLog pk result
      (Hashing.messageInput parsed.randomizer pk message))
    (_hsigned : ∀ tree : MessageDigest.ForsTree,
      GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree ∈
        ServedLog.disclosedByLog pk result (SplitCharged.forsKeyOfDigest answer)) :
    ForgeryDisclosedCovered pk result ∨
      ∃ tree : MessageDigest.ForsTree, ∀ (input : Bytes) (a : HashOutput),
        ServedLog.servedLog pk result input → result.2 input = some a →
          SplitCharged.forsKeyOfDigest a = SplitCharged.forsKeyOfDigest answer →
            (∃ other : MessageDigest.ForsTree,
              GraphStakes.forsIndex (MessageDigest.forsIndices a) other =
                GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree) →
              input = Hashing.messageInput parsed.randomizer pk message := by
  classical
  by_cases hself : ∃ tree : MessageDigest.ForsTree, ∀ (input : Bytes) (a : HashOutput),
      ServedLog.servedLog pk result input → result.2 input = some a →
        SplitCharged.forsKeyOfDigest a = SplitCharged.forsKeyOfDigest answer →
          (∃ other : MessageDigest.ForsTree,
            GraphStakes.forsIndex (MessageDigest.forsIndices a) other =
              GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree) →
            input = Hashing.messageInput parsed.randomizer pk message
  · exact Or.inr hself
  refine Or.inl (forgeryDisclosedCovered_of_witnesses pk result message parsed answer
    hframe hparsed hentry hfresh fun tree => ?_)
  push Not at hself
  obtain ⟨input, a, hsigner, hcached, hkey, ⟨other, hother⟩, hne⟩ := hself tree
  obtain ⟨htree, hleaf⟩ := forsIndex_inj hother
  exact ⟨input, a, hne, hsigner, hcached, hkey, htree ▸ hleaf⟩

end SLHDSA.SHAKE128s.CoverageRouted
