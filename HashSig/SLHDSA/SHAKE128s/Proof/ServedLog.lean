/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ServedDisclosure
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalSignature

/-!
# What the signing log says the signer served

The carrier of the served requests is the game's own outcome: the log is part of it, and a log
entry carries everything the disclosed set needs — the request's framing and, in the signature
it returned, the randomiser the signer derived.

A served request is named by its **digest input**, not by its framing. That is what makes the
notion say what it should: an adversary that picks its own randomiser for a message the signer
signed names a different input, and names nothing the signer served. It also lets
`entry_of_servedLog` read the log entry back out of the input, pinning both the randomiser and
the framing through `Hashing.messageInput_injective`, with no collision bound anywhere.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServedLog

open Security

/-- The digest inputs the signer has served, read off the log: for each answered request, the
input its own signature's randomiser and its own framing name. -/
@[expose] def servedLog (pk : PublicKey) (result : (Outcome × Nat) × QueryCache HashSpec)
    (input : Bytes) : Prop :=
  ∃ entry ∈ result.1.1.signed, ∃ (framed : Bytes) (bytes : Bytes) (parsed : Signature),
    entry.1.frame = some framed ∧ entry.2 = some bytes ∧
      Signature.fromBytes? bytes = some parsed ∧
        input = Hashing.messageInput parsed.randomizer pk framed

/-- **A served input is a message-class input**, which is what the recorder's classes need of
it. -/
theorem isMessageInput_of_servedLog (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (input : Bytes)
    (hserved : servedLog pk result input) : CombinedCharge.IsMessageInput pk input := by
  obtain ⟨entry, -, framed, bytes, parsed, -, -, -, hinput⟩ := hserved
  exact ⟨parsed.randomizer, framed, hinput⟩

/-- **The log entry, read back out of the input it served.** Naming a served request by its
digest input pins both the randomiser the signer published and the message it signed, because
`Hashing.messageInput` is injective in each. This is the step the replay branch turns on. -/
theorem entry_of_servedLog (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (randomizer : Digest) (message : Bytes)
    (hserved : servedLog pk result (Hashing.messageInput randomizer pk message)) :
    ∃ entry ∈ result.1.1.signed, ∃ (bytes : Bytes) (parsed : Signature),
      entry.1.frame = some message ∧ entry.2 = some bytes ∧
        Signature.fromBytes? bytes = some parsed ∧ parsed.randomizer = randomizer := by
  obtain ⟨entry, hentry, framed, bytes, parsed, hframe, hanswer, hparsed, hinput⟩ := hserved
  obtain ⟨hrandomizer, -, hmessage⟩ := Hashing.messageInput_injective hinput
  subst hmessage
  exact ⟨entry, hentry, bytes, parsed, hframe, hanswer, hparsed, hrandomizer.symm⟩

open scoped Classical in
/-- The FORS positions the log's served requests disclose, read off the log. -/
@[expose] noncomputable def disclosedByLog (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (key : CanonicalGraph.ForsKey) :
    Finset (Fin (forsTrees * 2 ^ forsHeight)) :=
  Finset.univ.filter fun index =>
    ∃ (input : Bytes) (answer : HashOutput), servedLog pk result input ∧
      result.2 input = some answer ∧ SplitCharged.forsKeyOfDigest answer = key ∧
      ∃ tree : Fin forsTrees,
        GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree = index

/-- Membership in `disclosedByLog`: some served digest input caches an answer that selects the
position in that FORS key. -/
theorem mem_disclosedByLog (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (key : CanonicalGraph.ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) :
    index ∈ disclosedByLog pk result key ↔
      ∃ (input : Bytes) (answer : HashOutput), servedLog pk result input ∧
        result.2 input = some answer ∧ SplitCharged.forsKeyOfDigest answer = key ∧
        ∃ tree : Fin forsTrees,
          GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree = index := by
  classical
  rw [disclosedByLog, Finset.mem_filter]
  exact ⟨fun hmem => hmem.2, fun hwitness => ⟨Finset.mem_univ _, hwitness⟩⟩

end SlhDsaSecurity.ServedLog
