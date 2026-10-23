/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsCoverage
public import HashSig.SLHDSA.SHAKE128s.Proof.MessageDigest
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalTarget
public import HashSig.SLHDSA.SHAKE128s.Proof.HashSeparation

/-!
# One combined answer-side charge

Charging the structural and FORS avenues separately costs `2 ^ -128 + 2 ^ -129` per query,
which together with the `2 ^ -128` of secret guessing exceeds the target rate `2 ^ -127`. The
two avenues are *mutually exclusive by input format*: a query whose bytes are an `H_msg` input
is not a structural query, so its answer cannot hit the honest cell of a node, and conversely a
structural query's answer is never read as a message digest.

So the two clauses are charged as one predicate, whose per-call probability is the **maximum**
of the two rates rather than their sum:

* on a message-class input the structural clause is dead, leaving `2 ^ -129`;
* on any other input the coverage clause is dead, leaving `2 ^ -128`.

Hence `2 ^ -128` overall, half the target, leaving the other half for the secret-guessing
avenue, which is the only one not of answer-side form.

The separation hypothesis is discharged by `HashSeparation`: an `H_msg` input can coincide with
a structural one only if `PK.seed ‖ PK.root` encodes a valid address, which has probability at
most `2 ^ -165` under actual key generation. `IsMessageInput` is the message class, and
`separated_of_not_possible` is the deterministic half of the separation.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CombinedCharge

open CanonicalGraph

/-- The byte inputs of the message class: those read as an `H_msg` call **under the real
public key**.

Pinning the key is not a convenience, it is required for soundness. With the key existentially
quantified an adversary could choose a `pk` whose `pk.seed ‖ pk.root` happens to encode a valid
address, craft a query that is simultaneously a message input and a structural one, and have
both clauses live at once — rate `3` on the answer side instead of `2`, which breaks the
budget. Pinning the key removes that: the only `H_msg` call that can produce a forgery is the
one the verifier makes, and the verifier uses the real key. A query under any other key is not
a message input, so the coverage clause is dead for it and only the structural clause is
charged. -/
def IsMessageInput (pk : PublicKey) (input : Bytes) : Prop :=
  ∃ (randomizer : Digest) (message : Bytes),
    input = Hashing.messageInput randomizer pk message

/-! ## Discharging the separation hypothesis

With the key pinned, `hseparated` is no longer an assumption. A structural input begins with
the real `PK.seed` and continues with an address; a message input begins with the randomizer
and continues with `PK.seed ‖ PK.root`. For one to be the other, `PK.seed ‖ PK.root` would have
to encode a valid address — `HashSeparation.Possible`, which
`HashSeparation.prob_possible_le` bounds by `2 ^ -165` for an independently uniform key pair.

The statement below is the deterministic half: given that the real key is *not* such a
coincidence, the separation holds outright, for every input and every cell assignment. -/

/-- **The separation hypothesis, discharged.** -/
theorem separated_of_not_possible (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    (input : Bytes) (hmessage : IsMessageInput pk input) :
    CanonicalTarget.canonicalTarget publicSeed cells input = none := by
  obtain ⟨randomizer, message, rfl⟩ := hmessage
  cases hparse : CanonicalGraph.parseInput publicSeed
      (Hashing.messageInput randomizer pk message) with
  | none => simp [CanonicalTarget.canonicalTarget, hparse]
  | some parsed =>
    exact absurd (CanonicalGraph.parseInput_sound hparse).symm
      (HashSeparation.message_tweakable_ne hpublic (hbounds parsed.parent))

end SlhDsaSecurity.CombinedCharge
