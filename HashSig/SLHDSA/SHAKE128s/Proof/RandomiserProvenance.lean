/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.PhaseProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomiserCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.SigningFaithful

/-!
# The overlap of message inputs with `PRF_msg` inputs

A message input *is* a `PRF_msg` input, at its own randomiser read as the seed
(`RandomizerGate.messageInput_eq_randomizerInput`), so the signer's digest query and the
verifier's digest query each match a `PRF_msg` input at the real seed exactly when the randomiser
behind them is `SK.prf` itself. This file names the two halves of that overlap:

* `SignerHitsSeed` — the randomiser the signer derived for a request it served is the seed
  itself, stated at the cache entry the answer sits in.
* `forgeryDigestRecord` — the one input the forgery's own digest query names, which is one more
  guess at the seed and so costs one more element of the record.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RandomiserProvenance

open Security CacheReplay RecordedQueries CacheProvenance PhaseProvenance

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-- **The signer's coincidence.** The randomiser the signer derived for a request it served is
the seed itself.

Stated at the *cache entry* the answer sits in, not at `HonestProbes.replayRandomizer`, and the
difference matters: `replay` answers `default` at an absent input, so the predicate read through
`replayRandomizer` alone would also be satisfied by `Hashing.truncate default = SK.prf`, a
statement about a fixed constant that no per-run charge can pay for. The entry's presence comes
from the signing sub-run, through `PhaseProvenance.SignerMade`. -/
def SignerHitsSeed (prfSeed publicSeed : Digest) (cache : QueryCache HashSpec)
    (signed : SigningLog) : Prop :=
  ∃ entry ∈ signed, ∃ (framed : Bytes) (answer : HashOutput),
    entry.1.frame = some framed ∧
      cache (Hashing.randomizerInput prfSeed publicSeed framed) = some answer ∧
        Hashing.truncate answer = prfSeed

/-- The one input the forgery's own digest query names, when the forgery has one. The forgery's
randomiser being `SK.prf` is *exactly* this input being a `PRF_msg` input at the seed. -/
noncomputable def forgeryDigestRecord (pk : PublicKey) (forgery : Forgery) : Multiset Bytes :=
  match forgery.message.frame with
  | none => 0
  | some framed =>
    match Signature.fromBytes? forgery.signature with
    | none => 0
    | some parsed => {Hashing.messageInput parsed.randomizer pk framed}

/-- A parsed forgery's own digest input is in its digest record. -/
theorem mem_forgeryDigestRecord (pk : PublicKey) (forgery : Forgery) (framed : Bytes)
    (parsed : Signature) (hframe : forgery.message.frame = some framed)
    (hparsed : Signature.fromBytes? forgery.signature = some parsed) :
    Hashing.messageInput parsed.randomizer pk framed ∈ forgeryDigestRecord pk forgery := by
  simp only [forgeryDigestRecord, hframe, hparsed]
  simp

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail

end SlhDsaSecurity.RandomiserProvenance
