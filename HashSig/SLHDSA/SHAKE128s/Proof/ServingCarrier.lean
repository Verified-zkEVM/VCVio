/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ServedDisclosure
public import HashSig.SLHDSA.SHAKE128s.Proof.HonestProbes
public import HashSig.SLHDSA.SHAKE128s.Proof.HandlerCarrier

/-!
# What a handler has to carry for disclosure to be served-indexed

The carrier (`HandlerCarrier.State`) is what a handler carries: a served multiset naming the
digest inputs the signer has served, a framing flag, and the cache the digests are read from.
This file re-exports its operations and defines `AgreesWithLog`, the statement that the carrier
served exactly what the signing log names.

**The flag carries the framing, not the request, and the set carries digest inputs, not
messages.** Indexing by the message would let an adversary choose its own randomiser for a
message the signer did sign and have its own digest's positions counted as disclosed. Indexing by
the *input* pins the randomiser and the message together through
`Hashing.messageInput_injective`, and the framing in the flag is what the recorder tests an input
against, so an input of the right shape for a *different* request is not filed.

**Filing happens at the query, not at the request.** The digest input is not known when the
request arrives — it depends on the randomiser the oracle has yet to answer — so the carrier
cannot be told it up front. What the handler can do is set the framing while it serves, and file
an input that matches that framing. `HandlerCarrier.FilesLeft` is that test, and it asks for no
freshness: a served request whose digest input was already cached is served all the same, and
leaving it unfiled would make the signer's own reads unavailable at the carrier. Nothing an
adversary can do files an input, because only the signing oracle sets the framing.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServingCarrier

open CanonicalGraph Security

/-! ## The type, declared below

The carrier's type and the operations on it live in `HandlerCarrier`, below `OpenCache`, because
the handler that has to carry them is below the files that state what is read off them. The
names are re-exported here. -/

/-- What a handler carries. -/
abbrev Carrier := HandlerCarrier.State

export HandlerCarrier (Served cacheOf Grows setFraming clearFraming file cacheAnswer
  grows_of_framing grows_setFraming grows_clearFraming grows_file grows_cacheAnswer
  FilesLeft not_filesLeft_of_clear framed_of_filesLeft)

/-! ## The carrier and the log must agree

The carrier's served multiset and the signing log are two objects, and the argument needs them
to be one. At the end of a run they are: every completed request is logged and nothing is in
flight. -/

/-- The digest inputs a signing log names, each read at the cache the randomiser is replayed
from. -/
@[expose] def logServed (sk : SecretKey) (cache : QueryCache HashSpec) (signed : SigningLog)
    (input : Bytes) : Prop :=
  ∃ entry ∈ signed, ∃ framed : Bytes, entry.1.frame = some framed ∧
    input = Hashing.messageInput (HonestProbes.replayRandomizer cache sk framed)
      sk.publicKey framed

/-- **What a run must leave true**: the carrier served exactly what the log names. -/
@[expose] def AgreesWithLog (sk : SecretKey) (signed : SigningLog) (state : Carrier) : Prop :=
  ∀ input : Bytes, Served state input ↔ logServed sk state.cache signed input

end SlhDsaSecurity.ServingCarrier
