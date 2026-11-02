/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Requests
public import HashSig.SLHDSA.SHAKE128s.Statement.RandomOracleModel
public import HashSig.SLHDSA.SHAKE128s.Statement.UnforgeabilityGame
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# External signature game carriers and observations

Requests, algorithms, adversaries, raw optional replies, freshness and source-count projections
are independent of any concrete experiment interpreter.
-/

public section
open OracleComp OracleSpec
namespace SLHDSA.SHAKE128s.Game

/-- The world of the scheme: private uniform sampling and the shared hash oracle on byte strings. -/
abbrev World (Output : Type) := RandomOracleModel.World Bytes Output

/-- A pure-mode signature scheme over one hash oracle with answers in `Output`, public keys `PK`
and secret keys `SK`. Signatures and messages are byte strings; signing returns `none` when it
rejects the request. -/
structure ExternalScheme (Output PK SK : Type) where
  /-- Key generation. -/
  keygen : OracleComp (World Output) (SK × PK)
  /-- Signing of a request. -/
  sign : SK → Message → OracleComp (World Output) (Option Bytes)
  /-- Verification of a signature on a request. -/
  verify : PK → Message → Bytes → OracleComp (World Output) Bool

/-- The signing oracle's interface. -/
abbrev SigningSpec : OracleSpec Message := Message →ₒ Option Bytes

/-- The requests made of the signing oracle, with its answers. -/
abbrev SigningLog := QueryLog SigningSpec

/-- A claimed forgery: a request and a signature. -/
structure Forgery where
  /-- The request the forgery signs. -/
  message : Message
  /-- The forged signature. -/
  signature : Bytes
deriving DecidableEq

variable {Output PK SK : Type}

/-- An adversary: given the public key, the hash oracle and a signing oracle, it outputs a
forgery. -/
structure Adversary (Output PK : Type) where
  /-- The adversary's program. -/
  main : PK → OracleComp (World Output + SigningSpec) Forgery

/-- What the adversary's phase counts: its signing requests, its hash calls and verification's. -/
inductive QueryKind where
  /-- A request to the signing oracle. -/
  | signing
  /-- A hash call the adversary makes directly. -/
  | hash
  /-- A hash call of the verification of the forgery. -/
  | verification
deriving DecidableEq

/-- A count per kind. -/
abbrev Counts := QueryKind → Nat

/-- `count` queries of kind `kind`, and none of the others. -/
@[expose] def Counts.single (kind : QueryKind) (count : Nat) : Counts := Pi.single kind count

/-- The hash work of the adversary's phase: its own hash calls and those of verification. -/
@[expose] def Counts.work (counts : Counts) : Nat := counts .hash + counts .verification

/-- One unit per hash call; nothing per uniform sample. -/
@[expose] def hashCost : (World Output).Domain → Nat :=
  RandomOracleModel.hashCost Bytes Output

/-- The result of one run of the experiment. -/
structure Outcome where
  /-- The adversary's forgery. -/
  forgery : Forgery
  /-- The signing log. -/
  signed : SigningLog
  /-- Whether the forgery verifies. -/
  verified : Bool
  /-- The counts of the adversary's phase and of verification. -/
  counts : Counts

/-- The forgery is new: no signing request returned this pair. -/
@[expose] def Fresh (signed : SigningLog) (forgery : Forgery) : Prop :=
  ¬∃ entry ∈ signed, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

/-- The adversary wins: its forgery verifies and is new. -/
@[expose] def Wins (outcome : Outcome) : Prop :=
  outcome.verified = true ∧ Fresh outcome.signed outcome.forgery

/-- Freshness of a forgery is decidable. -/
instance (signed : SigningLog) (forgery : Forgery) : Decidable (Fresh signed forgery) := by
  unfold Fresh; infer_instance

/-- Winning is decidable. -/
instance (outcome : Outcome) : Decidable (Wins outcome) := by
  unfold Wins; infer_instance

/-- The counts by source; the signer's calls are what remains after key generation. -/
@[expose] def sourceCounts (outcome : Outcome) (keygenHashes laterHashes : Nat) :
    Unforgeability.QueryCounts
  | .sign => outcome.counts .signing
  | .hash => outcome.counts .hash
  | .keygen => keygenHashes
  | .signer => laterHashes - outcome.counts .hash - outcome.counts .verification
  | .verifier => outcome.counts .verification


end SLHDSA.SHAKE128s.Game
