/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.RandomOracleModel
public import HashSig.SLHDSA.SHAKE128s.Statement.UnforgeabilityGame
public import HashSig.SLHDSA.SHAKE128s.Statement.BitSecurity
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# The strong unforgeability game of a pure-mode signature over one hash oracle

A signature scheme in pure mode signs requests made of a message and a context, and produces
byte-string signatures; every party shares one lazily sampled random oracle on byte strings,
whose answers have type `Output` (`ExternalScheme`).

The adversary gets the public key, the random oracle and a signing oracle, and outputs a forgery.
It wins if the forgery verifies and the signing oracle never returned that message and signature
(`Wins`). Every hash call is counted by its source: the adversary's own, key generation's, the
signer's and the final verification's; signing requests are counted too (`securityGame`).
`HasSecurityBits Z bits` says that every adversary within `2 ^ 64` signing requests and with at
most `q ≥ 1` counted queries of the kinds in `Z` wins with probability at most `q / 2 ^ bits`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-- A signing request: message and context. -/
structure Message where
  /-- The message. -/
  message : Bytes
  /-- The context string. -/
  context : Bytes
deriving DecidableEq

/-- At most `2 ^ 64` signatures per key. -/
def signingLimit : Nat := 2 ^ 64

namespace Game

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
  | signing | hash | verification
deriving DecidableEq

instance : Fintype QueryKind where
  elems := {.signing, .hash, .verification}
  complete := by intro kind; cases kind <;> decide

/-- A count per kind. -/
abbrev Counts := QueryKind → Nat

/-- `count` queries of kind `kind`, and none of the others. -/
def Counts.single (kind : QueryKind) (count : Nat) : Counts := Pi.single kind count

/-- The hash work of the adversary's phase: its own hash calls and those of verification. -/
def Counts.work (counts : Counts) : Nat := counts .hash + counts .verification

/-- The adversary's phase: counts, and the signing log, over the world. -/
abbrev CountedRun (Output : Type) :=
  AddWriterT Counts (StateT SigningLog (OracleComp (World Output)))

/-- One unit per hash call; nothing per uniform sample. -/
def hashCost : (World Output).Domain → Nat :=
  RandomOracleModel.hashCost Bytes Output

/-- Run a computation, and also return the sum of `cost` over its queries. -/
def countQueries {α : Type} (cost : (World Output).Domain → Counts)
    (computation : OracleComp (World Output) α) : OracleComp (World Output) (α × Counts) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle cost) computation).run

/-- Run a computation, and also return its number of hash calls. -/
def countAllHashes {α : Type} (computation : OracleComp (World Output) α) :
    OracleComp (World Output) (α × Nat) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle hashCost) computation).run

/-- Signs with the real key, counts each request and logs each answer. -/
def signingOracle (scheme : ExternalScheme Output PK SK) (sk : SK) :
    QueryImpl SigningSpec (CountedRun Output) := fun request => do
  AddWriterT.addTell (Counts.single .signing 1)
  let answer ← liftM (scheme.sign sk request : OracleComp (World Output) (Option Bytes))
  liftM (modify (fun signed => signed ++ [⟨request, answer⟩]) :
    StateT SigningLog (OracleComp (World Output)) Unit)
  return answer

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

/-- The adversary's phase and the verification of its forgery. -/
noncomputable def afterKeygen (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) :
    OracleComp (World Output) Outcome := do
  let (sk, pk) := keys
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift (World Output)
          (StateT SigningLog (OracleComp (World Output)))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle scheme sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

/-- The forgery is new: no signing request returned this pair. -/
def Fresh (signed : SigningLog) (forgery : Forgery) : Prop :=
  ¬∃ entry ∈ signed, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

/-- The adversary wins: its forgery verifies and is new. -/
def Wins (outcome : Outcome) : Prop :=
  outcome.verified = true ∧ Fresh outcome.signed outcome.forgery

instance (signed : SigningLog) (forgery : Forgery) : Decidable (Fresh signed forgery) := by
  unfold Fresh; infer_instance

instance (outcome : Outcome) : Decidable (Wins outcome) := by
  unfold Wins; infer_instance

/-- The counts by source; the signer's calls are what remains after key generation. -/
def sourceCounts (outcome : Outcome) (keygenHashes laterHashes : Nat) :
    Unforgeability.QueryCounts
  | .sign => outcome.counts .signing
  | .hash => outcome.counts .hash
  | .keygen => keygenHashes
  | .signer => laterHashes - outcome.counts .hash - outcome.counts .verification
  | .verifier => outcome.counts .verification

/-- Key generation, then the adversary's phase and verification, with the counts by source. -/
noncomputable def experimentBySource (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    OracleComp (World Output) (Outcome × Unforgeability.QueryCounts) := do
  let (keys, keygenHashes) ← countAllHashes scheme.keygen
  let (outcome, laterHashes) ← countAllHashes (afterKeygen scheme adversary keys)
  return (outcome, sourceCounts outcome keygenHashes laterHashes)

variable [SampleableType Output]

/-- All parties share one random oracle, starting empty. -/
noncomputable def runBySource (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    ProbComp (Outcome × Unforgeability.QueryCounts) :=
  RandomOracleModel.run (experimentBySource scheme adversary)

/-- The strong unforgeability game of `scheme`: the winning bit and the counts by source. -/
noncomputable def securityGame (scheme : ExternalScheme Output PK SK) :
    SecurityGame Unit Unforgeability.QueryKind where
  Adversary := Adversary Output PK
  experiment := fun _ adversary =>
    (fun result => (decide (Wins result.1), result.2)) <$> runBySource scheme adversary

/-- At most `2 ^ 64` signing requests, with probability one. -/
def WithinSigningLimit (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) : Prop :=
  Pr{let result ← (securityGame scheme).experiment () adversary}[result.2 .sign ≤ signingLimit] = 1

/-- `bits` bits of security in counting mode `Z`, for adversaries within the signing limit. -/
def HasSecurityBits (scheme : ExternalScheme Output PK SK)
    (Z : Finset Unforgeability.QueryKind) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary Output PK, WithinSigningLimit scheme adversary →
    (securityGame scheme).HasQueryBound () Z adversary q →
    (securityGame scheme).advantage () adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The adversary's work is the sum of:
- its signing requests (+1 per request, at most `2^64`),
- its hash calls (+1 per call it makes to the random oracle),
- the hash calls of verifying its forgery (+1 per call). -/
def adversaryWork : Finset Unforgeability.QueryKind := {.sign, .hash, .verifier}

end Game

end SlhDsaSecurity
