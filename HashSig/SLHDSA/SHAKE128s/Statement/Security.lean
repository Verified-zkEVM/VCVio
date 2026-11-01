/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Scheme
public import HashSig.SLHDSA.SHAKE128s.Statement.UnforgeabilityGame
public import HashSig.SLHDSA.SHAKE128s.Statement.BitSecurity
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Strong unforgeability of SLH-DSA-SHAKE-128s

The strong unforgeability game of the SLH-DSA-SHAKE-128s scheme of `Statement/Scheme.lean`, over
the oracle world `OracleWorld`. The adversary gets the public key, the random oracle and a
signing oracle, and outputs a forgery. It wins if the forgery verifies and was not returned by
the signing oracle (`Wins`). Every hash call is counted by its source: the adversary's own, key
generation's, the signer's and the final verification's; signing requests are counted too
(`securityGame`). `HasSecurityBits Z bits` bounds the advantage of every adversary within the
signing limit and of at most `q ≥ 1` counted queries of the kinds in `Z` by `q / 2 ^ bits`.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.Security

/-- The paper algorithms with their actual key generation, request signer and verifier. -/
@[expose] noncomputable def externalScheme :
    Game.ExternalScheme HashOutput PublicKey SecretKey where
  keygen := Scheme.keygen
  sign := Scheme.sign
  verify := Scheme.verify

/-- The signing oracle's interface. -/
abbrev SigningSpec : OracleSpec Message := Game.SigningSpec

/-- The signing log. -/
abbrev SigningLog := Game.SigningLog

/-- A claimed forgery. -/
abbrev Forgery := Game.Forgery

/-- An adversary against SLH-DSA-SHAKE-128s. -/
abbrev Adversary := Game.Adversary HashOutput PublicKey

/-! ## The experiment -/

/-- What the adversary's phase counts: its signing requests, its hash calls and verification's. -/
abbrev QueryKind := Game.QueryKind

export Game (Counts)

/-- `count` queries of kind `kind`, and none of the others. -/
@[expose] def Counts.single (kind : QueryKind) (count : Nat) : Counts := Pi.single kind count

/-- The adversary's phase: counts, and the signing log, over the oracle world. -/
abbrev CountedRun := AddWriterT Counts (StateT SigningLog (OracleComp OracleWorld))

/-- One unit per hash call; nothing per uniform sample. -/
@[expose] def hashCost : OracleWorld.Domain → Nat :=
  RandomOracleModel.hashCost Bytes HashOutput

/-- The shared component observer with its original phase-count interface. -/
@[expose] def countQueries {α : Type} (cost : OracleWorld.Domain → Counts)
    (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × Counts) :=
  Game.countQueries cost computation

/-- The shared component observer for every actual hash call. -/
@[expose] def countAllHashes {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) := Game.countAllHashes computation

/-- The shared callback signer, presented through the paper proof's phase/log interface. -/
@[expose] def signingOracle (sk : SecretKey) : QueryImpl SigningSpec CountedRun :=
  fun request => Game.Counted.legacyRun
    (SignatureAlg.SigningView.countedSigningOracleUsing Game.Counted.phasePolicy
      (fun request => (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))) request)

/-- The result of one run of the experiment. -/
abbrev Outcome := Game.Outcome

/-- The shared supplied-key client and final verifier retain the paper phase observation. -/
@[expose] noncomputable def afterKeygen (adversary : Adversary) (keys : SecretKey × PublicKey) :
    OracleComp OracleWorld Outcome := Game.afterKeygen externalScheme adversary keys

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

/-! ## Counting by source -/

/-- The counts by source; the signer's calls are what remains after key generation. -/
@[expose] def sourceCounts (outcome : Outcome) (keygenHashes laterHashes : Nat) :
    Unforgeability.QueryCounts
  | .sign => outcome.counts .signing
  | .hash => outcome.counts .hash
  | .keygen => keygenHashes
  | .signer => laterHashes - outcome.counts .hash - outcome.counts .verification
  | .verifier => outcome.counts .verification

/-- The shared counted experiment, projected to the paper outcome and all five source counts. -/
@[expose] noncomputable def experimentBySource (adversary : Adversary) :
    OracleComp OracleWorld (Outcome × Unforgeability.QueryCounts) :=
  Game.experimentBySource externalScheme adversary

/-- All parties share one random oracle, starting empty. -/
@[expose] noncomputable def runBySource (adversary : Adversary) :
    ProbComp (Outcome × Unforgeability.QueryCounts) :=
  RandomOracleModel.run (experimentBySource adversary)

/-- The strong unforgeability game of SLH-DSA-SHAKE-128s: the winning bit and the counts by
source. -/
@[expose] noncomputable def securityGame : SecurityGame Unit Unforgeability.QueryKind where
  Adversary := Adversary
  experiment := fun _ adversary =>
    (fun result => (decide (Wins result.1), result.2)) <$> runBySource adversary

/-! ## Bit security -/

/-- At most `2 ^ 64` signing requests, with probability one. -/
@[expose] def WithinSigningLimit (adversary : Adversary) : Prop :=
  Pr{let result ← securityGame.experiment () adversary}[result.2 .sign ≤ signingLimit] = 1

/-- `bits` bits of security in counting mode `Z`, for adversaries within the signing limit. -/
@[expose] def HasSecurityBits (Z : Finset Unforgeability.QueryKind) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary, WithinSigningLimit adversary →
    securityGame.HasQueryBound () Z adversary q →
    securityGame.advantage () adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The adversary's work is the sum of:
- its signing requests (+1 per request, at most `2^64`),
- its hash calls (+1 per call it makes to the random oracle),
- the hash calls of verifying its forgery (+1 per call). -/
@[expose] def adversaryWork : Finset Unforgeability.QueryKind := {.sign, .hash, .verifier}

end SLHDSA.SHAKE128s.Security
