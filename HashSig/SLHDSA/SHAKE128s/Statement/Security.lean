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
# Strong unforgeability of SLH-DSA

The adversary gets the public key, the random oracle and a signing oracle, and outputs a forgery.
It wins if the forgery verifies and was not returned by the signing oracle. Every hash call is
counted by its source: the adversary's own, key generation's, the signer's and the final
verification's; signing requests are counted too.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Security

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

def Counts.single (kind : QueryKind) (count : Nat) : Counts := Pi.single kind count

abbrev CountedRun := AddWriterT Counts (StateT SigningLog (OracleComp OracleWorld))

def hashCost : OracleWorld.Domain → Nat :=
  Xmss.RandomOracleModel.hashCost Bytes HashOutput

def countQueries {α : Type} (cost : OracleWorld.Domain → Counts)
    (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × Counts) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle cost) computation).run

/-- One unit for every hash call. -/
def countAllHashes {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle hashCost) computation).run

/-- Signs with the real key, counts each request and logs each answer. -/
def signingOracle (sk : SecretKey) : QueryImpl SigningSpec CountedRun := fun request => do
  AddWriterT.addTell (Counts.single .signing 1)
  let answer ← liftM (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))
  liftM (modify (fun signed => signed ++ [⟨request, answer⟩]) :
    StateT SigningLog (OracleComp OracleWorld) Unit)
  return answer

/-- The result of one run of the experiment. -/
abbrev Outcome := Game.Outcome

/-- The adversary's phase and the verification of its forgery. -/
noncomputable def afterKeygen (adversary : Adversary) (keys : SecretKey × PublicKey) :
    OracleComp OracleWorld Outcome := do
  let (sk, pk) := keys
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (Scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

/-- The forgery is new: no signing request returned this pair. -/
def Fresh (signed : SigningLog) (forgery : Forgery) : Prop :=
  ¬∃ entry ∈ signed, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

def Wins (outcome : Outcome) : Prop :=
  outcome.verified = true ∧ Fresh outcome.signed outcome.forgery

instance (signed : SigningLog) (forgery : Forgery) : Decidable (Fresh signed forgery) := by
  unfold Fresh; infer_instance

instance (outcome : Outcome) : Decidable (Wins outcome) := by
  unfold Wins; infer_instance

/-! ## Counting by source -/

/-- The counts by source; the signer's calls are what remains after key generation. -/
def sourceCounts (outcome : Outcome) (keygenHashes laterHashes : Nat) :
    Xmss.Unforgeability.QueryCounts
  | .sign => outcome.counts .signing
  | .hash => outcome.counts .hash
  | .keygen => keygenHashes
  | .signer => laterHashes - outcome.counts .hash - outcome.counts .verification
  | .verifier => outcome.counts .verification

noncomputable def experimentBySource (adversary : Adversary) :
    OracleComp OracleWorld (Outcome × Xmss.Unforgeability.QueryCounts) := do
  let (keys, keygenHashes) ← countAllHashes Scheme.keygen
  let (outcome, laterHashes) ← countAllHashes (afterKeygen adversary keys)
  return (outcome, sourceCounts outcome keygenHashes laterHashes)

/-- All parties share one random oracle, starting empty. -/
noncomputable def runBySource (adversary : Adversary) :
    ProbComp (Outcome × Xmss.Unforgeability.QueryCounts) :=
  Xmss.RandomOracleModel.run (experimentBySource adversary)

noncomputable def securityGame : Xmss.SecurityGame Unit Xmss.Unforgeability.QueryKind where
  Adversary := Adversary
  experiment := fun _ adversary =>
    (fun result => (decide (Wins result.1), result.2)) <$> runBySource adversary

/-! ## Bit security -/

/-- At most `2 ^ 64` signing requests, with probability one. -/
def WithinSigningLimit (adversary : Adversary) : Prop :=
  Pr{let result ← securityGame.experiment () adversary}[result.2 .sign ≤ signingLimit] = 1

/-- `bits` bits of security in counting mode `Z`, for adversaries within the signing limit. -/
def HasSecurityBits (Z : Finset Xmss.Unforgeability.QueryKind) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary, WithinSigningLimit adversary →
    securityGame.HasQueryBound () Z adversary q →
    securityGame.advantage () adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The adversary's work is the sum of:
- its signing requests (+1 per request, at most `2^64`),
- its hash calls (+1 per call it makes to the random oracle),
- the hash calls of verifying its forgery (+1 per call). -/
def adversaryWork : Finset Xmss.Unforgeability.QueryKind := {.sign, .hash, .verifier}

end SlhDsaSecurity.Security
