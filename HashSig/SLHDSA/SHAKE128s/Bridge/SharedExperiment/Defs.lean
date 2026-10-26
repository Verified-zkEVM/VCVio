/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import HashSig.SLHDSA.SHAKE128s.Statement.Game

/-!
# Source policies for the shared signature experiment

The source vector observes every signing attempt and each ambient hash in its actual phase.
Private sampling is free. Instrumentation belongs to the shared counted experiment; an outer
handler and its cache interpret the complete program afterward.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The five source coordinates of the original signature game. -/
abbrev SourceCounts := Unforgeability.QueryCounts

/-- The original source coordinate for each ambient-query phase. -/
@[expose] def sourceKind : SigningView.Phase → Unforgeability.QueryKind
  | .keygen => .keygen
  | .adversary => .hash
  | .signer => .signer
  | .verification => .verifier

/-- Every hash costs one in its phase; every signing attempt costs one, including rejection. -/
@[expose] def sourcePolicy {Output : Type} :
    SigningView.Event (Game.World Output) Message → SourceCounts
  | .ambient phase input => Pi.single (sourceKind phase) (Game.hashCost input)
  | .signingAttempt _ => Pi.single .sign 1

/-- A signing view of the same external algorithms, with public/secret key-pair order. -/
@[expose] def externalView {Output PK SK : Type} (scheme : Game.ExternalScheme Output PK SK) :
    SigningView (OracleComp (Game.World Output)) Message PK SK Bytes (Option Bytes) where
  keygen := Prod.swap <$> scheme.keygen
  sign _ sk request := scheme.sign sk request
  verify := scheme.verify
  readback := id

/-- Recover the three original phase coordinates from the full source vector. -/
@[expose] def phaseCounts (cost : SourceCounts) : Game.Counts
  | .signing => cost .sign
  | .hash => cost .hash
  | .verification => cost .verifier

/-- The total hashes after key generation include direct, signer and verification calls. -/
@[expose] def laterHashes (cost : SourceCounts) : Nat :=
  cost .hash + cost .signer + cost .verifier

/-- Present the original adversary's final forgery as a message/signature pair. -/
@[expose] def externalMain {Output PK : Type} (adversary : Game.Adversary Output PK)
    (pk : PK) : OracleComp (Game.World Output + Game.SigningSpec) (Message × Bytes) :=
  (fun forgery => (forgery.message, forgery.signature)) <$> adversary.main pk

/-- The shared counted program for the same external algorithms and adversary. -/
@[expose] def canonicalExperiment {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    OracleComp (Game.World Output)
      (SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :=
  SigningView.countedExperiment sourcePolicy (externalView scheme) (externalMain adversary)

/-- Recover the original outcome, including its full raw log and three phase counters. -/
@[expose] def legacyOutcome
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    Game.Outcome :=
  { forgery := ⟨observed.forgery.1, observed.forgery.2⟩
    signed := observed.rawLog
    verified := observed.verified
    counts := phaseCounts observed.cost }

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
