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

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
