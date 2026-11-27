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

export Game.Counted (SourceCounts sourceKind sourcePolicy externalView phaseCounts laterHashes
  externalMain canonicalExperiment legacyOutcome legacyObservation)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
