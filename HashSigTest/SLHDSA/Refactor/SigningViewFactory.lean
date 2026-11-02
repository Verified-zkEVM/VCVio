/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Factory

/-!
# Actual pure-view FIPS factory clients

The public key-generation equation compares the two existing pair presentations. The public
factory refinement covers the entire counted program for every original FIPS adversary,
including raw optional replies and the complete source vector, without a caller key premise.
-/

public section

open OracleComp OracleSpec SLHDSA SLHDSA.SHAKE128s SignatureAlg
open SLHDSA.SHAKE128s.Bridge.SharedExperiment

namespace SLHDSA.Refactor.SigningViewFactory

/-- The public presentation theorem applies to the actual FIPS key-generation program. -/
theorem keygenPresentation :
    (externalView FIPS205.scheme).keygen = FIPS205.internal.keygen :=
  externalView_fips205_keygen

/-- Every original FIPS adversary instantiates the complete counted factory equation. -/
theorem completeFactory (adversary : Game.Adversary FIPS205.Answer
    (PublicKeyCore FIPS205.core)) :
    SigningView.countedExperiment sourcePolicy
      (pureShakeView FIPS205.params FIPS205.deterministicRand ($ᵗ FIPS205.core.PkSeed))
      (externalMain adversary) = canonicalExperiment FIPS205.scheme adversary :=
  countedExperiment_pureShakeView_fips205 adversary

end SLHDSA.Refactor.SigningViewFactory
