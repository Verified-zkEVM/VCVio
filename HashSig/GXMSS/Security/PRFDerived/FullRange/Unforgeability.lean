/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
import all HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.PRFDerived.FullRange.DisplayedBound
import all HashSig.GXMSS.Security.PRFDerived.FullRange.DisplayedBound
public import HashSig.GXMSS.Security.PRFDerived.FullRange.Transport
import all HashSig.GXMSS.Security.PRFDerived.FullRange.Transport
public import HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction
import all HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction
public import HashSig.GXMSS.Security.PRFDerived.ResponseCache
import all HashSig.GXMSS.Security.PRFDerived.ResponseCache
public import HashSig.GXMSS.Security.PRFDerived.Unforgeability
import all HashSig.GXMSS.Security.PRFDerived.Unforgeability

/-!
# Full-range three-law PRF security

The complete three-projection-law theorem and independent full-range transports establish
the corresponding interval result without a filler projection premise.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec Encoding GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory ENNReal
variable {Key PP T X H M R Response : Type} {h w v : ℕ}
set_option maxHeartbeats 1600000 in
-- Elaborating the explicit complete reduction RHS exceeds the default heartbeat limit.
/-- Full-range interval strong security recovers the complete theorem with its original three
projection laws. No filler law is needed for the actual interval reduction or experiment. -/
theorem fullRangeStrongReductionBound
    [SampleableType Key] [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.Interval.PRFDerived.scheme hash enc prf.eval p K (Interval.full h))
      ProbCompRuntime.probComp adv ≤
      prf.prfAdvantage (randgenPRFReduction hash enc p K (Interval.full h) adv) +
        GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound hash enc K qs
          (Interval.full h) hv hw adv := by
  classical
  rw [show GXMSS.Interval.PRFDerived.scheme hash enc prf.eval p K
    (Interval.full h) = GXMSS.PRFDerived.scheme hash enc
      (restrictPRF prf).eval p.toComplete K from fullRangeSchemeCorrespondence hash enc prf p K,
    fullRangeDisplayedBound hash enc prf p K qs hv hw adv]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    GXMSS.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound hash enc (restrictPRF prf)
    p.toComplete K qs hv hw htwo adv hbound keyLaw hseed hstart hretry


end GXMSS.Interval.PRFDerived.Unforgeability
