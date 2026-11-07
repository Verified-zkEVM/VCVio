/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
import all HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedFullRangeBounds
import all HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedFullRangeBounds
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedFullRange
import all HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedFullRange
public import HashSig.GXMSS.Security.Reductions.PRFDerivedOracleInteraction
import all HashSig.GXMSS.Security.Reductions.PRFDerivedOracleInteraction
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
public import HashSig.GXMSS.Security.PRFDerivedUnforgeability
import all HashSig.GXMSS.Security.PRFDerivedUnforgeability

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

/-- The full-range PRF advantage plus the relaxed original-domain interval bound. -/
@[expose] noncomputable def fullRangeStrongUnforgeabilityBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : ℝ≥0∞ :=
  prf.prfAdvantage (randgenPRFReduction hash enc p K (Interval.full h) adv) +
    GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound hash enc K qs
      (Interval.full h) hv hw adv

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
      fullRangeStrongUnforgeabilityBound hash enc prf p K qs hv hw adv := by
  classical
  unfold fullRangeStrongUnforgeabilityBound
  rw [show GXMSS.Interval.PRFDerived.scheme hash enc prf.eval p K
    (Interval.full h) = GXMSS.PRFDerived.scheme hash enc
      (restrictPRF prf).eval p.toComplete K from fullRangeSchemeCorrespondence hash enc prf p K,
    fullRangeDisplayedBound hash enc prf p K qs hv hw adv]
  simpa only [GXMSS.PRFDerived.Unforgeability.strongUnforgeabilityBound,
    GXMSS.Unforgeability.reductionBound, Nat.cast_pow, Nat.cast_ofNat] using
    GXMSS.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound hash enc (restrictPRF prf)
    p.toComplete K qs hv hw htwo adv hbound keyLaw hseed hstart hretry


end GXMSS.Interval.PRFDerived.Unforgeability
