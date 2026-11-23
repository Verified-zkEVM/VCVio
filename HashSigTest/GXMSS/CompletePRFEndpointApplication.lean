/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerivedUnforgeability

/-! # Complete PRF GXMSS public endpoint application

Only ordinary public imports supply the original three-family endpoint, its three projection
premises and the six named full-range interval hardness terms.
-/

public section

namespace GXMSS.CompletePRFEndpointApplicationTest

open GXMSS IncomparableEncoding GXMSS.Unforgeability GXMSS.IntervalMerkle
open GXMSS.Interval.Unforgeability GXMSS.Interval.Reductions.Chain
open SyncSignatureUnforgeability
open OracleComp OracleSpec TweakableHash ENNReal

/-- The expanded PRF bound keeps three response laws and the actual full-range strategies. -/
theorem expanded {Key PP T X H M R Response : Type} {h w v : ℕ}
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hnonmax : enc.NoMaximumOutput)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (hqueries : SigningQueryBound qs adv)
    (hseed : GXMSS.PRFDerived.Unforgeability.PublicSeedSamplingLaw hash p)
    (hstart : GXMSS.PRFDerived.Unforgeability.ChainStartSamplingLaw p)
    (hretry : GXMSS.PRFDerived.Unforgeability.RetrySamplingLaw p) :
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p K) ProbCompRuntime.probComp adv ≤
      prf.prfAdvantage (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p K adv) +
      (SM_DT_TCR_Advantage (merkleTargetCollisionAdversary hash enc K (Interval.full h) hv adv) +
        TargetCollisionResistance.advantage
          (GXMSS.Interval.Reductions.encodingTargetCollisionReduction
            hash enc qs K (Interval.full h) adv) +
        SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction hash enc K (Interval.full h) adv) +
        SM_DT_TCR_Advantage (chainCutTargetCollisionReduction hash enc K (Interval.full h) adv) +
        (↑((2 ^ h) * v * (2 ^ w - 1)) : ℝ≥0∞) *
          SM_DT_PRE_Advantage (chainPreimageReduction hash enc K (Interval.full h) hv hw adv) +
        (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage
            (chainUndetectabilityReduction hash enc K (Interval.full h) hv hw adv)) := by
  simpa only [GXMSS.PRFDerived.Unforgeability.strongUnforgeabilityBound,
    GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full, Nat.cast_pow, Nat.cast_ofNat]
    using GXMSS.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound
      hash enc prf p K qs hv hw hnonmax adv hqueries hseed hstart hretry

end GXMSS.CompletePRFEndpointApplicationTest
