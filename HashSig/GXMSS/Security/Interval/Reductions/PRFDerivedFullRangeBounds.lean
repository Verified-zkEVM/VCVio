/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
import all HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedFullRange
import all HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedFullRange
public import HashSig.GXMSS.Security.Reductions.PRFDerivedOracleInteraction
import all HashSig.GXMSS.Security.Reductions.PRFDerivedOracleInteraction
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
public import HashSig.GXMSS.Security.Interval.Reductions.FullRange
import all HashSig.GXMSS.Security.Interval.Reductions.FullRange

/-!
# Full-range PRF bound expression

Actual query-domain advantage transport and original-domain algebra identify the relaxed
interval bound expression with the complete-tree displayed expression.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec Encoding GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory ENNReal
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Actual PRF domain renaming and original-domain algebra specialize the relaxed full-range
interval RHS without key or response projection sampling laws. -/
theorem fullRangeDisplayedBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfAdvantage (randgenPRFReduction hash enc p K (Interval.full h) adv) +
      GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound hash enc K qs
        (Interval.full h) hv hw adv =
      (restrictPRF prf).prfAdvantage
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv) +
        (TweakableHash.SM_DT_TCR_Advantage
          (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv) +
        Encoding.TargetCollisionResistance.advantage
          (GXMSS.Reductions.encodingTargetCollisionReduction hash enc qs K adv) +
        TweakableHash.SM_DT_TCR_Advantage
          (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K adv) +
        TweakableHash.SM_DT_TCR_Advantage
          (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K adv) +
        (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) *
          (((2 ^ w : ℕ) : ℝ≥0∞) * TweakableHash.SM_DT_UD_Advantage
            (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw adv) +
          TweakableHash.SM_DT_PRE_Advantage
            (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw adv))) := by
  rw [fullRangePRFAdvantage hash enc prf p K adv,
    GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full hash enc K qs hv hw adv]


end GXMSS.Interval.PRFDerived.Unforgeability
