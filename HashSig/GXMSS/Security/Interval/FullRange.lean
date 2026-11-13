/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Unforgeability
public import HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction

/-!
# Full-range interval security bounds

The empty frontier contributes zero native UD/PRE advantage. The remaining six named interval
reductions retain their original domains and exact positive-position or relaxed coefficients.
-/

public section
namespace GXMSS.Interval.Unforgeability
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash
  GXMSS.Reductions GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
  GXMSS.IntervalMerkle SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

/-- Empty-frontier advantages vanish and the actual six interval strategies remain. -/
theorem strongUnforgeabilityBound_full
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    strongUnforgeabilityBound P enc K qs (Interval.full h) hv hw A =
      SM_DT_TCR_Advantage (merkleTargetCollisionAdversary P enc K (Interval.full h) hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction
          P enc qs K (Interval.full h) A) +
      SM_DT_TCR_Advantage
        (sameMessageRandomizerChainTargetCollisionReduction P enc K (Interval.full h) A) +
      SM_DT_TCR_Advantage (chainCutTargetCollisionReduction P enc K (Interval.full h) A) +
      (((2 ^ h) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) *
        SM_DT_PRE_Advantage (chainPreimageReduction P enc K (Interval.full h) hv hw A) +
      (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K (Interval.full h) hv hw A) := by
  unfold strongUnforgeabilityBound
  simp only [GXMSS.Interval.activeChainPositionCount_full,
    GXMSS.Interval.Filler.udAdvantage_full, GXMSS.Interval.Filler.preAdvantage_full, add_zero]
  push_cast
  ring

/-- Empty-frontier advantages vanish and the actual six interval strategies remain. -/
theorem powerOfTwoStrongUnforgeabilityBound_full
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    powerOfTwoStrongUnforgeabilityBound P enc K qs (Interval.full h) hv hw A =
      SM_DT_TCR_Advantage (merkleTargetCollisionAdversary P enc K (Interval.full h) hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction
          P enc qs K (Interval.full h) A) +
      SM_DT_TCR_Advantage
        (sameMessageRandomizerChainTargetCollisionReduction P enc K (Interval.full h) A) +
      SM_DT_TCR_Advantage (chainCutTargetCollisionReduction P enc K (Interval.full h) A) +
      (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) *
        (((2 ^ w : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K (Interval.full h) hv hw A) +
          SM_DT_PRE_Advantage (chainPreimageReduction P enc K (Interval.full h) hv hw A)) := by
  unfold powerOfTwoStrongUnforgeabilityBound
  simp only [Interval.length_full,
    GXMSS.Interval.Filler.udAdvantage_full, GXMSS.Interval.Filler.preAdvantage_full, add_zero]
  push_cast
  ring

end GXMSS.Interval.Unforgeability
