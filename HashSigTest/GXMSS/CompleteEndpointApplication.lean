/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability

/-! # Complete GXMSS public endpoint application

The ordinary security theorem module alone supplies the complete theorem, its named reductions and
all statement support for an ordinary consumer.
-/

public section

open GXMSS IncomparableEncoding GXMSS.Unforgeability GXMSS.IntervalMerkle
open GXMSS.Interval.Unforgeability GXMSS.Interval.Reductions.Chain
open SyncSignatureUnforgeability
open OracleComp OracleSpec TweakableHash ENNReal

/-- The expanded complete bound names the actual full-range interval strategies. -/
theorem expanded {PP T X H M R : Type} {h w v : ℕ}
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hnonmax : enc.NoMaximumOutput)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (hqueries : SigningQueryBound qs adv) :
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash enc K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage (merkleTargetCollisionAdversary hash enc K (Interval.full h) hv adv) +
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
            (chainUndetectabilityReduction hash enc K (Interval.full h) hv hw adv) :=
  (GXMSS.Unforgeability.strong_unforgeability_reduction_bound
    hash enc K qs hv hw hnonmax adv) hqueries
