/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability

/-! # Complete GXMSS public endpoint application

The established public facade alone supplies the complete theorem, its named reductions and
all statement support for an ordinary consumer.
-/

public section

open GXMSS GXMSS.Encoding GXMSS.Unforgeability
open OracleComp OracleSpec TweakableHash ENNReal

example {PP T X H M R : Type} {h w v : ℕ}
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (hqueries : SigningQueryBound qs adv) :
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash enc K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv) +
        TargetCollisionResistance.advantage
          (GXMSS.Reductions.encodingTargetCollisionReduction hash enc qs K adv) +
        SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K adv) +
        SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K adv) +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) * SM_DT_UD_Advantage
              (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw adv) +
            SM_DT_PRE_Advantage
              (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw adv)) :=
  (GXMSS.Unforgeability.strong_unforgeability_reduction_bound
    hash enc K qs hv hw htwo adv) hqueries
