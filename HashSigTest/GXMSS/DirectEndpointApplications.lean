/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Unforgeability
public import HashSig.GXMSS.Security.Interval.Reductions.FullRange
public import HashSig.GXMSS.Security.Unforgeability
public import HashSigTest.GXMSS.CompleteEndpointApplication

/-! # Direct GXMSS public endpoint applications

Ordinary consumers state and apply the ten-term interval bound and both complete-tree
right-hand-side identities using the public API.
-/

public section

open GXMSS GXMSS.Encoding GXMSS.IntervalMerkle
open OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability ENNReal

variable {PP T X H M R : Type} {h w v : ℕ}

section

open GXMSS.Interval.Unforgeability
open GXMSS.Interval.Reductions.Chain GXMSS.Reductions GXMSS.Unforgeability GXMSS.Interval.Filler

example
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    strongAdvantage (GXMSS.Interval.scheme P enc K I) ProbCompRuntime.probComp A ≤
      SM_DT_TCR_Advantage (merkleTargetCollisionAdversary P enc K I hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction P enc K
          I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K I A) +
      ((GXMSS.Interval.activeChainPositionCount I w v : ℕ) : ℝ≥0∞) *
        SM_DT_PRE_Advantage (chainPreimageReduction P enc K I hv hw A) +
      ((GXMSS.Interval.activeChainPositionCount I w v : ℕ) : ℝ≥0∞) *
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A) +
      SM_DT_UD_Advantage (udAdversary P enc K I A .endpointVector) +
      SM_DT_PRE_Advantage (preAdversary P enc K I A .endpointVector) +
      SM_DT_UD_Advantage (udAdversary P enc K I A .childPair) +
      SM_DT_PRE_Advantage (preAdversary P enc K I A .childPair) := by
  simpa only [strongUnforgeabilityBound] using
    (GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound P enc K qs
      I hv hw htwo A hqueries)

example
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    strongUnforgeabilityBound P enc K qs (Interval.full h) hv hw A =
      SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction P enc K hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Reductions.encodingTargetCollisionReduction P enc qs K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction P enc K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction P enc K A) +
      (((2 ^ h) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) *
        SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction P enc K hv hw A) +
      (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction P enc K hv hw A) :=
  GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full P enc K qs hv hw A

example
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    powerOfTwoStrongUnforgeabilityBound P enc K qs (Interval.full h) hv hw A =
      SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction P enc K hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Reductions.encodingTargetCollisionReduction P enc qs K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction P enc K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction P enc K A) +
      (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) *
        (((2 ^ w : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction P enc K hv hw A) +
          SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction P enc K hv hw A)) :=
  GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full P enc K qs hv hw A

end
