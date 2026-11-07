/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.FullRange

/-!
# Original-domain interval security consumers

Ordinary imports expose the separate ten-term bound, its full-range returned-measure laws and
active-endpoint observation laws. The separate `DirectTrustAudit` covers the new main theorem
  origins.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Unforgeability
open GXMSS.Interval.Reductions.Chain GXMSS.Reductions
open GXMSS.Unforgeability
open SyncSignatureUnforgeability OracleComp OracleSpec TweakableHash Encoding

noncomputable example := @chainPreimageReduction
noncomputable example := @chainUndetectabilityReduction
example := @chainPreimageExperiment_full
example := @chainUndetectabilityExperiment_full
example := @chainPreimageAdvantage_full
example := @chainUndetectabilityAdvantage_full
example := @strongUnforgeabilityBound_full
example := @powerOfTwoStrongUnforgeabilityBound_full
example := @root_eq_of_active_endpoints_eq
example := @authPath_eq_of_active_endpoints_eq

example := @GXMSS.Interval.Unforgeability.merkleTargetCollisionExperiment_full
example := @GXMSS.Interval.Unforgeability.merkleTargetCollisionAdvantage_full
example := @GXMSS.Interval.Unforgeability.sameMessageRandomizerChainTargetCollisionExperiment_full
example := @GXMSS.Interval.Unforgeability.chainCutTargetCollisionExperiment_full
example := @GXMSS.Interval.Unforgeability.chainPreimageExperiment_full
example := @GXMSS.Interval.Unforgeability.chainUndetectabilityExperiment_full
example := @GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full
example := @GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full

example : GXMSS.Interval.activeChainPositionCount (Interval.full 0) 2 2 = 6 := by decide

example {PP T X H M R : Type} {h w v : ℕ}
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    strongAdvantage (GXMSS.Interval.scheme P enc K I) ProbCompRuntime.probComp A ≤
      strongUnforgeabilityBound P enc K qs I hv hw A :=
  strong_unforgeability_reduction_bound P enc K qs I hv hw htwo A hqueries
