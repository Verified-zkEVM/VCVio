/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.FullRange.OriginalDomain

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

#check @chainPreimageReduction
#check @chainUndetectabilityReduction
#check @chainPreimageExperiment_full
#check @chainUndetectabilityExperiment_full
#check @chainPreimageAdvantage_full
#check @chainUndetectabilityAdvantage_full
#check @strongUnforgeabilityBound_full
#check @powerOfTwoStrongUnforgeabilityBound_full
#check @root_eq_of_active_endpoints_eq
#check @authPath_eq_of_active_endpoints_eq

#check GXMSS.Interval.Unforgeability.merkleTargetCollisionExperiment_full
#check GXMSS.Interval.Unforgeability.merkleTargetCollisionAdvantage_full
#check @GXMSS.Interval.Unforgeability.sameMessageRandomizerChainTargetCollisionExperiment_full
#check @GXMSS.Interval.Unforgeability.chainCutTargetCollisionExperiment_full
#check @GXMSS.Interval.Unforgeability.chainPreimageExperiment_full
#check @GXMSS.Interval.Unforgeability.chainUndetectabilityExperiment_full
#check @GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full
#check @GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full

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
  strong_unforgeability_reduction_bound_of_two_codewords P enc K qs I hv hw htwo A hqueries
