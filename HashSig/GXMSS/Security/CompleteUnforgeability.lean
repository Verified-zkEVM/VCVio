/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.CompleteBounds
public import HashSig.GXMSS.Security.IntervalUnforgeability
public import HashSig.GXMSS.Security.Reductions.FullRange.OriginalDomain
import all HashSig.GXMSS.Security.Auxiliary.CompleteBounds
import all HashSig.GXMSS.Security.IntervalUnforgeability
import all HashSig.GXMSS.Security.Reductions.FullRange.OriginalDomain

/-!
# Complete-tree strong unforgeability

The full active interval specializes the original-domain interval reduction to the complete
scheme. Exact source-experiment and reduction-experiment transports retain the complete
separate-term bound.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash GXMSS.Interval.Unforgeability

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}
set_option maxHeartbeats 800000 in
-- Elaborating the six concrete reduction adversaries retains the complete endpoint's budget.
/-- The complete-tree separate-term bound follows from full-range interval security for a
global code containing two distinct words. -/
theorem strong_unforgeability_reduction_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) :
    StrongUnforgeabilityReductionBound hash enc K qs adv
      (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv)
      (GXMSS.Reductions.encodingTargetCollisionReduction hash enc qs K adv)
      (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K adv)
      (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K adv)
      (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw adv)
      (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw adv) := by
  intro hqueries
  have hbound := strong_unforgeability_power_of_two_reduction_bound_of_two_codewords
      hash enc K qs (GXMSS.IntervalMerkle.Interval.full h) hv hw htwo adv hqueries
  rw [GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full] at hbound
  simpa only [SyncSignatureUnforgeability.strongAdvantage,
    GXMSS.Interval.strongUnforgeableExp_full, GXMSS.Reductions.Epoch,
    GXMSS.Reductions.merkleTCRProblem, GXMSS.Reductions.chainTCRProblem,
    GXMSS.Reductions.encodingTCRProblem, GXMSS.Reductions.chainUDProblem,
    GXMSS.Reductions.chainPREProblem, Nat.cast_pow, Nat.cast_ofNat] using hbound

end

end GXMSS.Unforgeability
