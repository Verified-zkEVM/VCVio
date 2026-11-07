/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.MerkleCollisionBound
public import HashSig.GXMSS.Security.Interval.Unforgeability
public import HashSig.GXMSS.Security.Interval.Reductions.FullRange
import all HashSig.GXMSS.Security.Reductions.MerkleCollisionBound
import all HashSig.GXMSS.Security.Interval.Unforgeability
import all HashSig.GXMSS.Security.Interval.Reductions.FullRange

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

/-- The complete-tree numerical bound for four collision and two chain advantages. -/
@[expose] def reductionBound (h w v : ℕ)
    (merkle encoding firstChain secondChain ud pre : ℝ≥0∞) : ℝ≥0∞ :=
  merkle + encoding + firstChain + secondChain +
    (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) * ((↑(2 ^ w) : ℝ≥0∞) * ud + pre)

/-- The concrete separate-term reduction inequality underlying Theorem 1. The parameter `qs`
controls the encoding target-collision transcript, and `K` controls its retry law. The source
adversary has the explicit pathwise signing-query bound; the authoritative adversary types preserve
their own sampling, seed-reveal and oracle disciplines. This proposition does not claim
reduction-query or running-time bounds. -/
@[expose]
def StrongUnforgeabilityReductionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (advGXMSS : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (advMerkleTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf (2 * (2 ^ h) * v * (2 ^ w))))
    (advEncodingTCR : Encoding.TargetCollisionResistance.Adversary
  (Encoding.TargetCollisionResistance.Problem.mk enc
    (HashInstance.thf hash).seedGen ($ᵗ R) qs K))
    (advFirstChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advSecondChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advUD : SM_DT_UD_Adversary
  (SM_DT_UD_Problem.standalone (HashInstance.thf hash) (HashInstance.digestInput hash)
    (HashInstance.digestInput hash).injective
        ($ᵗ H) ($ᵗ H) 1))
    (advPRE : SM_DT_PRE_Adversary
  (SM_DT_PRE_Problem.standalone (HashInstance.thf hash) (HashInstance.digestInput hash)
    (HashInstance.digestInput hash).injective 1)) :
    Prop :=
  SigningQueryBound qs advGXMSS →
  SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp advGXMSS ≤
    reductionBound h w v
      (SM_DT_TCR_Advantage advMerkleTCR)
      (Encoding.TargetCollisionResistance.advantage advEncodingTCR)
      (SM_DT_TCR_Advantage advFirstChainTCR) (SM_DT_TCR_Advantage advSecondChainTCR)
      (SM_DT_UD_Advantage advUD) (SM_DT_PRE_Advantage advPRE)

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
  unfold reductionBound
  have hbound := strong_unforgeability_power_of_two_reduction_bound
      hash enc K qs (GXMSS.IntervalMerkle.Interval.full h) hv hw htwo adv hqueries
  rw [GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full] at hbound
  simpa only [SyncSignatureUnforgeability.strongAdvantage,
    GXMSS.Interval.strongUnforgeableExp_full, GXMSS.Reductions.Epoch,
    GXMSS.Reductions.merkleTCRProblem, GXMSS.Reductions.chainTCRProblem,
    GXMSS.Reductions.encodingTCRProblem, GXMSS.Reductions.chainUDProblem,
    GXMSS.Reductions.chainPREProblem, Nat.cast_pow, Nat.cast_ofNat] using hbound

end

end GXMSS.Unforgeability
