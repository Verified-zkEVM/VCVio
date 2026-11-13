/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.FullRange

/-!
# Complete-tree strong unforgeability

The complete source experiment is the full-range interval experiment. Its six named interval
reductions have original primitive domains and capacities. Exact positive-position coefficients
and their power-of-two relaxation are separate public bounds.
-/

public section

namespace GXMSS.Unforgeability

open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash
  GXMSS.Interval.Unforgeability GXMSS.IntervalMerkle GXMSS.Reductions
  GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain SyncSignatureUnforgeability

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The sharp complete-tree bound with exact positive-chain-position coefficients. -/
@[expose] def reductionBound (h w v : ℕ)
    (merkle encoding firstChain secondChain ud pre : ℝ≥0∞) : ℝ≥0∞ :=
  merkle + encoding + firstChain + secondChain +
    (↑((2 ^ h) * v * (2 ^ w - 1)) : ℝ≥0∞) * pre +
    (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) * ud

/-- The power-of-two relaxation of the exact complete-tree bound. -/
@[expose] def powerOfTwoReductionBound (h w v : ℕ)
    (merkle encoding firstChain secondChain ud pre : ℝ≥0∞) : ℝ≥0∞ :=
  merkle + encoding + firstChain + secondChain +
    (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) * ((↑(2 ^ w) : ℝ≥0∞) * ud + pre)

/-- Enlarging positive-position counts gives the power-of-two relaxation. -/
theorem reductionBound_le_powerOfTwo (h w v : ℕ)
    (merkle encoding firstChain secondChain ud pre : ℝ≥0∞) :
    reductionBound h w v merkle encoding firstChain secondChain ud pre ≤
      powerOfTwoReductionBound h w v merkle encoding firstChain secondChain ud pre := by
  unfold reductionBound powerOfTwoReductionBound
  calc
    _ ≤ merkle + encoding + firstChain + secondChain +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) * pre +
        (((2 ^ h) * v * (2 ^ w) ^ 2 : ℕ) : ℝ≥0∞) * ud := by
      gcongr <;> exact Nat.sub_le _ _
    _ = _ := by
      push_cast
      ring

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
    (advEncodingTCR : TargetCollisionResistance.Adversary
      (TargetCollisionResistance.Problem.mk enc hash.thf.seedGen ($ᵗ R) qs K))
    (advFirstChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advSecondChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advUD : SM_DT_UD_Adversary
      (SM_DT_UD_Problem.standalone hash.thf hash.digestInput hash.digestInput.injective
        ($ᵗ H) ($ᵗ H) 1))
    (advPRE : SM_DT_PRE_Adversary
      (SM_DT_PRE_Problem.standalone hash.thf hash.digestInput hash.digestInput.injective 1)) :
    Prop :=
  SigningQueryBound qs advGXMSS →
  SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp advGXMSS ≤
    reductionBound h w v
      (SM_DT_TCR_Advantage advMerkleTCR)
      (IncomparableEncoding.TargetCollisionResistance.advantage advEncodingTCR)
      (SM_DT_TCR_Advantage advFirstChainTCR) (SM_DT_TCR_Advantage advSecondChainTCR)
      (SM_DT_UD_Advantage advUD) (SM_DT_PRE_Advantage advPRE)

/-- The complete-tree separate-term bound follows from full-range interval security for a
pointwise nonmaximum encoding output condition. -/
theorem strong_unforgeability_reduction_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hnonmax : enc.NoMaximumOutput)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) :
    StrongUnforgeabilityReductionBound hash enc K qs adv
      (merkleTargetCollisionAdversary hash enc K (Interval.full h) hv adv)
      (GXMSS.Interval.Reductions.encodingTargetCollisionReduction
        hash enc qs K (Interval.full h) adv)
      (sameMessageRandomizerChainTargetCollisionReduction hash enc K (Interval.full h) adv)
      (chainCutTargetCollisionReduction hash enc K (Interval.full h) adv)
      (chainUndetectabilityReduction hash enc K (Interval.full h) hv hw adv)
      (chainPreimageReduction hash enc K (Interval.full h) hv hw adv) := by
  intro hqueries
  unfold reductionBound
  have hbound := GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound
      hash enc K qs (GXMSS.IntervalMerkle.Interval.full h) hv hw hnonmax adv hqueries
  rw [GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full] at hbound
  simpa only [SyncSignatureUnforgeability.strongAdvantage,
    GXMSS.Interval.strongUnforgeableExp_full, GXMSS.Reductions.Epoch,
    GXMSS.Reductions.merkleTCRProblem, GXMSS.Reductions.chainTCRProblem,
    GXMSS.Reductions.encodingTCRProblem, GXMSS.Reductions.chainUDProblem,
    GXMSS.Reductions.chainPREProblem, Nat.cast_pow, Nat.cast_ofNat] using hbound

/-- The complete strong-unforgeability theorem with relaxed power-of-two coefficients. -/
theorem strong_unforgeability_power_of_two_reduction_bound
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
    SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp adv ≤
      powerOfTwoReductionBound h w v
        (SM_DT_TCR_Advantage (merkleTargetCollisionAdversary hash enc K (Interval.full h) hv adv))
        (IncomparableEncoding.TargetCollisionResistance.advantage
          (GXMSS.Interval.Reductions.encodingTargetCollisionReduction
            hash enc qs K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction hash enc K (Interval.full h) adv))
        (SM_DT_TCR_Advantage (chainCutTargetCollisionReduction hash enc K (Interval.full h) adv))
        (SM_DT_UD_Advantage (chainUndetectabilityReduction hash enc K (Interval.full h) hv hw adv))
        (SM_DT_PRE_Advantage (chainPreimageReduction hash enc K (Interval.full h) hv hw adv)) := by
  exact (strong_unforgeability_reduction_bound hash enc K qs hv hw hnonmax adv hqueries).trans
    (reductionBound_le_powerOfTwo h w v _ _ _ _ _ _)

/-- Two distinct global words derive the complete endpoint's positivity and encoding premises. -/
theorem strong_unforgeability_reduction_bound_of_two_codewords
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) :
    let hv : 0 < v := by
      have := enc.two_le_length_of_two_codewords htwo
      omega
    let hw : 0 < w := by
      by_contra hz
      have hw0 : w = 0 := by omega
      have hr := enc.two_le_radix_of_two_codewords htwo
      simp [hw0] at hr
    StrongUnforgeabilityReductionBound hash enc K qs adv
      (merkleTargetCollisionAdversary hash enc K (Interval.full h) hv adv)
      (GXMSS.Interval.Reductions.encodingTargetCollisionReduction
        hash enc qs K (Interval.full h) adv)
      (sameMessageRandomizerChainTargetCollisionReduction hash enc K (Interval.full h) adv)
      (chainCutTargetCollisionReduction hash enc K (Interval.full h) adv)
      (chainUndetectabilityReduction hash enc K (Interval.full h) hv hw adv)
      (chainPreimageReduction hash enc K (Interval.full h) hv hw adv) := by
  have hv : 0 < v := by
    have := enc.two_le_length_of_two_codewords htwo
    omega
  have hw : 0 < w := by
    by_contra hz
    have hw0 : w = 0 := by omega
    have hr := enc.two_le_radix_of_two_codewords htwo
    simp [hw0] at hr
  exact strong_unforgeability_reduction_bound hash enc K qs hv hw
    (enc.noMaximumOutput_of_two_codewords htwo) adv

/-- Two distinct global words derive the complete endpoint's positivity and encoding premises. -/
theorem strong_unforgeability_power_of_two_reduction_bound_of_two_codewords
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (hqueries : SigningQueryBound qs adv) :
    let hv : 0 < v := by
      have := enc.two_le_length_of_two_codewords htwo
      omega
    let hw : 0 < w := by
      by_contra hz
      have hw0 : w = 0 := by omega
      have hr := enc.two_le_radix_of_two_codewords htwo
      simp [hw0] at hr
    SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp adv ≤
      powerOfTwoReductionBound h w v
        (SM_DT_TCR_Advantage (merkleTargetCollisionAdversary hash enc K (Interval.full h) hv adv))
        (IncomparableEncoding.TargetCollisionResistance.advantage
          (GXMSS.Interval.Reductions.encodingTargetCollisionReduction
            hash enc qs K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction hash enc K (Interval.full h) adv))
        (SM_DT_TCR_Advantage (chainCutTargetCollisionReduction hash enc K (Interval.full h) adv))
        (SM_DT_UD_Advantage (chainUndetectabilityReduction hash enc K (Interval.full h) hv hw adv))
        (SM_DT_PRE_Advantage (chainPreimageReduction hash enc K (Interval.full h) hv hw adv)) := by
  have hv : 0 < v := by
    have := enc.two_le_length_of_two_codewords htwo
    omega
  have hw : 0 < w := by
    by_contra hz
    have hw0 : w = 0 := by omega
    have hr := enc.two_le_radix_of_two_codewords htwo
    simp [hw0] at hr
  exact strong_unforgeability_power_of_two_reduction_bound hash enc K qs hv hw
    (enc.noMaximumOutput_of_two_codewords htwo) adv hqueries

end

end GXMSS.Unforgeability
