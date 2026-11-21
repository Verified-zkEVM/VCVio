/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.EncodingComposition
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Collision
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Counting
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz.Collision
public import HashSig.GXMSS.Security.Unforgeability

/-!
# GXMSS bounds for checksum and target-sum encodings

The complete endpoint composes the actual full-range interval strategies with generic encoding
hash collision bridges. Seed-sampler agreement is explicit; the core encoding premise is pointwise.
-/

public section

namespace GXMSS.Unforgeability.SpecificEncoding

open IncomparableEncoding GXMSS.IntervalMerkle
open GXMSS.Interval.Unforgeability GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
open SyncSignatureUnforgeability
open GXMSS.Unforgeability
open GXMSS.Reductions
open OracleComp TweakableHash ENNReal

variable {PP T X H M R Y : Type} {h w v n₀ target : ℕ}

/-- A nonmaximum encoding with a target-collision bridge yields a scheme bound in terms of the
encoding hash's SM-DT-rTCR advantage. The other generic GXMSS terms are unchanged. -/
theorem strong_unforgeability_bound_of_bridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hnonmax : bridge.enc.NoMaximumOutput)
    (adv : SchemeAdversary PP H M R h v)
    (hqueries : SigningQueryBound qs adv) :
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash bridge.enc K) ProbCompRuntime.probComp adv ≤
      reductionBound h w v
        (SM_DT_TCR_Advantage
          (merkleTargetCollisionAdversary hash bridge.enc K (Interval.full h) hv adv))
        (SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash bridge hseed qs K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction
            hash bridge.enc K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (chainCutTargetCollisionReduction hash bridge.enc K (Interval.full h) adv))
        (SM_DT_UD_Advantage
          (chainUndetectabilityReduction hash bridge.enc K (Interval.full h) hv hw adv))
        (SM_DT_PRE_Advantage
          (chainPreimageReduction hash bridge.enc K (Interval.full h) hv hw adv)) := by
  have hencoding := encodingTargetCollisionAdvantage_le_hash
    hash bridge hseed qs K (Interval.full h) adv
  have hbase := (GXMSS.Unforgeability.strong_unforgeability_reduction_bound
    hash bridge.enc K qs hv hw hnonmax adv) hqueries
  unfold reductionBound at hbase ⊢
  exact hbase.trans
    (_root_.add_le_add (_root_.add_le_add (_root_.add_le_add
      (_root_.add_le_add (_root_.add_le_add le_rfl hencoding) le_rfl) le_rfl) le_rfl) le_rfl)

/-- Two global codewords derive the geometry and pointwise premise for hash composition. -/
theorem strong_unforgeability_bound_of_bridge_of_two_codewords
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (K qs : ℕ)
    (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ bridge.enc.code ∧ y ∈ bridge.enc.code ∧ x ≠ y)
    (adv : SchemeAdversary PP H M R h v)
    (hqueries : SigningQueryBound qs adv) :
    let hv : 0 < v := by
      have := bridge.enc.two_le_length_of_two_codewords htwo
      omega
    let hw : 0 < w := by
      by_contra hz
      have hw0 : w = 0 := by omega
      have hr := bridge.enc.two_le_radix_of_two_codewords htwo
      simp [hw0] at hr
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash bridge.enc K) ProbCompRuntime.probComp adv ≤
      reductionBound h w v
        (SM_DT_TCR_Advantage
          (merkleTargetCollisionAdversary hash bridge.enc K (Interval.full h) hv adv))
        (SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash bridge hseed qs K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction
            hash bridge.enc K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (chainCutTargetCollisionReduction hash bridge.enc K (Interval.full h) adv))
        (SM_DT_UD_Advantage
          (chainUndetectabilityReduction hash bridge.enc K (Interval.full h) hv hw adv))
        (SM_DT_PRE_Advantage
          (chainPreimageReduction hash bridge.enc K (Interval.full h) hv hw adv)) := by
  have hv : 0 < v := by
    have := bridge.enc.two_le_length_of_two_codewords htwo
    omega
  have hw : 0 < w := by
    by_contra hz
    have hw0 : w = 0 := by omega
    have hr := bridge.enc.two_le_radix_of_two_codewords htwo
    simp [hw0] at hr
  exact strong_unforgeability_bound_of_bridge hash bridge hseed K qs hv hw
    (bridge.enc.noMaximumOutput_of_two_codewords htwo) adv hqueries

/-- The checksum-word instance has two global codewords from its positive payload length and
digit width. Its scheme bound charges encoding collisions to the message hash's SM-DT-rTCR game. -/
theorem winternitz_strong_unforgeability_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword n₀ (2 ^ w))]
    [DecidableEq (GXMSS.Signature R H h (n₀ + Winternitz.checksumWidth n₀ w))]
    (hash : HashInstance PP T X H h w (n₀ + Winternitz.checksumWidth n₀ w))
    (params : Winternitz.Parameters PP M R (Fin (2 ^ h)) T n₀ w)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (adv : SchemeAdversary PP H M R h (n₀ + Winternitz.checksumWidth n₀ w)) :
    SigningQueryBound qs adv →
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (Winternitz.encoding params) K) ProbCompRuntime.probComp adv ≤
      reductionBound h w (n₀ + Winternitz.checksumWidth n₀ w)
        (SM_DT_TCR_Advantage
          (merkleTargetCollisionAdversary hash (Winternitz.encoding params) K (Interval.full h)
            (by have := params.payloadLengthPositive; omega :
              0 < n₀ + Winternitz.checksumWidth n₀ w) adv))
        (SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (WinternitzCollision.bridge params hEpoch)
            (by simpa [WinternitzCollision.bridge] using hseed) qs K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction
            hash (Winternitz.encoding params) K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (chainCutTargetCollisionReduction
            hash (Winternitz.encoding params) K (Interval.full h) adv))
        (SM_DT_UD_Advantage
          (chainUndetectabilityReduction hash (Winternitz.encoding params) K (Interval.full h)
            (by have := params.payloadLengthPositive; omega :
              0 < n₀ + Winternitz.checksumWidth n₀ w) params.digitWidthPositive adv))
        (SM_DT_PRE_Advantage
          (chainPreimageReduction hash (Winternitz.encoding params) K (Interval.full h)
            (by have := params.payloadLengthPositive; omega :
              0 < n₀ + Winternitz.checksumWidth n₀ w) params.digitWidthPositive adv)) := by
  intro hqueries
  have hv : 0 < n₀ + Winternitz.checksumWidth n₀ w := by
    have := params.payloadLengthPositive
    omega
  have htwo : ∃ x y : Codeword (n₀ + Winternitz.checksumWidth n₀ w) (2 ^ w),
      x ∈ (WinternitzCollision.bridge params hEpoch).enc.code ∧
        y ∈ (WinternitzCollision.bridge params hEpoch).enc.code ∧ x ≠ y := by
    simpa only [WinternitzCollision.bridge, Winternitz.encoding] using
      Winternitz.two_codewords params
  exact strong_unforgeability_bound_of_bridge hash
    (WinternitzCollision.bridge params hEpoch)
    (by simpa [WinternitzCollision.bridge] using hseed) K qs hv
    params.digitWidthPositive
    ((WinternitzCollision.bridge params hEpoch).enc.noMaximumOutput_of_two_codewords htwo)
    adv hqueries

/-- The target-sum scheme bound under the exact parameter-only condition that its finite code
contains at least two words. The returned sum-mismatch failure mass is retained. -/
theorem target_sum_strong_unforgeability_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword v (2 ^ w))] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (params : TargetSum.Parameters PP M R (Fin (2 ^ h)) T v w target)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (hcount : 2 ≤ TargetSum.acceptedCount v w target)
    (adv : SchemeAdversary PP H M R h v) :
    SigningQueryBound qs adv →
    let htwo : ∃ x y : Codeword v (2 ^ w),
        x ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧
          y ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧ x ≠ y := by
      simpa only [TargetSumCollision.bridge, TargetSum.encoding] using
        TargetSum.two_codewords_of_acceptedCount v w target hcount
    let hv : 0 < v := by
      have := (TargetSumCollision.bridge params hEpoch).enc.two_le_length_of_two_codewords htwo
      omega
    let hw : 0 < w := by
      by_contra hz
      have hw0 : w = 0 := by omega
      have hr := (TargetSumCollision.bridge params hEpoch).enc.two_le_radix_of_two_codewords htwo
      simp [hw0] at hr
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (TargetSum.encoding params) K) ProbCompRuntime.probComp adv ≤
      reductionBound h w v
        (SM_DT_TCR_Advantage
          (merkleTargetCollisionAdversary
            hash (TargetSum.encoding params) K (Interval.full h) hv adv))
        (SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (TargetSumCollision.bridge params hEpoch)
            (by simpa [TargetSumCollision.bridge] using hseed) qs K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction
            hash (TargetSum.encoding params) K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (chainCutTargetCollisionReduction
            hash (TargetSum.encoding params) K (Interval.full h) adv))
        (SM_DT_UD_Advantage
          (chainUndetectabilityReduction
            hash (TargetSum.encoding params) K (Interval.full h) hv hw adv))
        (SM_DT_PRE_Advantage
          (chainPreimageReduction
            hash (TargetSum.encoding params) K (Interval.full h) hv hw adv)) := by
  intro hqueries
  have htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧
        y ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧ x ≠ y := by
    simpa only [TargetSumCollision.bridge, TargetSum.encoding] using
      TargetSum.two_codewords_of_acceptedCount v w target hcount
  exact strong_unforgeability_bound_of_bridge_of_two_codewords hash
    (TargetSumCollision.bridge params hEpoch)
    (by simpa [TargetSumCollision.bridge] using hseed) K qs htwo adv hqueries

/-- A positive target that fits in one digit, with at least two digit positions, directly
discharges the target-sum code-size premise in the scheme bound. -/
theorem target_sum_strong_unforgeability_bound_of_small_target
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword v (2 ^ w))] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (params : TargetSum.Parameters PP M R (Fin (2 ^ h)) T v w target)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (hv : 2 ≤ v) (hw : 0 < w) (htarget : 0 < target) (hfit : target < 2 ^ w)
    (adv : SchemeAdversary PP H M R h v) :
    SigningQueryBound qs adv →
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (TargetSum.encoding params) K) ProbCompRuntime.probComp adv ≤
      reductionBound h w v
        (SM_DT_TCR_Advantage
          (merkleTargetCollisionAdversary hash (TargetSum.encoding params) K (Interval.full h)
            (by omega : 0 < v) adv))
        (SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (TargetSumCollision.bridge params hEpoch)
            (by simpa [TargetSumCollision.bridge] using hseed) qs K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (sameMessageRandomizerChainTargetCollisionReduction
            hash (TargetSum.encoding params) K (Interval.full h) adv))
        (SM_DT_TCR_Advantage
          (chainCutTargetCollisionReduction
            hash (TargetSum.encoding params) K (Interval.full h) adv))
        (SM_DT_UD_Advantage
          (chainUndetectabilityReduction hash (TargetSum.encoding params) K (Interval.full h)
            (by omega : 0 < v) hw adv))
        (SM_DT_PRE_Advantage
          (chainPreimageReduction hash (TargetSum.encoding params) K (Interval.full h)
            (by omega : 0 < v) hw adv)) := by
  exact target_sum_strong_unforgeability_bound hash params hEpoch hseed K qs
    (TargetSum.acceptedCount_two_le_of_small_target v w target hv htarget hfit) adv

end GXMSS.Unforgeability.SpecificEncoding
