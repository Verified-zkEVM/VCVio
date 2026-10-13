/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability
public import HashSig.GXMSS.Security.WinternitzEncodingTargetCollision
public import HashSig.GXMSS.Security.TargetSumEncodingTargetCollision

/-!
# GXMSS bounds for checksum and target-sum encodings

These bounds compose the generic two-codeword GXMSS theorem with the native encoding
target-collision bridges. Equality of public-seed samplers is explicit because the scheme
hash and encoding hash have different input and output types.
-/

public section

namespace GXMSS.Encoding.SpecializedUnforgeability

open GXMSS.Encoding
open GXMSS.Unforgeability
open GXMSS.ReductionGames
open OracleComp TweakableHash ENNReal

variable {PP T X H M R Y : Type} {h w v n₀ target : ℕ}

/-- Seed-sampler agreement identifies the scheme's encoding game with the bridge game. -/
theorem encoding_problem_eq [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (qs K : ℕ) (hseed : hash.thf.seedGen = bridge.th.seedGen) :
    encodingTCRProblem hash bridge.enc qs K =
      TargetCollisionReduction.encodingProblem bridge qs K := by
  simp [encodingTCRProblem, TargetCollisionReduction.encodingProblem, hseed]

private theorem advantage_eq_transport
    [DecidableEq M] [DecidableEq R]
    {P Q : TargetCollisionResistance.Problem PP M R (Fin (2 ^ h)) v (2 ^ w)}
    (heq : P = Q) (source : TargetCollisionResistance.Adversary P) :
    TargetCollisionResistance.advantage source =
      TargetCollisionResistance.advantage (heq ▸ source) := by
  cases heq
  rfl

/-- The hash-game adversary obtained from the scheme's encoding-game adversary. -/
@[expose] noncomputable def encodingHashTargetCollisionReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq R]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :=
  TargetCollisionReduction.reduction bridge qs K
    ((encoding_problem_eq hash bridge qs K hseed) ▸
      encodingTargetCollisionReduction hash bridge.enc qs K adv)

set_option maxHeartbeats 800000 in
-- Elaborating the six scheme reductions and the dependent transport of the encoding adversary
-- through the seed-agreed target-collision problem exceeds the default heartbeat limit.
/-- A two-word encoding with a target-collision bridge yields a scheme bound in terms of the
encoding hash's SM-DT-rTCR advantage. The other generic GXMSS terms are unchanged. -/
theorem strong_unforgeability_bound_of_bridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ bridge.enc.code ∧ y ∈ bridge.enc.code ∧ x ≠ y)
    (adv : SchemeAdversary PP H M R h v)
    (hqueries : SigningQueryBound qs adv) :
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash bridge.enc K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage (merkleTargetCollisionReduction hash bridge.enc K hv adv) +
        SM_DT_RTCR_Advantage (encodingHashTargetCollisionReduction hash bridge hseed qs K adv) +
        SM_DT_TCR_Advantage (firstChainTargetCollisionReduction hash bridge.enc K adv) +
        SM_DT_TCR_Advantage (secondChainTargetCollisionReduction hash bridge.enc K adv) +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage (jointUndetectabilityReduction hash bridge.enc K hv hw adv) +
            SM_DT_PRE_Advantage (jointPreimageReduction hash bridge.enc K hv hw adv)) := by
  let source := encodingTargetCollisionReduction hash bridge.enc qs K adv
  let source' := (encoding_problem_eq hash bridge qs K hseed) ▸ source
  have hcast : TargetCollisionResistance.advantage source =
      TargetCollisionResistance.advantage source' :=
    advantage_eq_transport (encoding_problem_eq hash bridge qs K hseed) source
  have hhash := TargetCollisionReduction.advantage_le_hash bridge qs K source'
  have hbase := (strong_unforgeability_reduction_bound_of_two_codewords
    hash bridge.enc K qs hv hw htwo adv) hqueries
  change SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.scheme hash bridge.enc K) ProbCompRuntime.probComp adv ≤
    SM_DT_TCR_Advantage (merkleTargetCollisionReduction hash bridge.enc K hv adv) +
      TargetCollisionResistance.advantage source +
      SM_DT_TCR_Advantage (firstChainTargetCollisionReduction hash bridge.enc K adv) +
      SM_DT_TCR_Advantage (secondChainTargetCollisionReduction hash bridge.enc K adv) +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) *
            SM_DT_UD_Advantage (jointUndetectabilityReduction hash bridge.enc K hv hw adv) +
          SM_DT_PRE_Advantage (jointPreimageReduction hash bridge.enc K hv hw adv)) at hbase
  calc
    _ ≤ _ := hbase
    _ ≤ _ := by
      dsimp only [encodingHashTargetCollisionReduction]
      rw [hcast]
      gcongr

set_option maxHeartbeats 800000 in
-- The checksum code dimensions appear in all six concrete reduction types and require a larger
-- elaboration budget when the generic composition theorem is specialized.
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
      SM_DT_TCR_Advantage
          (merkleTargetCollisionReduction hash (Winternitz.encoding params) K
            (by have := params.payloadLengthPositive; omega :
              0 < n₀ + Winternitz.checksumWidth n₀ w) adv) +
        SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (WinternitzCollision.bridge params hEpoch)
            (by simpa [WinternitzCollision.bridge] using hseed) qs K adv) +
        SM_DT_TCR_Advantage
          (firstChainTargetCollisionReduction hash (Winternitz.encoding params) K adv) +
        SM_DT_TCR_Advantage
          (secondChainTargetCollisionReduction hash (Winternitz.encoding params) K adv) +
        (↑((2 ^ h) * (n₀ + Winternitz.checksumWidth n₀ w) * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage
                (jointUndetectabilityReduction hash (Winternitz.encoding params) K
                  (by have := params.payloadLengthPositive; omega :
                    0 < n₀ + Winternitz.checksumWidth n₀ w)
                  params.digitWidthPositive adv) +
            SM_DT_PRE_Advantage
              (jointPreimageReduction hash (Winternitz.encoding params) K
                (by have := params.payloadLengthPositive; omega :
                  0 < n₀ + Winternitz.checksumWidth n₀ w)
                params.digitWidthPositive adv)) := by
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
    params.digitWidthPositive htwo adv hqueries

set_option maxHeartbeats 800000 in
-- Specializing the generic scheme reduction to the target-sum bridge elaborates six concrete
-- adversary types and exceeds the default heartbeat limit.
/-- The target-sum scheme bound under the exact parameter-only condition that its finite code
contains at least two words. The returned sum-mismatch failure mass is retained. -/
theorem target_sum_strong_unforgeability_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword v (2 ^ w))]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (params : TargetSum.Parameters PP M R (Fin (2 ^ h)) T v w target)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hcount : 2 ≤ TargetSum.acceptedCount v w target)
    (adv : SchemeAdversary PP H M R h v) :
    SigningQueryBound qs adv →
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (TargetSum.encoding params) K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage
          (merkleTargetCollisionReduction hash (TargetSum.encoding params) K hv adv) +
        SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (TargetSumCollision.bridge params hEpoch)
            (by simpa [TargetSumCollision.bridge] using hseed) qs K adv) +
        SM_DT_TCR_Advantage
          (firstChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        SM_DT_TCR_Advantage
          (secondChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage
                (jointUndetectabilityReduction hash (TargetSum.encoding params) K hv hw adv) +
            SM_DT_PRE_Advantage
              (jointPreimageReduction hash (TargetSum.encoding params) K hv hw adv)) := by
  intro hqueries
  have htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧
        y ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧ x ≠ y := by
    simpa only [TargetSumCollision.bridge, TargetSum.encoding] using
      TargetSum.two_codewords_of_acceptedCount v w target hcount
  exact strong_unforgeability_bound_of_bridge hash
    (TargetSumCollision.bridge params hEpoch)
    (by simpa [TargetSumCollision.bridge] using hseed) K qs hv hw htwo adv hqueries

/-- A positive target that fits in one digit, with at least two digit positions, directly
discharges the target-sum code-size premise in the scheme bound. -/
theorem target_sum_strong_unforgeability_bound_of_small_target
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword v (2 ^ w))]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (params : TargetSum.Parameters PP M R (Fin (2 ^ h)) T v w target)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (hv : 2 ≤ v) (hw : 0 < w) (htarget : 0 < target) (hfit : target < 2 ^ w)
    (adv : SchemeAdversary PP H M R h v) :
    SigningQueryBound qs adv →
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (TargetSum.encoding params) K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage
          (merkleTargetCollisionReduction hash (TargetSum.encoding params) K
            (by omega : 0 < v) adv) +
        SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (TargetSumCollision.bridge params hEpoch)
            (by simpa [TargetSumCollision.bridge] using hseed) qs K adv) +
        SM_DT_TCR_Advantage
          (firstChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        SM_DT_TCR_Advantage
          (secondChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage
                (jointUndetectabilityReduction hash (TargetSum.encoding params) K
                  (by omega : 0 < v) hw adv) +
            SM_DT_PRE_Advantage
              (jointPreimageReduction hash (TargetSum.encoding params) K
                (by omega : 0 < v) hw adv)) := by
  exact target_sum_strong_unforgeability_bound hash params hEpoch hseed K qs
    (by omega : 0 < v) hw
    (TargetSum.acceptedCount_two_le_of_small_target v w target hv htarget hfit) adv

end GXMSS.Encoding.SpecializedUnforgeability
