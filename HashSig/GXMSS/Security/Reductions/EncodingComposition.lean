/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.MerkleCollision
public import HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction

/-!
# Composition with encoding hash target-collision reductions

Seed-sampler agreement identifies the scheme's encoding game with the bridge game.
The composed bound charges the encoding term to the hash's SM-DT-rTCR advantage.
-/

public section

namespace GXMSS.Reductions

open GXMSS.Encoding GXMSS.Unforgeability
open OracleComp TweakableHash ENNReal

variable {PP T X H M R Y : Type} {h w v : ℕ}

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
/-- Compose a generic scheme bound with the encoding hash's SM-DT-rTCR reduction.
The Merkle, chain, undetectability, and preimage terms are preserved. -/
theorem strong_unforgeability_bound_of_bridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : StrongUnforgeabilityReductionBound hash bridge.enc K qs adv
      (merkleTargetCollisionReduction hash bridge.enc K hv adv)
      (encodingTargetCollisionReduction hash bridge.enc qs K adv)
      (firstChainTargetCollisionReduction hash bridge.enc K adv)
      (secondChainTargetCollisionReduction hash bridge.enc K adv)
      (jointUndetectabilityReduction hash bridge.enc K hv hw adv)
      (jointPreimageReduction hash bridge.enc K hv hw adv))
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
  have hbase := hbound hqueries
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

end GXMSS.Reductions
