/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.CollisionReductions
public import HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction

/-!
# Composition with encoding hash target-collision reductions

Seed-sampler agreement identifies the scheme's encoding game with the bridge game.
The encoding advantage is bounded by the hash's SM-DT-rTCR advantage.
-/

public section

namespace GXMSS.Reductions

open GXMSS.Encoding
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

/-- The scheme's encoding target-collision advantage is bounded by the composed hash
target-collision advantage under the same public-seed sampler. -/
theorem encodingTargetCollisionAdvantage_le_hash
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq Y]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    TargetCollisionResistance.advantage
        (encodingTargetCollisionReduction hash bridge.enc qs K adv) ≤
      SM_DT_RTCR_Advantage (encodingHashTargetCollisionReduction hash bridge hseed qs K adv) := by
  let source := encodingTargetCollisionReduction hash bridge.enc qs K adv
  let source' := (encoding_problem_eq hash bridge qs K hseed) ▸ source
  calc
    TargetCollisionResistance.advantage source =
        TargetCollisionResistance.advantage source' :=
      advantage_eq_transport (encoding_problem_eq hash bridge qs K hseed) source
    _ ≤ _ := TargetCollisionReduction.advantage_le_hash bridge qs K source'

end GXMSS.Reductions
