/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction
public import HashSig.GXMSS.Encoding.TargetSum

/-!
# Target-sum encoding collision bridge

The hash word is returned unchanged exactly when its bounded digit sum is the target. Failed
queries retain an occupied source epoch and an exhausted VCVio target slot.
-/

public section

namespace GXMSS.Encoding.TargetSumCollision

open TargetCollisionReduction

variable {PP M R E Tweak : Type} {v w target : ℕ}

/-- The target-sum predicate tests the challenged hash word itself. -/
@[expose] def accepts (word : Codeword v (2 ^ w)) : Bool :=
  decide (∑ i : Fin v, (word i).val = target)

/-- The accepted target-sum encoding instantiates the shared bridge. -/
@[expose] def bridge (params : TargetSum.Parameters PP M R E Tweak v w target)
    (hEpoch : Function.Injective params.epochToTweak) :
    Bridge PP M R E Tweak (Codeword v (2 ^ w)) v (2 ^ w) where
  enc := TargetSum.encoding params
  th := params.thf
  epochToTweak := params.epochToTweak
  epochToTweak_injective := hEpoch
  accepts := accepts (target := target)
  word := id
  word_injective := Function.injective_id
  value_eq := by
    intro pp msg r ep
    by_cases h : (∑ i : Fin v,
        (params.thf.eval pp (params.epochToTweak ep) (msg, r) i).val) = target
    · simp [TargetSum.encoding, IncomparableEncoding.value, accepts, h]
    · simp [TargetSum.encoding, IncomparableEncoding.value, accepts, h]

/-- Identification with a uniformly sampled paper parameter requires this separate seed law. -/
@[expose] def UniformSeedLaw [Fintype PP]
    (params : TargetSum.Parameters PP M R E Tweak v w target) : Prop :=
  UniformSampler ProbCompRuntime.probComp params.thf.seedGen

/-- The target-sum collision game transfers to SM-DT-rTCR with the hash-word digit-sum
predicate and the same capacities, including zero. Returned sum failures remain occupied slots. -/
theorem advantage_le_hash [SampleableType R]
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq (Codeword v (2 ^ w))]
    (params : TargetSum.Parameters PP M R E Tweak v w target)
    (hEpoch : Function.Injective params.epochToTweak) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary
      (encodingProblem (bridge params hEpoch) p K)) :
    TargetCollisionResistance.advantage source ≤
      TweakableHash.SM_DT_RTCR_Advantage
        (reduction (bridge params hEpoch) p K source) :=
  TargetCollisionReduction.advantage_le_hash (bridge params hEpoch) p K source

end GXMSS.Encoding.TargetSumCollision
