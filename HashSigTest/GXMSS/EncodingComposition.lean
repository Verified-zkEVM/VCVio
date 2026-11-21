/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.EncodingInstances
public import HashSigTest.GXMSS.ActiveSecurity

/-!
# Singleton encoding-hash bridge application

A one-word global code with a nonmaximum digit reaches the actual complete hash-composition core.
Its source adversary returns a different valid signature at the recorded message/randomizer pair.
-/

public section
namespace GXMSS.EncodingCompositionProbe
open ENNReal IncomparableEncoding GXMSS.IntervalMerkle GXMSS.Reductions
open GXMSS.Interval.Unforgeability GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
open GXMSS.Unforgeability GXMSS.Unforgeability.SpecificEncoding
open OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability

/-- A constant unit message hash gives the same singleton code as the admitted source encoding. -/
@[expose] def bridge : TargetCollisionReduction.Bridge Unit Unit Unit (Epoch 0)
    ((Fin 1 × Fin 1 × Fin 1) ⊕ (Fin 1 × Fin 1)) Unit 1 2 where
  enc := ActiveSecurityProbe.encoding
  th := ⟨pure (), fun _ _ _ => ()⟩
  epochToTweak := fun _ => .inl (0, 0, 0)
  epochToTweak_injective := by
    intro e e' _
    apply Fin.ext
    have he := e.isLt
    have he' := e'.isLt
    simp only [Nat.pow_zero] at he he'
    omega
  accepts := fun _ => true
  word := fun _ _ => 0
  word_injective := fun _ _ _ => Subsingleton.elim _ _
  value_eq := fun _ _ _ _ => rfl

/-- The bridge code cannot meet a two-codeword premise. -/
theorem one_word :
    ¬ ∃ x y : Codeword 1 2, x ∈ bridge.enc.code ∧ y ∈ bridge.enc.code ∧ x ≠ y :=
  ActiveSecurityProbe.singleton_not_two

/-- The actual complete endpoint uses the pointwise core and its six native named strategies. -/
theorem native_bound :
    strongAdvantage (GXMSS.scheme ActiveSecurityProbe.hash bridge.enc 1)
      ProbCompRuntime.probComp ActiveSecurityProbe.adversary ≤
      reductionBound 0 1 1
        (SM_DT_TCR_Advantage (merkleTargetCollisionAdversary ActiveSecurityProbe.hash bridge.enc
          1 (Interval.full 0) (by decide) ActiveSecurityProbe.adversary))
        (SM_DT_RTCR_Advantage (encodingHashTargetCollisionReduction ActiveSecurityProbe.hash bridge
          (by rfl) 1 1 (Interval.full 0) ActiveSecurityProbe.adversary))
        (SM_DT_TCR_Advantage (sameMessageRandomizerChainTargetCollisionReduction
          ActiveSecurityProbe.hash bridge.enc 1 (Interval.full 0) ActiveSecurityProbe.adversary))
        (SM_DT_TCR_Advantage (chainCutTargetCollisionReduction ActiveSecurityProbe.hash bridge.enc
          1 (Interval.full 0) ActiveSecurityProbe.adversary))
        (SM_DT_UD_Advantage (chainUndetectabilityReduction ActiveSecurityProbe.hash bridge.enc
          1 (Interval.full 0) (by decide) (by decide) ActiveSecurityProbe.adversary))
        (SM_DT_PRE_Advantage (chainPreimageReduction ActiveSecurityProbe.hash bridge.enc
          1 (Interval.full 0) (by decide) (by decide) ActiveSecurityProbe.adversary)) := by
  exact strong_unforgeability_bound_of_bridge ActiveSecurityProbe.hash bridge (by rfl) 1 1
    (by decide) (by decide) ActiveSecurityProbe.singleton_nonmaximum ActiveSecurityProbe.adversary
    ActiveSecurityProbe.one_request

end GXMSS.EncodingCompositionProbe
