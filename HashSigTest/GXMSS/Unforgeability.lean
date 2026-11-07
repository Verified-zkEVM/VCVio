/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability
public import HashSig.GXMSS.Security.EncodingInstances
public import HashSig.GXMSS.Security.Reductions.ChainHybrid
public import HashSig.GXMSS.Security.Reductions.CollisionBounds

/-! # Generalized XMSS strong-unforgeability reduction-bound probe -/

public section

namespace GXMSS.GXMSSUnforgeabilityProbe

example := @GXMSS.Reductions.encoding_problem_eq
example := @GXMSS.Unforgeability.SpecificEncoding.strong_unforgeability_bound_of_bridge
example := @GXMSS.Unforgeability.SpecificEncoding.winternitz_strong_unforgeability_bound
example := @GXMSS.Unforgeability.SpecificEncoding.target_sum_strong_unforgeability_bound
example :=
  @GXMSS.Unforgeability.SpecificEncoding.target_sum_strong_unforgeability_bound_of_small_target

example := @GXMSS.Unforgeability.StrongUnforgeabilityReductionBound
example := @GXMSS.Unforgeability.CorrectnessFailureBound
example := @GXMSS.Unforgeability.FirstMerkleTargetCollisionBound
example := @GXMSS.Unforgeability.first_merkle_target_collision_bound
example := @GXMSS.Unforgeability.SuccessfulEncodingTargetCollisionBound
example := @GXMSS.Unforgeability.successful_encoding_target_collision_bound
example := @GXMSS.Unforgeability.successful_first_chain_difference_le_target_collision_advantage
example := @GXMSS.Unforgeability.game_two_le_game_three_add_first_chain_target_collision
example := @GXMSS.Unforgeability.successful_second_chain_difference_le_target_collision_advantage
example := @GXMSS.Unforgeability.game_three_le_game_four_add_second_chain_target_collision
example := @GXMSS.Unforgeability.ValidForgeryYieldsMerkleCollisionStatement
example := @GXMSS.Unforgeability.ValidForgeryYieldsMerkleCollision
example := @GXMSS.Reductions.gameOne
example := @GXMSS.Reductions.gameOneObservation
example := @GXMSS.Reductions.merkleDifferenceObservation
example := @GXMSS.Reductions.sourceStrongObservation_eq_gameOne_or_merkleDifference
example := @GXMSS.Reductions.sourceProgram_map_eq_interaction
example := @GXMSS.Reductions.sourceStrongOutputMeasure_eq_strongUnforgeableExp
noncomputable example := @GXMSS.Reductions.gameOneOutputMeasure
noncomputable example := @GXMSS.Reductions.gameOneAdvantage
example := @GXMSS.Reductions.gameTwo
example := @GXMSS.Reductions.gameTwoObservation
noncomputable example := @GXMSS.Reductions.gameTwoOutputMeasure
noncomputable example := @GXMSS.Reductions.gameTwoAdvantage
noncomputable example := @GXMSS.Reductions.successfulEncodingDifferenceMass
example := @GXMSS.Reductions.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
example := @GXMSS.Reductions.gameThree
example := @GXMSS.Reductions.gameThreeObservation
example := @GXMSS.Reductions.gameFour
example := @GXMSS.Reductions.gameFourObservation
noncomputable example := @GXMSS.Reductions.gameFourAdvantage
noncomputable example := @GXMSS.Reductions.successfulSecondChainDifferenceMass
noncomputable example := @GXMSS.Reductions.successfulGameFourMass
noncomputable example := @GXMSS.Reductions.unusedGameFourMass
noncomputable example := @GXMSS.Reductions.failedConsumedGameFourMass
noncomputable example := @GXMSS.Reductions.nonSuccessGameFourMass
example := @GXMSS.Reductions.gameFourAdvantage_le_successful_add_nonSuccess
example := @GXMSS.Reductions.nonSuccessGameFourMass_le_unused_add_failedConsumed
example := @GXMSS.Reductions.gameFourObservation_unused
example := @GXMSS.Reductions.gameFourObservation_failedConsumed
example := @GXMSS.Reductions.gameFiveObservation_unused
example := @GXMSS.Reductions.gameFiveObservation_failedConsumed
example := @GXMSS.Reductions.gameFive
example := @GXMSS.Reductions.gameFiveObservation
example := @GXMSS.Reductions.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
example := @GXMSS.Reductions.guess_cardinality
example := @GXMSS.Reductions.guess_cardinality_le_paper_coefficient
example := @GXMSS.Reductions.gameFiveGuess_probability
example := @GXMSS.Reductions.gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
example := @GXMSS.Reductions.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
example := @GXMSS.Reductions.gameFourAdvantage_le_gameFive_add_unpaid_masses
example := @GXMSS.Reductions.NoMaximumOutput
example := @GXMSS.Reductions.findNonMaximumCoordinate
example := @GXMSS.Reductions.jointChainObservation
noncomputable example := @GXMSS.Reductions.jointChainOutputMeasure
noncomputable example := @GXMSS.Reductions.jointChainAdvantage
example := @GXMSS.Reductions.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
noncomputable example := @GXMSS.Reductions.jointPRESelectedProgram
example := @GXMSS.Reductions.jointPRESelectedMass_le_preimageAdvantage
example := @GXMSS.Reductions.JointChainHybridReturnedMeasureBridge
example := @GXMSS.Reductions.gameSix
example := @GXMSS.Reductions.gameSixObservation
example := @GXMSS.Reductions.encodingConsumedEpoch_rejected
example := @GXMSS.Reductions.registeredIndex_lt_length_of_mem
example := @GXMSS.Reductions.registeredIndex_lookup_of_mem
example := @GXMSS.Reductions.registeredIndex_lt_capacity_of_mem
example := @GXMSS.Reductions.merkleTargetCollisionReduction
noncomputable example := @GXMSS.Reductions.encodingTargetCollisionReduction
example := @GXMSS.Reductions.firstChainTargetCollisionReduction
example := @GXMSS.Reductions.secondChainTargetCollisionReduction
noncomputable example := @GXMSS.Reductions.undetectabilityReduction
example := @GXMSS.Reductions.preimageReduction
noncomputable example := @GXMSS.Reductions.jointUndetectabilityReduction
example := @GXMSS.Reductions.jointPreimageReduction
example := @GXMSS.Reductions.noMaximumOutput_of_two_codewords
example := @GXMSS.Reductions.jointChainAdvantage_le_jointUD_add_jointPRESelected
example := @GXMSS.Reductions.jointChainHybridReturnedMeasureBridge
example := @GXMSS.Reductions.jointChainAdvantage_le_jointUD_add_jointPRE
example := @GXMSS.Unforgeability.strong_unforgeability_reduction_bound

open Encoding ENNReal TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/- These importing examples pin the exact finite guess count, its paper coefficient bound,
and the actual native returned-measure successful-record Game 4→5 equality. -/
example : Fintype.card (GXMSS.Reductions.Guess h w v) =
    2 ^ h * v * (2 ^ w - 1) :=
  GXMSS.Reductions.guess_cardinality h w v

example : Fintype.card (GXMSS.Reductions.Guess h w v) ≤
    2 ^ h * v * 2 ^ w :=
  GXMSS.Reductions.guess_cardinality_le_paper_coefficient h w v

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.successfulGameFourMass hash enc K adv =
      (Fintype.card (GXMSS.Reductions.Guess h w v) : ℝ≥0∞) *
        GXMSS.Reductions.gameFiveAdvantage hash enc K hv hw adv :=
  GXMSS.Reductions.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
    hash enc K hv hw adv

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v)
    (hnonmax : GXMSS.Reductions.NoMaximumOutput enc) :
    GXMSS.Reductions.gameFourAdvantage hash enc K adv =
      (Fintype.card (GXMSS.Reductions.Guess h w v) : ℝ≥0∞) *
        GXMSS.Reductions.jointChainAdvantage hash enc K hv hw adv :=
  GXMSS.Reductions.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
    hash enc K hv hw adv hnonmax

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.gameFiveOutputMeasure hash enc K hv hw adv Set.univ =
      GXMSS.Reductions.gameFourOutputMeasure hash enc K adv Set.univ :=
  GXMSS.Reductions.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
    hash enc K hv hw adv

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.gameFourAdvantage hash enc K adv ≤
      (Fintype.card (GXMSS.Reductions.Guess h w v) : ℝ≥0∞) *
        GXMSS.Reductions.gameFiveAdvantage hash enc K hv hw adv +
          GXMSS.Reductions.unusedGameFourMass hash enc K adv +
            GXMSS.Reductions.failedConsumedGameFourMass hash enc K adv :=
  GXMSS.Reductions.gameFourAdvantage_le_gameFive_add_unpaid_masses
    hash enc K hv hw adv

/- These importing-module examples state the first-chain and second-chain probability bounds
and apply their public theorems. -/
example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.successfulFirstChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K adv) :=
  GXMSS.Unforgeability.successful_first_chain_difference_le_target_collision_advantage
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.gameTwoAdvantage hash enc K adv ≤
      GXMSS.Reductions.gameThreeAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K adv) :=
  GXMSS.Unforgeability.game_two_le_game_three_add_first_chain_target_collision
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.successfulSecondChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K adv) :=
  GXMSS.Unforgeability.successful_second_chain_difference_le_target_collision_advantage
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.gameThreeAdvantage hash enc K adv ≤
      GXMSS.Reductions.gameFourAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K adv) :=
  GXMSS.Unforgeability.game_three_le_game_four_add_second_chain_target_collision
    hash enc K adv

/- `DirectTrustAudit` checks compiler origins and transitive axioms for the direct proof closure. -/
end GXMSS.GXMSSUnforgeabilityProbe
