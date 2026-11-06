/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability
public import HashSig.GXMSS.Security.Reductions.CollisionBounds

/-! # Generalized XMSS strong-unforgeability reduction-bound probe -/

public section

namespace GXMSS.GXMSSUnforgeabilityProbe

#check @GXMSS.Reductions.encoding_problem_eq
#check @GXMSS.Unforgeability.SpecificEncoding.strong_unforgeability_bound_of_bridge
#check @GXMSS.Unforgeability.SpecificEncoding.winternitz_strong_unforgeability_bound
#check @GXMSS.Unforgeability.SpecificEncoding.target_sum_strong_unforgeability_bound
#check @GXMSS.Unforgeability.SpecificEncoding.target_sum_strong_unforgeability_bound_of_small_target

#check @GXMSS.Unforgeability.StrongUnforgeabilityReductionBound
#check @GXMSS.Unforgeability.CorrectnessFailureBound
#check @GXMSS.Unforgeability.FirstMerkleTargetCollisionBound
#check @GXMSS.Unforgeability.first_merkle_target_collision_bound
#check @GXMSS.Unforgeability.SuccessfulEncodingTargetCollisionBound
#check @GXMSS.Unforgeability.successful_encoding_target_collision_bound
#check @GXMSS.Unforgeability.successful_first_chain_difference_le_target_collision_advantage
#check @GXMSS.Unforgeability.game_two_le_game_three_add_first_chain_target_collision
#check @GXMSS.Unforgeability.successful_second_chain_difference_le_target_collision_advantage
#check @GXMSS.Unforgeability.game_three_le_game_four_add_second_chain_target_collision
#check @GXMSS.Unforgeability.ValidForgeryYieldsMerkleCollisionStatement
#check @GXMSS.Unforgeability.ValidForgeryYieldsMerkleCollision
#check @GXMSS.Reductions.gameOne
#check @GXMSS.Reductions.gameOneObservation
#check @GXMSS.Reductions.merkleDifferenceObservation
#check @GXMSS.Reductions.sourceStrongObservation_eq_gameOne_or_merkleDifference
#check @GXMSS.Reductions.sourceProgram_map_eq_interaction
#check @GXMSS.Reductions.sourceStrongOutputMeasure_eq_strongUnforgeableExp
#check @GXMSS.Reductions.gameOneOutputMeasure
#check @GXMSS.Reductions.gameOneAdvantage
#check @GXMSS.Reductions.gameTwo
#check @GXMSS.Reductions.gameTwoObservation
#check @GXMSS.Reductions.gameTwoOutputMeasure
#check @GXMSS.Reductions.gameTwoAdvantage
#check @GXMSS.Reductions.successfulEncodingDifferenceMass
#check @GXMSS.Reductions.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
#check @GXMSS.Reductions.gameThree
#check @GXMSS.Reductions.gameThreeObservation
#check @GXMSS.Reductions.gameFour
#check @GXMSS.Reductions.gameFourObservation
#check @GXMSS.Reductions.gameFourAdvantage
#check @GXMSS.Reductions.successfulSecondChainDifferenceMass
#check @GXMSS.Reductions.successfulGameFourMass
#check @GXMSS.Reductions.unusedGameFourMass
#check @GXMSS.Reductions.failedConsumedGameFourMass
#check @GXMSS.Reductions.nonSuccessGameFourMass
#check @GXMSS.Reductions.gameFourAdvantage_le_successful_add_nonSuccess
#check @GXMSS.Reductions.nonSuccessGameFourMass_le_unused_add_failedConsumed
#check @GXMSS.Reductions.gameFourObservation_unused
#check @GXMSS.Reductions.gameFourObservation_failedConsumed
#check @GXMSS.Reductions.gameFiveObservation_unused
#check @GXMSS.Reductions.gameFiveObservation_failedConsumed
#check @GXMSS.Reductions.gameFive
#check @GXMSS.Reductions.gameFiveObservation
#check @GXMSS.Reductions.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
#check @GXMSS.Reductions.guess_cardinality
#check @GXMSS.Reductions.guess_cardinality_le_paper_coefficient
#check @GXMSS.Reductions.gameFiveGuess_probability
#check @GXMSS.Reductions.gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
#check @GXMSS.Reductions.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
#check @GXMSS.Reductions.gameFourAdvantage_le_gameFive_add_unpaid_masses
#check @GXMSS.Reductions.NoMaximumOutput
#check @GXMSS.Reductions.findNonMaximumCoordinate
#check @GXMSS.Reductions.jointChainObservation
#check @GXMSS.Reductions.jointChainOutputMeasure
#check @GXMSS.Reductions.jointChainAdvantage
#check @GXMSS.Reductions.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
#check @GXMSS.Reductions.jointPRESelectedProgram
#check @GXMSS.Reductions.jointPRESelectedMass_le_preimageAdvantage
#check @GXMSS.Reductions.JointChainHybridReturnedMeasureBridge
#check @GXMSS.Reductions.gameSix
#check @GXMSS.Reductions.gameSixObservation
#check @GXMSS.Reductions.encodingConsumedEpoch_rejected
#check @GXMSS.Reductions.registeredIndex_lt_length_of_mem
#check @GXMSS.Reductions.registeredIndex_lookup_of_mem
#check @GXMSS.Reductions.registeredIndex_lt_capacity_of_mem
#check @GXMSS.Reductions.merkleTargetCollisionReduction
#check @GXMSS.Reductions.encodingTargetCollisionReduction
#check @GXMSS.Reductions.firstChainTargetCollisionReduction
#check @GXMSS.Reductions.secondChainTargetCollisionReduction
#check @GXMSS.Reductions.undetectabilityReduction
#check @GXMSS.Reductions.preimageReduction
#check @GXMSS.Reductions.jointUndetectabilityReduction
#check @GXMSS.Reductions.jointPreimageReduction
#check @GXMSS.Reductions.noMaximumOutput_of_two_codewords
#check @GXMSS.Reductions.jointChainAdvantage_le_jointUD_add_jointPRESelected
#check @GXMSS.Reductions.jointChainHybridReturnedMeasureBridge
#check @GXMSS.Reductions.jointChainAdvantage_le_jointUD_add_jointPRE
#check @GXMSS.Unforgeability.strong_unforgeability_reduction_bound

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
