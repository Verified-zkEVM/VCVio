/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability

/-! # Generalized XMSS strong-unforgeability reduction-bound probe -/

public section

namespace GXMSS.UnforgeabilityProbe

#check @Reductions.encoding_problem_eq
#check @Reductions.strong_unforgeability_bound_of_bridge
#check @Unforgeability.SpecificEncoding.winternitz_strong_unforgeability_bound
#check @Unforgeability.SpecificEncoding.target_sum_strong_unforgeability_bound
#check @Unforgeability.SpecificEncoding.target_sum_strong_unforgeability_bound_of_small_target

#check @Unforgeability.StrongUnforgeabilityReductionBound
#check @Unforgeability.CorrectnessFailureBound
#check @Unforgeability.FirstMerkleTargetCollisionBound
#check @Unforgeability.first_merkle_target_collision_bound
#check @Unforgeability.SuccessfulEncodingTargetCollisionBound
#check @Unforgeability.successful_encoding_target_collision_bound
#check @Unforgeability.successful_first_chain_difference_le_target_collision_advantage
#check @Unforgeability.game_two_le_game_three_add_first_chain_target_collision
#check @Unforgeability.successful_second_chain_difference_le_target_collision_advantage
#check @Unforgeability.game_three_le_game_four_add_second_chain_target_collision
#check @Unforgeability.ValidForgeryYieldsMerkleCollisionStatement
#check @Unforgeability.ValidForgeryYieldsMerkleCollision
#check @Reductions.gameOne
#check @Reductions.gameOneObservation
#check @Reductions.merkleDifferenceObservation
#check @Reductions.sourceStrongObservation_eq_gameOne_or_merkleDifference
#check @Reductions.sourceProgram_map_eq_interaction
#check @Reductions.sourceStrongOutputMeasure_eq_strongUnforgeableExp
#check @Reductions.gameOneOutputMeasure
#check @Reductions.gameOneAdvantage
#check @Reductions.gameTwo
#check @Reductions.gameTwoObservation
#check @Reductions.gameTwoOutputMeasure
#check @Reductions.gameTwoAdvantage
#check @Reductions.successfulEncodingDifferenceMass
#check @Reductions.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
#check @Reductions.gameThree
#check @Reductions.gameThreeObservation
#check @Reductions.gameFour
#check @Reductions.gameFourObservation
#check @Reductions.gameFourAdvantage
#check @Reductions.successfulSecondChainDifferenceMass
#check @Reductions.successfulGameFourMass
#check @Reductions.unusedGameFourMass
#check @Reductions.failedConsumedGameFourMass
#check @Reductions.nonSuccessGameFourMass
#check @Reductions.gameFourAdvantage_le_successful_add_nonSuccess
#check @Reductions.nonSuccessGameFourMass_le_unused_add_failedConsumed
#check @Reductions.gameFourObservation_unused
#check @Reductions.gameFourObservation_failedConsumed
#check @Reductions.gameFiveObservation_unused
#check @Reductions.gameFiveObservation_failedConsumed
#check @Reductions.gameFive
#check @Reductions.gameFiveObservation
#check @Reductions.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
#check @Reductions.guess_cardinality
#check @Reductions.guess_cardinality_le_paper_coefficient
#check @Reductions.gameFiveGuess_probability
#check @Reductions.gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
#check @Reductions.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
#check @Reductions.gameFourAdvantage_le_gameFive_add_unpaid_masses
#check @Reductions.NoMaximumOutput
#check @Reductions.findNonMaximumCoordinate
#check @Reductions.jointChainObservation
#check @Reductions.jointChainOutputMeasure
#check @Reductions.jointChainAdvantage
#check @Reductions.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
#check @Reductions.jointPRESelectedProgram
#check @Reductions.jointPRESelectedMass_le_preimageAdvantage
#check @Reductions.JointChainHybridReturnedMeasureBridge
#check @Reductions.gameSix
#check @Reductions.gameSixObservation
#check @Reductions.encodingConsumedEpoch_rejected
#check @Reductions.registeredIndex_lt_length_of_mem
#check @Reductions.registeredIndex_lookup_of_mem
#check @Reductions.registeredIndex_lt_capacity_of_mem
#check @Reductions.merkleTargetCollisionReduction
#check @Reductions.encodingTargetCollisionReduction
#check @Reductions.firstChainTargetCollisionReduction
#check @Reductions.secondChainTargetCollisionReduction
#check @Reductions.undetectabilityReduction
#check @Reductions.preimageReduction
#check @Reductions.jointUndetectabilityReduction
#check @Reductions.jointPreimageReduction
#check @Reductions.noMaximumOutput_of_two_codewords
#check @Reductions.jointChainAdvantage_le_jointUD_add_jointPRESelected
#check @Reductions.jointChainHybridReturnedMeasureBridge
#check @Reductions.jointChainAdvantage_le_jointUD_add_jointPRE
#check @Unforgeability.strong_unforgeability_reduction_bound

open Encoding ENNReal TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/- These importing examples pin the exact finite guess count, its paper coefficient bound,
and the actual native returned-measure successful-record Game 4→5 equality. -/
example : Fintype.card (Reductions.Guess h w v) =
    2 ^ h * v * (2 ^ w - 1) :=
  Reductions.guess_cardinality h w v

example : Fintype.card (Reductions.Guess h w v) ≤
    2 ^ h * v * 2 ^ w :=
  Reductions.guess_cardinality_le_paper_coefficient h w v

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.successfulGameFourMass hash enc K adv =
      (Fintype.card (Reductions.Guess h w v) : ℝ≥0∞) *
        Reductions.gameFiveAdvantage hash enc K hv hw adv :=
  Reductions.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
    hash enc K hv hw adv

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Reductions.SchemeAdversary PP H M R h v)
    (hnonmax : Reductions.NoMaximumOutput enc) :
    Reductions.gameFourAdvantage hash enc K adv =
      (Fintype.card (Reductions.Guess h w v) : ℝ≥0∞) *
        Reductions.jointChainAdvantage hash enc K hv hw adv :=
  Reductions.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
    hash enc K hv hw adv hnonmax

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.gameFiveOutputMeasure hash enc K hv hw adv Set.univ =
      Reductions.gameFourOutputMeasure hash enc K adv Set.univ :=
  Reductions.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
    hash enc K hv hw adv

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.gameFourAdvantage hash enc K adv ≤
      (Fintype.card (Reductions.Guess h w v) : ℝ≥0∞) *
        Reductions.gameFiveAdvantage hash enc K hv hw adv +
          Reductions.unusedGameFourMass hash enc K adv +
            Reductions.failedConsumedGameFourMass hash enc K adv :=
  Reductions.gameFourAdvantage_le_gameFive_add_unpaid_masses
    hash enc K hv hw adv

/- These examples apply the first- and second-chain bounds through their public interfaces. -/
example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.successfulFirstChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (Reductions.firstChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.successful_first_chain_difference_le_target_collision_advantage
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.gameTwoAdvantage hash enc K adv ≤
      Reductions.gameThreeAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (Reductions.firstChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.game_two_le_game_three_add_first_chain_target_collision
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.successfulSecondChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (Reductions.secondChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.successful_second_chain_difference_le_target_collision_advantage
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.gameThreeAdvantage hash enc K adv ≤
      Reductions.gameFourAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (Reductions.secondChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.game_three_le_game_four_add_second_chain_target_collision
    hash enc K adv

end GXMSS.UnforgeabilityProbe
