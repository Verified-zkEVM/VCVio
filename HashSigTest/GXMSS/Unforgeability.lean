/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public import HashSig.GXMSS.Security.Unforgeability
public import HashSig.GXMSS.Security.EncodingSpecializedUnforgeability
import all HashSig.GXMSS.Security.Unforgeability
import all HashSig.GXMSS.Security.EncodingSpecializedUnforgeability
import all HashSig.GXMSS.Security.ReductionGames.GuessingGames
import all HashSig.GXMSS.Security.ReductionGames.JointReductions
import all HashSig.GXMSS.Security.Unforgeability.MerkleCollision
import all HashSig.GXMSS.Security.Unforgeability.FirstChainCollision
import all HashSig.GXMSS.Security.Unforgeability.SecondChainCollision
import all HashSig.GXMSS.Security.Unforgeability.ReductionBound

/-! # Generalized XMSS strong-unforgeability reduction-bound probe -/

public section

namespace GXMSS.UnforgeabilityProbe

#check @Encoding.SpecializedUnforgeability.encoding_problem_eq
#check @Encoding.SpecializedUnforgeability.strong_unforgeability_bound_of_bridge
#check @Encoding.SpecializedUnforgeability.winternitz_strong_unforgeability_bound
#check @Encoding.SpecializedUnforgeability.target_sum_strong_unforgeability_bound
#check @Encoding.SpecializedUnforgeability.target_sum_strong_unforgeability_bound_of_small_target

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
#check @ReductionGames.gameOne
#check @ReductionGames.gameOneObservation
#check @ReductionGames.merkleDifferenceObservation
#check @ReductionGames.sourceStrongObservation_eq_gameOne_or_merkleDifference
#check @ReductionGames.sourceProgram_map_eq_interaction
#check @ReductionGames.sourceStrongOutputMeasure_eq_strongUnforgeableExp
#check @ReductionGames.gameOneOutputMeasure
#check @ReductionGames.gameOneAdvantage
#check @ReductionGames.gameTwo
#check @ReductionGames.gameTwoObservation
#check @ReductionGames.gameTwoOutputMeasure
#check @ReductionGames.gameTwoAdvantage
#check @ReductionGames.successfulEncodingDifferenceMass
#check @ReductionGames.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
#check @ReductionGames.gameThree
#check @ReductionGames.gameThreeObservation
#check @ReductionGames.gameFour
#check @ReductionGames.gameFourObservation
#check @ReductionGames.gameFourAdvantage
#check @ReductionGames.successfulSecondChainDifferenceMass
#check @ReductionGames.successfulGameFourMass
#check @ReductionGames.unusedGameFourMass
#check @ReductionGames.failedConsumedGameFourMass
#check @ReductionGames.nonSuccessGameFourMass
#check @ReductionGames.gameFourAdvantage_le_successful_add_nonSuccess
#check @ReductionGames.nonSuccessGameFourMass_le_unused_add_failedConsumed
#check @ReductionGames.gameFourObservation_unused
#check @ReductionGames.gameFourObservation_failedConsumed
#check @ReductionGames.gameFiveObservation_unused
#check @ReductionGames.gameFiveObservation_failedConsumed
#check @ReductionGames.gameFive
#check @ReductionGames.gameFiveObservation
#check @ReductionGames.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
#check @ReductionGames.guess_cardinality
#check @ReductionGames.guess_cardinality_le_paper_coefficient
#check @ReductionGames.gameFiveGuess_probability
#check @ReductionGames.gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
#check @ReductionGames.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
#check @ReductionGames.gameFourAdvantage_le_gameFive_add_unpaid_masses
#check @ReductionGames.NoMaximumOutput
#check @ReductionGames.findNonMaximumCoordinate
#check @ReductionGames.jointChainObservation
#check @ReductionGames.jointChainOutputMeasure
#check @ReductionGames.jointChainAdvantage
#check @ReductionGames.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
#check @ReductionGames.jointPRESelectedProgram
#check @ReductionGames.jointPRESelectedMass_le_preimageAdvantage
#check @ReductionGames.JointChainHybridReturnedMeasureBridge
#check @ReductionGames.gameSix
#check @ReductionGames.gameSixObservation
#check @ReductionGames.encodingConsumedEpoch_rejected
#check @ReductionGames.registeredIndex_lt_length_of_mem
#check @ReductionGames.registeredIndex_lookup_of_mem
#check @ReductionGames.registeredIndex_lt_capacity_of_mem
#check @ReductionGames.merkleTargetCollisionReduction
#check @ReductionGames.encodingTargetCollisionReduction
#check @ReductionGames.firstChainTargetCollisionReduction
#check @ReductionGames.secondChainTargetCollisionReduction
#check @ReductionGames.undetectabilityReduction
#check @ReductionGames.preimageReduction
#check @ReductionGames.jointUndetectabilityReduction
#check @ReductionGames.jointPreimageReduction
#check @ReductionGames.noMaximumOutput_of_two_codewords
#check @ReductionGames.jointChainAdvantage_le_jointUD_add_jointPRESelected
#check @ReductionGames.jointChainHybridReturnedMeasureBridge
#check @ReductionGames.jointChainAdvantage_le_jointUD_add_jointPRE
#check @Unforgeability.strong_unforgeability_reduction_bound_of_two_codewords

open Encoding ENNReal TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/- These importing examples pin the exact finite guess count, its paper coefficient bound,
and the actual native returned-measure successful-record Game 4→5 equality. -/
example : Fintype.card (ReductionGames.Guess h w v) =
    2 ^ h * v * (2 ^ w - 1) :=
  ReductionGames.guess_cardinality h w v

example : Fintype.card (ReductionGames.Guess h w v) ≤
    2 ^ h * v * 2 ^ w :=
  ReductionGames.guess_cardinality_le_paper_coefficient h w v

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.successfulGameFourMass hash enc K adv =
      (Fintype.card (ReductionGames.Guess h w v) : ℝ≥0∞) *
        ReductionGames.gameFiveAdvantage hash enc K hv hw adv :=
  ReductionGames.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
    hash enc K hv hw adv

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : ReductionGames.SchemeAdversary PP H M R h v)
    (hnonmax : ReductionGames.NoMaximumOutput enc) :
    ReductionGames.gameFourAdvantage hash enc K adv =
      (Fintype.card (ReductionGames.Guess h w v) : ℝ≥0∞) *
        ReductionGames.jointChainAdvantage hash enc K hv hw adv :=
  ReductionGames.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
    hash enc K hv hw adv hnonmax

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.gameFiveOutputMeasure hash enc K hv hw adv Set.univ =
      ReductionGames.gameFourOutputMeasure hash enc K adv Set.univ :=
  ReductionGames.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
    hash enc K hv hw adv

example [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.gameFourAdvantage hash enc K adv ≤
      (Fintype.card (ReductionGames.Guess h w v) : ℝ≥0∞) *
        ReductionGames.gameFiveAdvantage hash enc K hv hw adv +
          ReductionGames.unusedGameFourMass hash enc K adv +
            ReductionGames.failedConsumedGameFourMass hash enc K adv :=
  ReductionGames.gameFourAdvantage_le_gameFive_add_unpaid_masses
    hash enc K hv hw adv

/- Compiler origin and transitive axioms for the imported finite-guess theorems. The importing
examples above fix the proposition shape independently of the definition site. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let names := [
    ``ReductionGames.guess_cardinality,
    ``ReductionGames.guess_cardinality_le_paper_coefficient,
    ``ReductionGames.gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ,
    ``ReductionGames.gameFiveGuess_probability,
    ``ReductionGames.gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card,
    ``ReductionGames.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage,
    ``ReductionGames.gameFourAdvantage_le_gameFive_add_unpaid_masses,
    ``ReductionGames.jointChainGuess_probability,
    ``ReductionGames.jointChainAdvantage_eq_gameFourAdvantage_div_guess_card,
    ``ReductionGames.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage,
    ``ReductionGames.jointPRESelectedMass_le_preimageAdvantage]
  let env ← Lean.getEnv
  for name in names do
    let some constInfo := env.find? name
      | throwError "{name} is missing from the imported environment"
    let .thmInfo info := constInfo
      | throwError "{name} is not an imported theorem"
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "{name} has no imported-module origin"
    let header := env.header
    let origin := header.moduleNames[moduleIdx.toNat]!
    let expected :=
      if name == ``ReductionGames.jointPRESelectedMass_le_preimageAdvantage
      then `HashSig.GXMSS.Security.ReductionGames.JointReductions
      else `HashSig.GXMSS.Security.ReductionGames.GuessingGames
    unless origin == expected do
      throwError "{name} originates in {origin}, not {expected}"
    Lean.Meta.forallTelescope info.type fun _ result => do
      let resultType ← Lean.Meta.inferType result
      unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
        throwError "{name} is not a universally closed proposition"
    let axioms ← Lean.collectAxioms name
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
    Lean.logInfo m!"Imported finite-guess theorem {name} origin: {origin}"
    Lean.logInfo m!"Imported finite-guess theorem {name} axioms: {axioms.toList}"

/- These importing-module examples state the two exact new claims and must elaborate
using the imported theorems. The origin and axiom checks below audit their proof objects. -/
example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.successfulFirstChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (ReductionGames.firstChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.successful_first_chain_difference_le_target_collision_advantage
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.gameTwoAdvantage hash enc K adv ≤
      ReductionGames.gameThreeAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (ReductionGames.firstChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.game_two_le_game_three_add_first_chain_target_collision
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.successfulSecondChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (ReductionGames.secondChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.successful_second_chain_difference_le_target_collision_advantage
    hash enc K adv

example [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.gameThreeAdvantage hash enc K adv ≤
      ReductionGames.gameFourAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (ReductionGames.secondChainTargetCollisionReduction hash enc K adv) :=
  Unforgeability.game_three_le_game_four_add_second_chain_target_collision
    hash enc K adv

/- The imported theorem must prove the named proposition from this module with only the
project-approved transitive axioms. Keep this audit in an importing module so the compiler
origin is checked rather than inferred from source text. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``Unforgeability.first_merkle_target_collision_bound
  let env ← Lean.getEnv
  let some constInfo := env.find? name
    | throwError "{name} is missing from the imported environment"
  let .thmInfo info := constInfo
    | throwError "{name} is not an imported theorem"
  let some moduleIdx := env.getModuleIdxFor? name
    | throwError "{name} has no imported-module origin"
  let header := env.header
  let origin := header.moduleNames[moduleIdx.toNat]!
  unless origin == `HashSig.GXMSS.Security.Unforgeability.MerkleCollision do
    throwError "{name} originates in {origin}"
  Lean.Meta.forallTelescope info.type fun fvars result => do
    let levelParams := info.levelParams
    let levels := levelParams.map Lean.Level.param
    let expected := Lean.mkAppN
      (Lean.mkConst ``Unforgeability.FirstMerkleTargetCollisionBound levels) fvars
    unless (← Lean.Meta.isDefEq result expected) do
      throwError "{name} does not prove the exact named Merkle probability bound"
    let resultType ← Lean.Meta.inferType result
    unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
      throwError "{name} is not a universally closed proposition"
  let axioms ← Lean.collectAxioms name
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter fun ax => !allowed.contains ax
  unless unexpected.isEmpty do
    throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
  Lean.logInfo m!"Imported Merkle theorem origin: {origin}"
  Lean.logInfo m!"Imported Merkle theorem axioms: {axioms.toList}"

/- Audit the successor theorem from its imported module, independently of source text. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``Unforgeability.successful_encoding_target_collision_bound
  let env ← Lean.getEnv
  let some constInfo := env.find? name
    | throwError "{name} is missing from the imported environment"
  let .thmInfo info := constInfo
    | throwError "{name} is not an imported theorem"
  let some moduleIdx := env.getModuleIdxFor? name
    | throwError "{name} has no imported-module origin"
  let origin := env.header.moduleNames[moduleIdx.toNat]!
  unless origin == `HashSig.GXMSS.Security.Unforgeability.ReductionBound do
    throwError "{name} originates in {origin}"
  Lean.Meta.forallTelescope info.type fun fvars result => do
    let levels := info.levelParams.map Lean.Level.param
    let expected := Lean.mkAppN
      (Lean.mkConst ``Unforgeability.SuccessfulEncodingTargetCollisionBound levels) fvars
    unless (← Lean.Meta.isDefEq result expected) do
      throwError "{name} does not prove the exact named successful-record bound"
    let resultType ← Lean.Meta.inferType result
    unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
      throwError "{name} is not a universally closed proposition"
  let axioms ← Lean.collectAxioms name
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter fun ax => !allowed.contains ax
  unless unexpected.isEmpty do
    throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
  Lean.logInfo m!"Imported successful-record theorem origin: {origin}"
  Lean.logInfo m!"Imported successful-record theorem axioms: {axioms.toList}"

/- Audit both new first-chain theorems from the importing module. Their exact types are
printed above; this check rejects a changed compiler origin or unapproved transitive axiom. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let names := [
    ``Unforgeability.successful_first_chain_difference_le_target_collision_advantage,
    ``Unforgeability.game_two_le_game_three_add_first_chain_target_collision]
  let env ← Lean.getEnv
  for name in names do
    let some constInfo := env.find? name
      | throwError "{name} is missing from the imported environment"
    let .thmInfo info := constInfo
      | throwError "{name} is not an imported theorem"
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "{name} has no imported-module origin"
    let origin := env.header.moduleNames[moduleIdx.toNat]!
    unless origin == `HashSig.GXMSS.Security.Unforgeability.FirstChainCollision do
      throwError "{name} originates in {origin}"
    Lean.Meta.forallTelescope info.type fun _ result => do
      let resultType ← Lean.Meta.inferType result
      unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
        throwError "{name} is not a universally closed proposition"
    let axioms ← Lean.collectAxioms name
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
    Lean.logInfo m!"Imported first-chain theorem {name} origin: {origin}"
    Lean.logInfo m!"Imported first-chain theorem {name} axioms: {axioms.toList}"

/- The two second-chain theorem types elaborate above; audit their imported compiler origins and
full transitive axiom sets without relying on source-text searches. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let names := [
    ``Unforgeability.successful_second_chain_difference_le_target_collision_advantage,
    ``Unforgeability.game_three_le_game_four_add_second_chain_target_collision]
  let env ← Lean.getEnv
  for name in names do
    let some constInfo := env.find? name
      | throwError "{name} is missing from the imported environment"
    let .thmInfo info := constInfo
      | throwError "{name} is not an imported theorem"
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "{name} has no imported-module origin"
    let origin := env.header.moduleNames[moduleIdx.toNat]!
    unless origin == `HashSig.GXMSS.Security.Unforgeability.SecondChainCollision do
      throwError "{name} originates in {origin}"
    Lean.Meta.forallTelescope info.type fun _ result => do
      let resultType ← Lean.Meta.inferType result
      unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
        throwError "{name} is not a universally closed proposition"
    let axioms ← Lean.collectAxioms name
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
    Lean.logInfo m!"Imported second-chain theorem {name} origin: {origin}"
    Lean.logInfo m!"Imported second-chain theorem {name} axioms: {axioms.toList}"

/- Audit the conditional result and its joint accounting from this importing module. The
`#check` commands above print their exact elaborated theorem types. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let names := [
    ``ReductionGames.noMaximumOutput_of_two_codewords,
    ``ReductionGames.jointChainAdvantage_le_jointUD_add_jointPRESelected,
    ``ReductionGames.jointChainHybridReturnedMeasureBridge,
    ``ReductionGames.jointChainAdvantage_le_jointUD_add_jointPRE,
    ``Unforgeability.strong_unforgeability_reduction_bound_of_two_codewords]
  let env ← Lean.getEnv
  for name in names do
    let some constInfo := env.find? name
      | throwError "{name} is missing from the imported environment"
    let .thmInfo info := constInfo
      | throwError "{name} is not an imported theorem"
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "{name} has no imported-module origin"
    let origin := env.header.moduleNames[moduleIdx.toNat]!
    let expected :=
      if name == ``Unforgeability.strong_unforgeability_reduction_bound_of_two_codewords
      then `HashSig.GXMSS.Security.Unforgeability.ReductionBound
      else if name == ``ReductionGames.noMaximumOutput_of_two_codewords
      then `HashSig.GXMSS.Security.ReductionGames.GuessingGames
      else `HashSig.GXMSS.Security.ReductionGames.JointReductions
    unless origin == expected do
      throwError "{name} originates in {origin}, not {expected}"
    Lean.Meta.forallTelescope info.type fun _ result => do
      let resultType ← Lean.Meta.inferType result
      unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
        throwError "{name} is not a universally closed proposition"
    let axioms ← Lean.collectAxioms name
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
    Lean.logInfo m!"Imported conditional theorem {name} origin: {origin}"
    Lean.logInfo m!"Imported conditional theorem {name} axioms: {axioms.toList}"

/- Check the new encoding-specialized theorem origins and their complete transitive axioms. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let names := [
    ``Encoding.SpecializedUnforgeability.encoding_problem_eq,
    ``Encoding.SpecializedUnforgeability.strong_unforgeability_bound_of_bridge,
    ``Encoding.SpecializedUnforgeability.winternitz_strong_unforgeability_bound,
    ``Encoding.SpecializedUnforgeability.target_sum_strong_unforgeability_bound,
    ``Encoding.SpecializedUnforgeability.target_sum_strong_unforgeability_bound_of_small_target]
  let env ← Lean.getEnv
  for name in names do
    let some constInfo := env.find? name
      | throwError "{name} is missing from the imported environment"
    let .thmInfo info := constInfo
      | throwError "{name} is not an imported theorem"
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "{name} has no imported-module origin"
    let origin := env.header.moduleNames[moduleIdx.toNat]!
    unless origin == `HashSig.GXMSS.Security.EncodingSpecializedUnforgeability do
      throwError "{name} originates in {origin}, not the composition module"
    Lean.Meta.forallTelescope info.type fun _ result => do
      let resultType ← Lean.Meta.inferType result
      unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
        throwError "{name} is not a universally closed proposition"
    let axioms ← Lean.collectAxioms name
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
    Lean.logInfo m!"Imported encoding-specialized theorem {name} origin: {origin}"
    Lean.logInfo m!"Imported encoding-specialized theorem {name} axioms: {axioms.toList}"

end GXMSS.UnforgeabilityProbe
