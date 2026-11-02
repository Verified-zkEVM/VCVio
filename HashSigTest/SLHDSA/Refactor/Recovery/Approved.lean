/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.Recovery.Contracts
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Unforgeability

/-! # Exact approved-parameter security recoveries

The approved-parameter strong and ordinary bounds retain their original seed and randomizer
assumptions and numerical expressions. Pure SHAKE profiles keep the same algorithm, context,
signing mode and rational bound evaluator under the counted strong-forgery observation.
-/

public section

open Lean Elab Command Meta SLHDSA.Refactor.R0

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let mainModule ← getMainModule
  for row in #[18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 42] do
    let (_, levels, type) := goals[row - 1]!
    let suffix := if row == 42 then "countedProfileBound" else s!"row{row}"
    let userName := Name.str `HashSigTest.SLHDSA.Refactor.Recovery.Approved suffix
    let name := if row == 42 then userName else mkPrivateNameCore mainModule userName
    if ((← getEnv).find? name).isSome then throwError "Duplicate approved recovery witness"
    let value ← liftTermElabM do
      Term.withoutErrToSorry do
        let proof ← if row == 18 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply
            SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_validatedParams
          all_goals assumption)
        else if row == 19 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply
            SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams
          all_goals assumption)
        else if row == 20 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply
            SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_validatedParams
          all_goals assumption)
        else if row == 21 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply
            SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams
          all_goals assumption)
        else if row == 22 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply
            SLHDSA.Security.shakeStrongAdvantage_le_securityBound_validatedParams
          all_goals assumption)
        else if row == 23 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply
            SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_validatedParams
          all_goals assumption)
        else if row == 24 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_pure_le_securityBound
          all_goals assumption)
        else if row == 25 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_le_securityBound
          all_goals assumption)
        else if row == 26 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_le_securityBound_hedged
          all_goals assumption)
        else if row == 27 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_pure_le_securityBound_validatedParams
          all_goals assumption)
        else if row == 28 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_pure_le_securityBound_hedged_validatedParams
          all_goals assumption)
        else if row == 29 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_pure_le_securityBound_add_validatedParams
          all_goals assumption)
        else if row == 30 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_pure_le_securityBound_add_hedged_validatedParams
          all_goals assumption)
        else if row == 31 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_le_securityBound_validatedParams
          all_goals assumption)
        else if row == 32 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeAdvantage_def]
          apply
            SLHDSA.Security.shakeAdvantage_le_securityBound_hedged_validatedParams
          all_goals assumption)
        else `(by
          classical
          intro profile adv qh qs hadv C _ policy
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          exact SLHDSA.Security.ShakeProfile.strongUnforgeableAdvantage_le_boundEvaluator
            profile adv hadv)
        let result ← Term.elabTermEnsuringType proof (some type)
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars result
    if value.hasLooseBVars || value.hasFVar || value.hasMVar || value.hasLevelMVar then
      throwError "Approved recovery proof is not closed"
    if value.getUsedConstantsAsSet.contains `sorryAx then
      throwError "Approved recovery contains sorryAx"
    if (← MonadLog.hasErrors) then throwError "Approved recovery elaboration recorded errors"
    liftCoreM <| addAndCompile (.thmDecl {
      name := name
      levelParams := levels
      type := type
      value := value
    })
    addDocStringCore name (if row == 42 then
      "The original pure SHAKE profile bound under the counted strong-forgery observation."
      else "An exact quantified approved-parameter bound under the original assumptions.")
    let .thmInfo actual ← getConstInfo name |
      throwError "Expected checked approved recovery theorem"
    unless (← ofExcept (encodeExpr actual.type)) == (← ofExcept (encodeExpr type)) &&
        actual.levelParams == levels do
      throwError "Actual approved recovery type or raw universe parameters changed"
  logInfo "SIXTEEN_APPROVED_RECOVERY_WITNESSES_CREATED_NATIVE_EXIT_REQUIRED"
