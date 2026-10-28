/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.Recovery.Contracts
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Unforgeability

/-! # Exact public-seed security recoveries

Counted forgery observations retain the original public-seed, weak-key and randomizer bounds.
The averaged bound keeps its uncounted per-seed hypothesis and the original seed distribution.
Ordinary and strong unforgeability use their separate observation identities.
-/

public section

open Lean Elab Command Meta SLHDSA.Refactor.R0

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let mainModule ← getMainModule
  for row in #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 33, 34] do
    let (_, levels, type) := goals[row - 1]!
    let suffix := if row == 34 then "countedSeedAverage" else s!"row{row}"
    let userName := Name.str `HashSigTest.SLHDSA.Refactor.Recovery.SeedBounds suffix
    let name := if row == 34 then userName else mkPrivateNameCore mainModule userName
    if ((← getEnv).find? name).isSome then throwError "Duplicate public-seed recovery witness"
    let value ← liftTermElabM do
      Term.withoutErrToSorry do
        let proof ← if row == 4 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound
          all_goals assumption)
        else if row == 5 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero
          all_goals assumption)
        else if row == 6 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32
          all_goals assumption)
        else if row == 7 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_prEvent_optRand_le
          all_goals assumption)
        else if row == 8 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged
          all_goals assumption)
        else if row == 9 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32
          all_goals assumption)
        else if row == 10 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_min_of_n_eq_32
          all_goals assumption)
        else if row == 11 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32
          all_goals assumption)
        else if row == 12 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_weakKeyMass_mul
          all_goals assumption)
        else if row == 13 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply
            SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_add_weakKeyMass_mul
          all_goals assumption)
        else if row == 14 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_le_securityBound
          all_goals assumption)
        else if row == 15 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged
          all_goals assumption)
        else if row == 16 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_le_securityBound_of_n_eq_32
          all_goals assumption)
        else if row == 17 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          rw [← SLHDSA.Security.shakeStrongAdvantage_def]
          apply SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_of_n_eq_32
          all_goals assumption)
        else if row == 33 then `(by
          classical
          intro vp optRand pkSeedDist adv C _ policy
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
            P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage,
            SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          simpa only [SLHDSA.Security.shakeAdvantage_def,
            SLHDSA.Security.shakeStrongAdvantage_def] using
            (SLHDSA.Security.shakeAdvantage_le_shakeStrongAdvantage adv))
        else `(by
          classical
          intro vp _ _ optRand pkSeedDist β qh qs h adv hadv C _ policy
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          simpa only [SLHDSA.Security.shakeStrongAdvantage_def] using
            (SLHDSA.Security.shakeStrongAdvantage_le_lintegral pkSeedDist β h adv hadv))
        let result ← Term.elabTermEnsuringType proof (some type)
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars result
    if value.hasLooseBVars || value.hasFVar || value.hasMVar || value.hasLevelMVar then
      throwError "Public-seed recovery proof is not closed"
    if value.getUsedConstantsAsSet.contains `sorryAx then
      throwError "Public-seed recovery contains sorryAx"
    if (← MonadLog.hasErrors) then throwError "Public-seed recovery elaboration recorded errors"
    liftCoreM <| addAndCompile (.thmDecl {
      name := name
      levelParams := levels
      type := type
      value := value
    })
    addDocStringCore name (if row == 34 then
      "The original public-seed average for the counted strong-forgery observation."
      else "An exact quantified public-seed security bound under the original assumptions.")
    let .thmInfo actual ← getConstInfo name |
      throwError "Expected checked public-seed recovery theorem"
    unless (← ofExcept (encodeExpr actual.type)) == (← ofExcept (encodeExpr type)) &&
        actual.levelParams == levels do
      throwError "Actual public-seed recovery type or raw universe parameters changed"
  logInfo "SIXTEEN_PUBLIC_SEED_RECOVERY_WITNESSES_CREATED_NATIVE_EXIT_REQUIRED"
