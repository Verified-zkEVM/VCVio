/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.Recovery.Contracts
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Unforgeability

/-! # Exact random-oracle recovery proofs

The counted observations satisfy the original security bounds with the original assumptions
and query limits. The message-freshness and pair-freshness observations remain distinct.
-/

public section

open Lean Elab Command Meta SLHDSA.Refactor.R0

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let mainModule ← getMainModule
  for row in #[1, 2, 3, 35, 36] do
    let (_, levels, type) := goals[row - 1]!
    let suffix := if row == 1 then "countedRomBound" else if row == 36 then "legacy36"
      else s!"row{row}"
    let userName := Name.str `HashSigTest.SLHDSA.Refactor.Recovery.General suffix
    let name := if row == 1 then userName else mkPrivateNameCore mainModule userName
    if ((← getEnv).find? name).isSome then throwError "Duplicate recovery witness"
    let value ← if row == 36 then
      pure (mkConst `SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage
        (levels.map Level.param))
    else liftTermElabM do
      Term.withoutErrToSorry do
        let proof ← if row == 1 then `(by
          classical
          intro vp core _ _ _ _ _ _ _ _ laws hd hcard e optRand pkSeed adv qh qs hadv C _ policy
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          exact SLHDSA.Security.strongUnforgeableAdvantage_romScheme_pure_le_securityBound
            laws hd hcard e optRand pkSeed hadv)
        else if row == 2 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          apply SLHDSA.Security.securityTarget_two_one <;> assumption)
        else if row == 3 then `(by
          classical
          intros
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          apply SLHDSA.Security.strongUnforgeableAdvantage_romScheme_le_securityBound <;>
            assumption)
        else `(by
          classical
          intros
          unfold P5Continuation.F4.totalEufAdvantage P5Continuation.F4.totalEufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage]
          apply SLHDSA.Security.unforgeableAdvantage_romScheme_le <;> assumption)
        let result ← Term.elabTermEnsuringType proof (some type)
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars result
    if value.hasLooseBVars || value.hasFVar || value.hasMVar || value.hasLevelMVar then
      throwError "Recovery proof is not closed"
    if value.getUsedConstantsAsSet.contains `sorryAx then throwError "Recovery contains sorryAx"
    if (← MonadLog.hasErrors) then throwError "Recovery elaboration recorded errors"
    liftCoreM <| addAndCompile (.thmDecl { name, levelParams := levels, type, value })
    addDocStringCore name (if row == 1 then
      "The original random-oracle security bound for the counted total-signature observation."
      else "An exact quantified security recovery under the original runtime and premises.")
    let .thmInfo actual ← getConstInfo name | throwError "Expected checked recovery theorem"
    unless (← ofExcept (encodeExpr actual.type)) == (← ofExcept (encodeExpr type)) &&
        actual.levelParams == levels do
      throwError "Actual recovery type or raw universe parameters changed"
  logInfo "FIVE_GENERAL_RECOVERY_WITNESSES_CREATED_NATIVE_EXIT_REQUIRED"
