/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.Recovery.Contracts
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Unforgeability

/-! # Exact pure-wire recovery proofs

The strict pure-wire interpretation and named adversary reduction retain their complete
interfaces. Counted strong-forgery observations satisfy the original deterministic and hedged
bounds with the original context, seed distributions and query budgets.
-/

public section

open Lean Elab Command Meta SLHDSA.Refactor.R0

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let mainModule ← getMainModule
  for row in #[37, 38, 39, 40, 41] do
    let (_, levels, type) := goals[row - 1]!
    let suffix := if row == 37 then "wireSchemeInterpretation" else s!"row{row}"
    let userName := Name.str `HashSigTest.SLHDSA.Refactor.Recovery.Wire suffix
    let name := if row == 37 then userName else mkPrivateNameCore mainModule userName
    if ((← getEnv).find? name).isSome then throwError "Duplicate wire recovery witness"
    let value ← if row == 37 || row == 38 then
      pure (mkConst (if row == 37 then `SLHDSA.Security.wireShakeScheme_map_shakeAnswer
        else `SLHDSA.Security.romQueryBound_wireReduce) (levels.map Level.param))
    else liftTermElabM do
      Term.withoutErrToSorry do
        let proof ← if row == 39 then `(by
          classical
          intro vp ctx optRand pkSeedDist adv C _ policy
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage,
            SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          simpa only [SLHDSA.Security.shakeStrongAdvantage_def] using
            (SLHDSA.Security.wireStrongAdvantage_le vp ctx adv))
        else if row == 40 then `(by
          classical
          intro set ctx optRand adv qh qs hadv C _ policy
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          exact SLHDSA.Security.wireStrongAdvantage_le_securityBound_validatedParams
            set ctx adv hadv)
        else `(by
          classical
          intro set ctx adv qh qs hadv C _ policy
          unfold P5Continuation.F4.totalSufAdvantage P5Continuation.F4.totalSufProgram
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage]
          exact SLHDSA.Security.wireStrongAdvantage_le_securityBound_hedged_validatedParams
            set ctx adv hadv)
        let result ← Term.elabTermEnsuringType proof (some type)
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars result
    if value.hasLooseBVars || value.hasFVar || value.hasMVar || value.hasLevelMVar then
      throwError "Wire recovery proof is not closed"
    if value.getUsedConstantsAsSet.contains `sorryAx then
      throwError "Wire recovery contains sorryAx"
    if (← MonadLog.hasErrors) then throwError "Wire recovery elaboration recorded errors"
    liftCoreM <| addAndCompile (.thmDecl {
      name := name
      levelParams := levels
      type := type
      value := value
    })
    addDocStringCore name (if row == 37 then
      "The strict pure-wire scheme interpreted by the concrete SHAKE answer implementation."
      else "An exact quantified pure-wire recovery with the original context and budgets.")
    let .thmInfo actual ← getConstInfo name | throwError "Expected checked wire recovery theorem"
    unless (← ofExcept (encodeExpr actual.type)) == (← ofExcept (encodeExpr type)) &&
        actual.levelParams == levels do
      throwError "Actual wire recovery type or raw universe parameters changed"
  logInfo "FIVE_WIRE_RECOVERY_WITNESSES_CREATED_NATIVE_EXIT_REQUIRED"
