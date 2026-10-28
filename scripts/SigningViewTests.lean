/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import VCVioTest.CryptoFoundations.SigningViewCounted
import VCVioTest.CryptoFoundations.SigningViewEncoding
import VCVioTest.CryptoFoundations.SigningViewUniverse
import VCVioTest.CryptoFoundations.SigningViewUnforgeability
import HashSigTest.SLHDSA.Refactor.SigningViewContext
public import HashSigTest.SLHDSA.Refactor.Recovery.General
public import HashSigTest.SLHDSA.Refactor.Recovery.Wire

/-! # Executable signing-view observation checks -/

open Lean Elab Command SLHDSA.Refactor.R0

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let (_, levels, type) := goals[0]!
  let proofName ← resolveGlobalConstNoOverloadCore
    `HashSigTest.SLHDSA.Refactor.Recovery.General.countedRomBound
  unless proofName == `HashSigTest.SLHDSA.Refactor.Recovery.General.countedRomBound &&
      !isPrivateName proofName && levels.isEmpty do
    throwError "The ordinary General recovery is not the expected public theorem"
  let info ← getConstInfo proofName
  unless (← ofExcept (encodeExpr info.type)) == (← ofExcept (encodeExpr type)) &&
      info.levelParams == levels do
    throwError "The ordinary General consumer has a different complete type"
  unless owner (← getEnv) proofName == some `HashSigTest.SLHDSA.Refactor.Recovery.General do
    throwError "The ordinary General recovery owner changed"
  let name := mkPrivateNameCore (← getMainModule) `SigningViewTests.countedRomBound
  if ((← getEnv).find? name).isSome then throwError "Duplicate ordinary General consumer"
  liftCoreM <| addAndCompile (.thmDecl
    { name, levelParams := levels, type, value := mkConst proofName [] })
  addDocStringCore name
    "An ordinary complete-type proof consumer of the counted random-oracle bound."

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let (_, levels, type) := goals[36]!
  let proofName ← resolveGlobalConstNoOverloadCore
    `HashSigTest.SLHDSA.Refactor.Recovery.Wire.wireSchemeInterpretation
  unless proofName == `HashSigTest.SLHDSA.Refactor.Recovery.Wire.wireSchemeInterpretation &&
      !isPrivateName proofName && levels.isEmpty do
    throwError "The ordinary wire interpretation is not the expected public theorem"
  let info ← getConstInfo proofName
  unless (← ofExcept (encodeExpr info.type)) == (← ofExcept (encodeExpr type)) &&
      info.levelParams == levels do
    throwError "The ordinary wire consumer has a different complete type"
  unless owner (← getEnv) proofName == some `HashSigTest.SLHDSA.Refactor.Recovery.Wire do
    throwError "The ordinary wire interpretation owner changed"
  let name := mkPrivateNameCore (← getMainModule) `SigningViewTests.wireSchemeInterpretation
  if ((← getEnv).find? name).isSome then throwError "Duplicate ordinary wire consumer"
  liftCoreM <| addAndCompile (.thmDecl {
    name := name
    levelParams := levels
    type := type
    value := mkConst proofName []
  })
  addDocStringCore name
    "An ordinary complete-type proof consumer of the strict pure-wire interpretation."

/-- Run the signing-view observation checks. -/
public def main : IO Unit := do
  VCVioTest.CryptoFoundations.SigningViewCounted.run
  VCVioTest.CryptoFoundations.SigningViewEncoding.run
  VCVioTest.CryptoFoundations.SigningViewUniverse.run
  let completed ← IO.mkRef ([] : List String)
  let complete : String → IO Unit := fun token => completed.modify (· ++ [token])
  VCVioTest.CryptoFoundations.SigningViewUnforgeability.run complete
  SLHDSA.Refactor.SigningViewContext.run complete
  SLHDSA.Refactor.Recovery.Contracts.auditFixture complete
  let expected := ["f4-unforgeability", "f5-context", "f6-fixture"]
  unless (← completed.get) == expected do
    throw (IO.userError "Signing-view completion mismatch")
