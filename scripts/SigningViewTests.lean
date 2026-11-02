/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import VCVioTest.CryptoFoundations.SigningViewCounted
import VCVioTest.QueryTracking.RandomOraclePresampling
import VCVioTest.CryptoFoundations.SigningViewEncoding
import VCVioTest.CryptoFoundations.SigningViewUniverse
import VCVioTest.CryptoFoundations.SigningViewUnforgeability
import HashSigTest.SLHDSA.Refactor.SigningViewContext
public import HashSigTest.SLHDSA.Refactor.Recovery.General
public import HashSigTest.SLHDSA.Refactor.Recovery.Wire
public import HashSigTest.SLHDSA.Refactor.Recovery.SeedBounds
public import HashSigTest.SLHDSA.Refactor.Recovery.Approved
public import HashSigTest.SLHDSA.Refactor.Recovery.Generic

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

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let (_, levels, type) := goals[33]!
  let proofName ← resolveGlobalConstNoOverloadCore
    `HashSigTest.SLHDSA.Refactor.Recovery.SeedBounds.countedSeedAverage
  unless proofName == `HashSigTest.SLHDSA.Refactor.Recovery.SeedBounds.countedSeedAverage &&
      !isPrivateName proofName && levels.isEmpty do
    throwError "The ordinary seed average is not the expected public theorem"
  let info ← getConstInfo proofName
  unless (← ofExcept (encodeExpr info.type)) == (← ofExcept (encodeExpr type)) &&
      info.levelParams == levels do
    throwError "The ordinary seed-average consumer has a different complete type"
  unless owner (← getEnv) proofName == some `HashSigTest.SLHDSA.Refactor.Recovery.SeedBounds do
    throwError "The ordinary seed-average recovery owner changed"
  let name := mkPrivateNameCore (← getMainModule) `SigningViewTests.countedSeedAverage
  if ((← getEnv).find? name).isSome then throwError "Duplicate ordinary seed-average consumer"
  liftCoreM <| addAndCompile (.thmDecl {
    name := name
    levelParams := levels
    type := type
    value := mkConst proofName []
  })
  addDocStringCore name
    "An ordinary complete-type proof consumer of the counted public-seed average."

run_cmd do
  let goals ← SLHDSA.Refactor.Recovery.Contracts.readGoals
  let (_, levels, type) := goals[41]!
  let proofName ← resolveGlobalConstNoOverloadCore
    `HashSigTest.SLHDSA.Refactor.Recovery.Approved.countedProfileBound
  unless proofName == `HashSigTest.SLHDSA.Refactor.Recovery.Approved.countedProfileBound &&
      !isPrivateName proofName && levels.isEmpty do
    throwError "The ordinary profile bound is not the expected public theorem"
  let info ← getConstInfo proofName
  unless (← ofExcept (encodeExpr info.type)) == (← ofExcept (encodeExpr type)) &&
      info.levelParams == levels do
    throwError "The ordinary profile-bound consumer has a different complete type"
  unless owner (← getEnv) proofName == some `HashSigTest.SLHDSA.Refactor.Recovery.Approved do
    throwError "The ordinary profile-bound recovery owner changed"
  let name := mkPrivateNameCore (← getMainModule) `SigningViewTests.countedProfileBound
  if ((← getEnv).find? name).isSome then throwError "Duplicate ordinary profile-bound consumer"
  liftCoreM <| addAndCompile (.thmDecl {
    name := name
    levelParams := levels
    type := type
    value := mkConst proofName []
  })
  addDocStringCore name
    "An ordinary complete-type proof consumer of the counted pure SHAKE profile bound."

run_cmd do
  let (levels, type) ← HashSigTest.SLHDSA.Refactor.Recovery.Generic.readGoal
  let proofName ← resolveGlobalConstNoOverloadCore
    `HashSigTest.SLHDSA.Refactor.Recovery.Generic.genericCounted36
  unless proofName == `HashSigTest.SLHDSA.Refactor.Recovery.Generic.genericCounted36 &&
      !isPrivateName proofName && levels == [`i, `r] do
    throwError "The ordinary generic counted theorem or raw universes changed"
  let info ← getConstInfo proofName
  unless (← ofExcept (encodeExpr info.type)) == (← ofExcept (encodeExpr type)) &&
      info.levelParams == levels do
    throwError "The ordinary generic counted theorem has a different complete type"
  unless owner (← getEnv) proofName == some `HashSigTest.SLHDSA.Refactor.Recovery.Generic do
    throwError "The ordinary generic counted theorem owner changed"
  let clients : Array (Name × List Name × List Level) := #[
    (`SigningViewTests.genericCounted36, levels, levels.map Level.param),
    (`SigningViewTests.genericCounted36Higher, [], [Level.ofNat 1, Level.ofNat 2]),
    (`SigningViewTests.genericCounted36Type0, [], [.zero, .zero])]
  for (userName, clientLevels, arguments) in clients do
    let name := mkPrivateNameCore (← getMainModule) userName
    if ((← getEnv).find? name).isSome then throwError "Duplicate ordinary generic counted client"
    liftCoreM <| addAndCompile (.thmDecl {
      name := name
      levelParams := clientLevels
      type := type.instantiateLevelParams levels arguments
      value := mkConst proofName arguments
    })
    addDocStringCore name
      "An ordinary complete-type proof consumer of generic counted unforgeability domination."

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
  VCVioTest.QueryTracking.RandomOraclePresampling.run complete
  let expected := ["f4-unforgeability", "f5-context", "f6-fixture", "c3-presampling"]
  unless (← completed.get) == expected do
    throw (IO.userError "Signing-view completion mismatch")
