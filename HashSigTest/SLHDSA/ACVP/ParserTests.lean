/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSigTest.SLHDSA.ACVP.Schema
public import Lean.Data.Json.Printer

/-!
# Runtime tests for the strict ACVP sample parser

The positive gate parses the committed NIST sample fixtures. The separate negative gate exercises
fail-closed syntax, schema, conditional-field, width, identifier, and pairing behavior. These tests
are parser/schema-format validation evidence only. They are not implementation-conformance
evidence, construction evidence, or security evidence.
-/

public section

namespace SLHDSA.Test.ACVP.ParserTests

open Lean
open SLHDSA.Test.ACVP

private def fixtureRoot : System.FilePath := "HashSigTest/SLHDSA/ACVP/fixtures"

private def requireOk {α : Type} (label : String) : Except String α → IO α
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: unexpected rejection: {error}"

private def requireError {α : Type} (label : String) : Except String α → IO Unit
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError s!"{label}: unexpectedly accepted"

private def nestedPair (path : System.FilePath) : IO (Prompt × Results) := do
  let source ← IO.FS.readFile path
  let fixture ← requireOk s!"{path}: projection fixture" (StrictJson.parse source)
  let object ← requireOk s!"{path}: projection object" <|
    fixture.getObj?.mapError (fun _ => "object expected")
  let some prompt := object.get? "prompt"
    | throw <| IO.userError s!"{path}: missing prompt"
  let some results := object.get? "expectedResults"
    | throw <| IO.userError s!"{path}: missing expectedResults"
  let projected := "{\"prompt\":" ++ prompt.compress ++
    ",\"expectedResults\":" ++ results.compress ++ "}"
  requireOk s!"{path}: wrapped pair" (parseWrappedPair projected)

private def zeros (bytes : Nat) : String := String.ofList (List.replicate (2 * bytes) '0')

private def keyGenGroup : String :=
  "{\"tgId\":1,\"testType\":\"AFT\",\"parameterSet\":\"SLH-DSA-SHA2-128s\",\"tests\":[{\"tcId\":1,\"skSeed\":\"" ++
    zeros 16 ++ "\",\"skPrf\":\"" ++ zeros 16 ++ "\",\"pkSeed\":\"" ++ zeros 16 ++ "\"}]}"

private def keyGenPrompt (groups : String := "[" ++ keyGenGroup ++ "]") : String :=
  "{\"vsId\":1,\"algorithm\":\"SLH-DSA\",\"mode\":\"keyGen\",\"revision\":\"FIPS205\",\"isSample\":true,\"testGroups\":" ++ groups ++ "}"

private def sigGenPrompt (contextBytes : Nat) (preHash : String := "pure")
    (hashField : String := "") (deterministic : Bool := true)
    (randomnessField : String := "") : String :=
  "{\"vsId\":1,\"algorithm\":\"SLH-DSA\",\"mode\":\"sigGen\",\"revision\":\"FIPS205\",\"isSample\":true,\"testGroups\":[{\"tgId\":1,\"testType\":\"AFT\",\"parameterSet\":\"SLH-DSA-SHA2-128s\",\"deterministic\":" ++
    (if deterministic then "true" else "false") ++ ",\"signatureInterface\":\"external\",\"preHash\":\"" ++
    preHash ++ "\",\"tests\":[{\"tcId\":1,\"sk\":\"" ++ zeros 64 ++
    "\",\"message\":\"00\",\"context\":\"" ++ zeros contextBytes ++ "\"" ++ hashField ++
    randomnessField ++ "}]}]}"

private def internalSigGenPrompt (testExtra : String := "") (groupExtra : String := "") : String :=
  "{\"vsId\":1,\"algorithm\":\"SLH-DSA\",\"mode\":\"sigGen\",\"revision\":\"FIPS205\",\"isSample\":true,\"testGroups\":[{\"tgId\":1,\"testType\":\"AFT\",\"parameterSet\":\"SLH-DSA-SHA2-128s\",\"deterministic\":true,\"signatureInterface\":\"internal\"" ++
    groupExtra ++ ",\"tests\":[{\"tcId\":1,\"sk\":\"" ++ zeros 64 ++
    "\",\"message\":\"00\"" ++ testExtra ++ "}]}]}"

private def sigVerPrompt (signatureBytes : Nat) : String :=
  "{\"vsId\":1,\"algorithm\":\"SLH-DSA\",\"mode\":\"sigVer\",\"revision\":\"FIPS205\",\"isSample\":true,\"testGroups\":[{\"tgId\":1,\"testType\":\"AFT\",\"parameterSet\":\"SLH-DSA-SHA2-128s\",\"signatureInterface\":\"external\",\"preHash\":\"pure\",\"tests\":[{\"tcId\":1,\"pk\":\"" ++
    zeros 32 ++ "\",\"message\":\"00\",\"context\":\"\",\"signature\":\"" ++
    zeros signatureBytes ++ "\"}]}]}"

private def keyGenResultGroup (tgId tcId : Nat) : String :=
  "{\"tgId\":" ++ toString tgId ++ ",\"tests\":[{\"tcId\":" ++ toString tcId ++
    ",\"pk\":\"" ++ zeros 32 ++ "\",\"sk\":\"" ++ zeros 64 ++ "\"}]}"

private def keyGenResults (groups : String := "[" ++ keyGenResultGroup 1 1 ++ "]") : String :=
  "{\"vsId\":1,\"algorithm\":\"SLH-DSA\",\"mode\":\"keyGen\",\"revision\":\"FIPS205\",\"isSample\":true,\"testGroups\":" ++
    groups ++ "}"

private def wrappedPair (prompt results : String) : String :=
  "{\"prompt\":" ++ prompt ++ ",\"expectedResults\":" ++ results ++ "}"

private def sigGenResults (signatureBytes : Nat) : String :=
  "{\"vsId\":1,\"algorithm\":\"SLH-DSA\",\"mode\":\"sigGen\",\"revision\":\"FIPS205\",\"isSample\":true,\"testGroups\":[{\"tgId\":1,\"tests\":[{\"tcId\":1,\"signature\":\"" ++
    zeros signatureBytes ++ "\"}]}]}"

private def sigVerResults (passed : Bool) : String :=
  "{\"vsId\":1,\"algorithm\":\"SLH-DSA\",\"mode\":\"sigVer\",\"revision\":\"FIPS205\",\"isSample\":true,\"testGroups\":[{\"tgId\":1,\"tests\":[{\"tcId\":1,\"testPassed\":" ++
    (if passed then "true" else "false") ++ "}]}]}"

private def runPositive : IO Nat := do
  let keyPrompt ← IO.FS.readFile (fixtureRoot / "keygen-prompt.json")
  let keyResults ← IO.FS.readFile (fixtureRoot / "keygen-expected.json")
  let _ ← requireOk "vendored keyGen pair" (parseAndValidate keyPrompt keyResults)
  let _ ← nestedPair (fixtureRoot / "siggen-schema-slice.json")
  let _ ← nestedPair (fixtureRoot / "sigver-schema-slice.json")
  let _ ← requireOk "255-byte context" (parsePrompt (sigGenPrompt 255))
  let hashes := ["SHA2-224", "SHA2-256", "SHA2-384", "SHA2-512", "SHA2-512/224",
    "SHA2-512/256", "SHA3-224", "SHA3-256", "SHA3-384", "SHA3-512", "SHAKE-128",
    "SHAKE-256"]
  for hash in hashes do
    let _ ← requireOk s!"advertised hash {hash}" <|
      parsePrompt (sigGenPrompt 0 "preHash" s!",\"hashAlg\":\"{hash}\"")
  IO.println "SLH-DSA ACVP parser positive suite: PASS (16 cases)"
  return 16

private def runNegative : IO Nat := do
  let valid := keyGenPrompt
  let failures : List (String × String) := [
    ("malformed JSON", "{"),
    ("non-object top level", "[]"),
    ("duplicate object key", valid.replace "\"vsId\":1" "\"vsId\":1,\"vsId\":1"),
    ("escaped-equivalent duplicate key", valid.replace "\"vsId\":1" "\"vsId\":1,\"vs\\u0049d\":1"),
    ("nested duplicate key", valid.replace "\"tcId\":1" "\"tcId\":1,\"tc\\u0049d\":1"),
    ("unknown key", valid.replace "\"isSample\":true" "\"isSample\":true,\"unknown\":0"),
    ("missing key", valid.replace ",\"revision\":\"FIPS205\"" ""),
    ("bad type", valid.replace "\"vsId\":1" "\"vsId\":\"1\""),
    ("bad algorithm", valid.replace "\"SLH-DSA\"" "\"SLH-DSA-X\""),
    ("bad mode", valid.replace "\"keyGen\"" "\"keygen\""),
    ("bad revision", valid.replace "\"FIPS205\"" "\"FIPS205-draft\""),
    ("not sample", valid.replace "\"isSample\":true" "\"isSample\":false"),
    ("bad enum", valid.replace "SLH-DSA-SHA2-128s" "SLH-DSA-SHA2-999s"),
    ("nonpositive vsId", valid.replace "\"vsId\":1" "\"vsId\":0"),
    ("nonpositive tgId", valid.replace "\"tgId\":1" "\"tgId\":0"),
    ("nonpositive tcId", valid.replace "\"tcId\":1" "\"tcId\":0"),
    ("empty groups", keyGenPrompt "[]"),
    ("empty tests", valid.replace ("[{\"tcId\":1,\"skSeed\":\"" ++ zeros 16 ++
      "\",\"skPrf\":\"" ++ zeros 16 ++ "\",\"pkSeed\":\"" ++ zeros 16 ++ "\"}]") "[]"),
    ("odd hex", valid.replace (zeros 16) "0"),
    ("non-hex", valid.replace (zeros 16) "gg"),
    ("wrong seed width", valid.replace (zeros 16) (zeros 15)),
    ("context 256", sigGenPrompt 256),
    ("pure with hashAlg", sigGenPrompt 0 "pure" ",\"hashAlg\":\"SHA2-256\""),
    ("preHash missing hashAlg", sigGenPrompt 0 "preHash"),
    ("deterministic with randomness", sigGenPrompt 0 "pure" "" true s!",\"additionalRandomness\":\"{zeros 16}\""),
    ("randomized missing randomness", sigGenPrompt 0 "pure" "" false)
  ]
  for (label, source) in failures do requireError label (parsePrompt source)
  requireError "wrapped duplicate prompt key" <| parseWrappedPair <|
    "{\"prompt\":" ++ valid ++ ",\"prompt\":" ++ valid ++
      ",\"expectedResults\":" ++ keyGenResults ++ "}"
  requireError "wrapped escaped-equivalent prompt key" <| parseWrappedPair <|
    "{\"prompt\":" ++ valid ++ ",\"prom\\u0070t\":" ++ valid ++
      ",\"expectedResults\":" ++ keyGenResults ++ "}"
  requireError "wrapped nested duplicate key" <| parseWrappedPair <| wrappedPair
    (valid.replace "\"vsId\":1" "\"vsId\":1,\"vsId\":1") keyGenResults
  requireError "wrapped unknown key" <| parseWrappedPair <|
    "{\"prompt\":" ++ valid ++ ",\"expectedResults\":" ++ keyGenResults ++
      ",\"unknown\":0}"
  requireError "wrapped missing expectedResults" <| parseWrappedPair <|
    "{\"prompt\":" ++ valid ++ "}"
  requireError "broken prompt/result vsId" <|
    parseAndValidate keyGenPrompt (keyGenResults.replace "\"vsId\":1" "\"vsId\":2")
  requireError "broken prompt/result tcId" <|
    parseAndValidate keyGenPrompt (keyGenResults.replace "\"tcId\":1" "\"tcId\":2")
  let duplicateTests := valid.replace "}]}]}" ("},{\"tcId\":1,\"skSeed\":\"" ++ zeros 16 ++
    "\",\"skPrf\":\"" ++ zeros 16 ++ "\",\"pkSeed\":\"" ++ zeros 16 ++ "\"}]}]}")
  requireError "duplicate tcId" (parsePrompt duplicateTests)
  requireError "duplicate tgId" (parsePrompt (keyGenPrompt ("[" ++ keyGenGroup ++ "," ++ keyGenGroup ++ "]")))
  let duplicateResultCase := "{\"tgId\":1,\"tests\":[{\"tcId\":1,\"pk\":\"" ++
    zeros 32 ++ "\",\"sk\":\"" ++ zeros 64 ++ "\"},{\"tcId\":1,\"pk\":\"" ++
    zeros 32 ++ "\",\"sk\":\"" ++ zeros 64 ++ "\"}]}"
  requireError "duplicate result tcId" (parseResults (keyGenResults ("[" ++ duplicateResultCase ++ "]")))
  requireError "duplicate result tgId" <| parseResults <|
    keyGenResults ("[" ++ keyGenResultGroup 1 1 ++ "," ++ keyGenResultGroup 1 2 ++ "]")
  requireError "omitted result group" (parseAndValidate keyGenPrompt (keyGenResults "[]"))
  requireError "extra result group" <| parseAndValidate keyGenPrompt <|
    keyGenResults ("[" ++ keyGenResultGroup 1 1 ++ "," ++ keyGenResultGroup 2 2 ++ "]")
  requireError "omitted result case" <| parseAndValidate keyGenPrompt <|
    keyGenResults "[{\"tgId\":1,\"tests\":[]}]"
  let extraResultCase := "{\"tgId\":1,\"tests\":[{\"tcId\":1,\"pk\":\"" ++
    zeros 32 ++ "\",\"sk\":\"" ++ zeros 64 ++ "\"},{\"tcId\":2,\"pk\":\"" ++
    zeros 32 ++ "\",\"sk\":\"" ++ zeros 64 ++ "\"}]}"
  requireError "extra result case" <| parseAndValidate keyGenPrompt <|
    keyGenResults ("[" ++ extraResultCase ++ "]")
  requireError "internal carries preHash" (parsePrompt (internalSigGenPrompt "" ",\"preHash\":\"pure\""))
  requireError "internal carries context" (parsePrompt (internalSigGenPrompt ",\"context\":\"\""))
  requireError "internal carries hashAlg" (parsePrompt (internalSigGenPrompt ",\"hashAlg\":\"SHA2-256\""))
  requireError "external missing preHash" (parsePrompt ((sigGenPrompt 0).replace ",\"preHash\":\"pure\"" ""))
  requireError "external missing context" (parsePrompt ((sigGenPrompt 0).replace ",\"context\":\"\"" ""))
  requireError "unknown hash enum" (parsePrompt (sigGenPrompt 0 "preHash" ",\"hashAlg\":\"SHA-999\""))
  requireError "wrong secret-key width" (parsePrompt ((sigGenPrompt 0).replace (zeros 64) (zeros 63)))
  requireError "wrong public-key width" (parsePrompt ((sigVerPrompt 7856).replace (zeros 32) (zeros 31)))
  requireError "wrong sigGen result width" (parseAndValidate (sigGenPrompt 0) (sigGenResults 7855))
  requireError "sigVer outside exact plus-or-minus one" (parsePrompt (sigVerPrompt 7854))
  requireError "positive sigVer with short signature" <|
    parseAndValidate (sigVerPrompt 7855) (sigVerResults true)
  IO.println "SLH-DSA ACVP parser negative suite: PASS (52 cases)"
  return 52

private def runAll : IO Unit := do
  let positive ← runPositive
  let negative ← runNegative
  IO.println s!"SLH-DSA ACVP parser runtime gate: PASS ({positive + negative} cases)"

end SLHDSA.Test.ACVP.ParserTests

/-- Run the positive and fail-closed negative ACVP parser gates. -/
def main : IO Unit := SLHDSA.Test.ACVP.ParserTests.runAll
