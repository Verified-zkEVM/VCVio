/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSigTest.SLHDSA.ACVP.StrictJson

/-!
# Strict ACVP SLH-DSA sample schema

Typed, fail-closed parsing for the pinned `FIPS205` keyGen, sigGen, and sigVer sample JSON. This is
test support and provenance infrastructure, not a construction or security statement.
-/

public section

namespace SLHDSA.Test.ACVP

open Lean

inductive Mode where
  | keyGen | sigGen | sigVer
  deriving BEq, Repr

inductive SignatureInterface where
  | internal | external
  deriving BEq, Repr

inductive PreHash where
  | pure | preHash
  deriving BEq, Repr

inductive HashAlg where
  | sha2_224 | sha2_256 | sha2_384 | sha2_512 | sha2_512_224 | sha2_512_256
  | sha3_224 | sha3_256 | sha3_384 | sha3_512 | shake128 | shake256
  deriving BEq, Repr

/-- Test-only copy of one exact FIPS 205 Table-2 row. -/
structure ParamInfo where
  name : String
  family : String
  n : Nat
  h : Nat
  d : Nat
  hp : Nat
  a : Nat
  k : Nat
  lgw : Nat
  m : Nat
  category : Nat
  publicKeyBytes : Nat
  secretKeyBytes : Nat
  signatureBytes : Nat
  deriving BEq, Repr

/-- The exact twelve FIPS 205 Table-2 rows, used only to validate sample widths and names. -/
def parameterSets : Array ParamInfo := #[
  ⟨"SLH-DSA-SHA2-128s", "SHA2", 16, 63, 7, 9, 12, 14, 4, 30, 1, 32, 64, 7856⟩,
  ⟨"SLH-DSA-SHAKE-128s", "SHAKE", 16, 63, 7, 9, 12, 14, 4, 30, 1, 32, 64, 7856⟩,
  ⟨"SLH-DSA-SHA2-128f", "SHA2", 16, 66, 22, 3, 6, 33, 4, 34, 1, 32, 64, 17088⟩,
  ⟨"SLH-DSA-SHAKE-128f", "SHAKE", 16, 66, 22, 3, 6, 33, 4, 34, 1, 32, 64, 17088⟩,
  ⟨"SLH-DSA-SHA2-192s", "SHA2", 24, 63, 7, 9, 14, 17, 4, 39, 3, 48, 96, 16224⟩,
  ⟨"SLH-DSA-SHAKE-192s", "SHAKE", 24, 63, 7, 9, 14, 17, 4, 39, 3, 48, 96, 16224⟩,
  ⟨"SLH-DSA-SHA2-192f", "SHA2", 24, 66, 22, 3, 8, 33, 4, 42, 3, 48, 96, 35664⟩,
  ⟨"SLH-DSA-SHAKE-192f", "SHAKE", 24, 66, 22, 3, 8, 33, 4, 42, 3, 48, 96, 35664⟩,
  ⟨"SLH-DSA-SHA2-256s", "SHA2", 32, 64, 8, 8, 14, 22, 4, 47, 5, 64, 128, 29792⟩,
  ⟨"SLH-DSA-SHAKE-256s", "SHAKE", 32, 64, 8, 8, 14, 22, 4, 47, 5, 64, 128, 29792⟩,
  ⟨"SLH-DSA-SHA2-256f", "SHA2", 32, 68, 17, 4, 9, 35, 4, 49, 5, 64, 128, 49856⟩,
  ⟨"SLH-DSA-SHAKE-256f", "SHAKE", 32, 68, 17, 4, 9, 35, 4, 49, 5, 64, 128, 49856⟩
]

inductive PromptPayload where
  | keyGen (skSeed skPrf pkSeed : ByteArray)
  | sigGen (sk message : ByteArray) (context : Option ByteArray)
      (hashAlg : Option HashAlg) (additionalRandomness : Option ByteArray)
  | sigVer (pk message : ByteArray) (context : Option ByteArray)
      (hashAlg : Option HashAlg) (signature : ByteArray)
  deriving BEq

structure PromptTest where
  tcId : Nat
  payload : PromptPayload
  deriving BEq

structure PromptGroup where
  tgId : Nat
  parameter : ParamInfo
  signatureInterface : Option SignatureInterface := none
  preHash : Option PreHash := none
  deterministic : Option Bool := none
  tests : Array PromptTest
  deriving BEq

structure Prompt where
  vsId : Nat
  mode : Mode
  groups : Array PromptGroup
  deriving BEq

inductive ResultPayload where
  | keyGen (pk sk : ByteArray)
  | sigGen (signature : ByteArray)
  | sigVer (passed : Bool)
  deriving BEq

structure ResultTest where
  tcId : Nat
  payload : ResultPayload
  deriving BEq

structure ResultGroup where
  tgId : Nat
  tests : Array ResultTest
  deriving BEq

structure Results where
  vsId : Nat
  mode : Mode
  groups : Array ResultGroup
  deriving BEq

abbrev Object := Std.TreeMap.Raw String Json compare

private def fail {α : Type} (message : String) : Except String α := .error message

private def objectSize (object : Object) : Nat :=
  object.foldl (init := 0) fun size _ _ => size + 1

private def requireKeys (label : String) (object : Object) (keys : List String) :
    Except String Unit := do
  if objectSize object != keys.length then
    fail s!"{label}: unexpected or missing object key"
  for key in keys do
    if !object.contains key then
      fail s!"{label}: missing key {key}"

private def field (label : String) (object : Object) (key : String) : Except String Json :=
  match object.get? key with
  | some value => .ok value
  | none => fail s!"{label}: missing key {key}"

private def asObject (label : String) (value : Json) : Except String Object :=
  value.getObj?.mapError (fun _ => s!"{label}: object expected")

private def asArray (label : String) (value : Json) : Except String (Array Json) :=
  value.getArr?.mapError (fun _ => s!"{label}: array expected")

private def asString (label : String) (value : Json) : Except String String :=
  value.getStr?.mapError (fun _ => s!"{label}: string expected")

private def asNat (label : String) (value : Json) : Except String Nat :=
  value.getNat?.mapError (fun _ => s!"{label}: natural number expected")

private def asBool (label : String) (value : Json) : Except String Bool :=
  value.getBool?.mapError (fun _ => s!"{label}: boolean expected")

private def positiveId (label : String) (value : Json) : Except String Nat := do
  let id ← asNat label value
  if id == 0 then fail s!"{label}: identifier must be positive"
  return id

private def parseMode : String → Except String Mode
  | "keyGen" => .ok .keyGen
  | "sigGen" => .ok .sigGen
  | "sigVer" => .ok .sigVer
  | other => fail s!"unsupported mode {other}"

private def parseInterface : String → Except String SignatureInterface
  | "internal" => .ok .internal
  | "external" => .ok .external
  | other => fail s!"unsupported signatureInterface {other}"

private def parsePreHash : String → Except String PreHash
  | "pure" => .ok .pure
  | "preHash" => .ok .preHash
  | other => fail s!"unsupported preHash {other}"

private def parseHashAlg : String → Except String HashAlg
  | "SHA2-224" => .ok .sha2_224
  | "SHA2-256" => .ok .sha2_256
  | "SHA2-384" => .ok .sha2_384
  | "SHA2-512" => .ok .sha2_512
  | "SHA2-512/224" => .ok .sha2_512_224
  | "SHA2-512/256" => .ok .sha2_512_256
  | "SHA3-224" => .ok .sha3_224
  | "SHA3-256" => .ok .sha3_256
  | "SHA3-384" => .ok .sha3_384
  | "SHA3-512" => .ok .sha3_512
  | "SHAKE-128" => .ok .shake128
  | "SHAKE-256" => .ok .shake256
  | other => fail s!"unsupported hashAlg {other}"

private def parameterByName (name : String) : Except String ParamInfo :=
  match parameterSets.find? (·.name == name) with
  | some info => .ok info
  | none => fail s!"unsupported parameterSet {name}"

private def hexNibble (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private def decodeHexAux (label : String) : List Char → ByteArray → Except String ByteArray
  | [], bytes => pure bytes
  | high :: low :: rest, bytes => do
      let some highNibble := hexNibble high | fail s!"{label}: non-hex character"
      let some lowNibble := hexNibble low | fail s!"{label}: non-hex character"
      decodeHexAux label rest (bytes.push (UInt8.ofNat (16 * highNibble + lowNibble)))
  | [_], _ => fail s!"{label}: odd-length hex"

private def hexBytes (label value : String) : Except String ByteArray :=
  decodeHexAux label value.toList ByteArray.empty

private def exactHex (label : String) (value : Json) (bytes : Nat) : Except String ByteArray := do
  let decoded ← hexBytes label (← asString label value)
  if decoded.size != bytes then fail s!"{label}: expected {bytes} bytes, got {decoded.size}"
  return decoded

private def boundedHex (label : String) (value : Json) (maximum : Nat) : Except String ByteArray := do
  let decoded ← hexBytes label (← asString label value)
  if decoded.size > maximum then fail s!"{label}: exceeds {maximum} bytes"
  return decoded

private def messageHex (value : Json) : Except String ByteArray := do
  let message ← boundedHex "message" value 8192
  if message.isEmpty then fail "message: at least one byte required"
  return message

private def parseCommonTop (json : Json) : Except String (Object × Nat × Mode) := do
  let object ← asObject "vector set" json
  requireKeys "vector set" object ["vsId", "algorithm", "mode", "revision", "isSample", "testGroups"]
  if (← asString "algorithm" (← field "vector set" object "algorithm")) != "SLH-DSA" then
    fail "algorithm must be SLH-DSA"
  if (← asString "revision" (← field "vector set" object "revision")) != "FIPS205" then
    fail "revision must be FIPS205"
  if !(← asBool "isSample" (← field "vector set" object "isSample")) then
    fail "only isSample=true evidence is accepted"
  let vsId ← positiveId "vsId" (← field "vector set" object "vsId")
  let mode ← parseMode (← asString "mode" (← field "vector set" object "mode"))
  return (object, vsId, mode)

private def requireUniquePositive (label : String) (ids : Array Nat) : Except String Unit := do
  let mut seen : List Nat := []
  for id in ids do
    if id == 0 then fail s!"{label}: zero identifier"
    if seen.contains id then fail s!"{label}: duplicate identifier {id}"
    seen := id :: seen

private def parseKeyGenTest (parameter : ParamInfo) (json : Json) : Except String PromptTest := do
  let object ← asObject "keyGen test" json
  requireKeys "keyGen test" object ["tcId", "skSeed", "skPrf", "pkSeed"]
  let tcId ← positiveId "tcId" (← field "keyGen test" object "tcId")
  let skSeed ← exactHex "skSeed" (← field "keyGen test" object "skSeed") parameter.n
  let skPrf ← exactHex "skPrf" (← field "keyGen test" object "skPrf") parameter.n
  let pkSeed ← exactHex "pkSeed" (← field "keyGen test" object "pkSeed") parameter.n
  return { tcId, payload := .keyGen skSeed skPrf pkSeed }

private def parseSignatureTest (mode : Mode) (parameter : ParamInfo)
    (interface : SignatureInterface) (preHash : Option PreHash) (deterministic : Option Bool)
    (json : Json) : Except String PromptTest := do
  let label := if mode == .sigGen then "sigGen test" else "sigVer test"
  let object ← asObject label json
  let mut keys := ["tcId", "message"]
  keys := (if mode == .sigGen then "sk" else "pk") :: keys
  if mode == .sigVer then keys := "signature" :: keys
  if interface == .external then keys := "context" :: keys
  if preHash == some .preHash then keys := "hashAlg" :: keys
  if deterministic == some false then keys := "additionalRandomness" :: keys
  requireKeys label object keys
  let tcId ← positiveId "tcId" (← field label object "tcId")
  let message ← messageHex (← field label object "message")
  let key ← if mode == .sigGen then
    exactHex "sk" (← field label object "sk") parameter.secretKeyBytes
  else
    exactHex "pk" (← field label object "pk") parameter.publicKeyBytes
  let context ← if interface == .external then
    some <$> boundedHex "context" (← field label object "context") 255
  else pure none
  let hashAlg ← if preHash == some .preHash then
    some <$> parseHashAlg (← asString "hashAlg" (← field label object "hashAlg"))
  else pure none
  let randomness ← if deterministic == some false then
    some <$> exactHex "additionalRandomness" (← field label object "additionalRandomness") parameter.n
  else pure none
  let signature ← if mode == .sigVer then
    let bytes ← hexBytes "signature" (← asString "signature" (← field label object "signature"))
    let allowed := bytes.size == parameter.signatureBytes || bytes.size + 1 == parameter.signatureBytes ||
      bytes.size == parameter.signatureBytes + 1
    if !allowed then fail "signature: sigVer sample permits only exact or one-byte size mutations"
    pure (some bytes)
  else pure none
  let payload ← match mode, signature with
    | .sigGen, none => pure (.sigGen key message context hashAlg randomness)
    | .sigVer, some bytes => pure (.sigVer key message context hashAlg bytes)
    | _, _ => fail s!"{label}: internal mode/payload mismatch"
  return { tcId, payload }

private def parsePromptGroup (mode : Mode) (json : Json) : Except String PromptGroup := do
  let object ← asObject "prompt group" json
  let baseKeys := ["tgId", "testType", "parameterSet", "tests"]
  let interface ← if mode == .keyGen then pure none else
    some <$> parseInterface (← asString "signatureInterface" (← field "prompt group" object "signatureInterface"))
  let preHash ← match interface with
    | some .external =>
        some <$> (parsePreHash
          (← asString "preHash" (← field "prompt group" object "preHash")))
    | _ => pure none
  let deterministic ← if mode == .sigGen then
    some <$> asBool "deterministic" (← field "prompt group" object "deterministic")
  else pure none
  let extraKeys := match mode, interface with
    | .keyGen, _ => []
    | .sigGen, some .internal => ["deterministic", "signatureInterface"]
    | .sigGen, some .external => ["deterministic", "signatureInterface", "preHash"]
    | .sigVer, some .internal => ["signatureInterface"]
    | .sigVer, some .external => ["signatureInterface", "preHash"]
    | _, _ => []
  requireKeys "prompt group" object (baseKeys ++ extraKeys)
  if (← asString "testType" (← field "prompt group" object "testType")) != "AFT" then
    fail "testType must be AFT"
  let tgId ← positiveId "tgId" (← field "prompt group" object "tgId")
  let parameter ← parameterByName
    (← asString "parameterSet" (← field "prompt group" object "parameterSet"))
  let testJson ← asArray "tests" (← field "prompt group" object "tests")
  if testJson.isEmpty then fail "prompt group: tests must be nonempty"
  let tests ← if mode == .keyGen then
    testJson.mapM (parseKeyGenTest parameter)
  else match interface with
    | some selected => testJson.mapM (parseSignatureTest mode parameter selected preHash deterministic)
    | none => fail "signatureInterface required for signature modes"
  requireUniquePositive "tcId" (tests.map (·.tcId))
  return { tgId, parameter, signatureInterface := interface, preHash, deterministic, tests }

/-- Parse a duplicate-preserving JSON value established by a `StrictJson.parse` string root. -/
private def parsePromptJson (json : Json) : Except String Prompt := do
  let (object, vsId, mode) ← parseCommonTop json
  let groupJson ← asArray "testGroups" (← field "vector set" object "testGroups")
  if groupJson.isEmpty then fail "testGroups must be nonempty"
  let groups ← groupJson.mapM (parsePromptGroup mode)
  requireUniquePositive "tgId" (groups.map (·.tgId))
  requireUniquePositive "global tcId" (groups.flatMap (·.tests.map (·.tcId)))
  return { vsId, mode, groups }

/-- Parse source text with duplicate-key rejection and then validate it as a prompt. -/
def parsePrompt (source : String) : Except String Prompt :=
  StrictJson.parse source >>= parsePromptJson

private def parseResultTest (mode : Mode) (json : Json) : Except String ResultTest := do
  let object ← asObject "result test" json
  let keys := match mode with
    | .keyGen => ["tcId", "pk", "sk"]
    | .sigGen => ["tcId", "signature"]
    | .sigVer => ["tcId", "testPassed"]
  requireKeys "result test" object keys
  let tcId ← positiveId "tcId" (← field "result test" object "tcId")
  let payload ← match mode with
    | .keyGen => do
        let pk ← hexBytes "pk" (← asString "pk" (← field "result test" object "pk"))
        let sk ← hexBytes "sk" (← asString "sk" (← field "result test" object "sk"))
        pure (.keyGen pk sk)
    | .sigGen => do
        let signature ← hexBytes "signature"
          (← asString "signature" (← field "result test" object "signature"))
        pure (.sigGen signature)
    | .sigVer => .sigVer <$> asBool "testPassed" (← field "result test" object "testPassed")
  return { tcId, payload }

private def parseResultGroup (mode : Mode) (json : Json) : Except String ResultGroup := do
  let object ← asObject "result group" json
  requireKeys "result group" object ["tgId", "tests"]
  let tgId ← positiveId "tgId" (← field "result group" object "tgId")
  let testJson ← asArray "tests" (← field "result group" object "tests")
  if testJson.isEmpty then fail "result group: tests must be nonempty"
  let tests ← testJson.mapM (parseResultTest mode)
  requireUniquePositive "result tcId" (tests.map (·.tcId))
  return { tgId, tests }

/-- Parse a duplicate-preserving JSON value established by a `StrictJson.parse` string root. -/
private def parseResultsJson (json : Json) : Except String Results := do
  let (object, vsId, mode) ← parseCommonTop json
  let groupJson ← asArray "testGroups" (← field "vector set" object "testGroups")
  if groupJson.isEmpty then fail "result testGroups must be nonempty"
  let groups ← groupJson.mapM (parseResultGroup mode)
  requireUniquePositive "result tgId" (groups.map (·.tgId))
  requireUniquePositive "global result tcId" (groups.flatMap (·.tests.map (·.tcId)))
  return { vsId, mode, groups }

/-- Parse source text with duplicate-key rejection and then validate it as expected results. -/
def parseResults (source : String) : Except String Results :=
  StrictJson.parse source >>= parseResultsJson

private def findResultGroup (results : Results) (tgId : Nat) : Option ResultGroup :=
  results.groups.find? (·.tgId == tgId)

private def findResultTest (group : ResultGroup) (tcId : Nat) : Option ResultTest :=
  group.tests.find? (·.tcId == tcId)

/-- Check a pair whose positive, nonempty, and globally unique IDs were established by the private
JSON validators above. This helper is not a validator for arbitrary constructed typed values. -/
private def validatePair (prompt : Prompt) (results : Results) : Except String Unit := do
  if prompt.vsId != results.vsId then fail "prompt/result vsId mismatch"
  if prompt.mode != results.mode then fail "prompt/result mode mismatch"
  if prompt.groups.size != results.groups.size then fail "prompt/result group count mismatch"
  for group in prompt.groups do
    let some resultGroup := findResultGroup results group.tgId
      | fail s!"missing result tgId {group.tgId}"
    if group.tests.size != resultGroup.tests.size then fail s!"tcId count mismatch in tgId {group.tgId}"
    for test in group.tests do
      let some result := findResultTest resultGroup test.tcId
        | fail s!"missing result tcId {test.tcId}"
      match prompt.mode, result.payload with
      | .keyGen, .keyGen pk sk =>
          if pk.size != group.parameter.publicKeyBytes || sk.size != group.parameter.secretKeyBytes then
            fail s!"keyGen output width mismatch at tcId {test.tcId}"
      | .sigGen, .sigGen signature =>
          if signature.size != group.parameter.signatureBytes then
            fail s!"sigGen signature width mismatch at tcId {test.tcId}"
      | .sigVer, .sigVer passed =>
          match test.payload with
          | .sigVer _ _ _ _ signature =>
              if passed && signature.size != group.parameter.signatureBytes then
                fail s!"positive sigVer result has noncanonical signature width at tcId {test.tcId}"
          | _ => fail s!"prompt payload mode mismatch at tcId {test.tcId}"
      | _, _ => fail s!"result payload mode mismatch at tcId {test.tcId}"

/-- Parse and jointly validate one prompt/expected-results pair. -/
def parseAndValidate (promptSource resultsSource : String) : Except String (Prompt × Results) := do
  let prompt ← parsePrompt promptSource
  let results ← parseResults resultsSource
  validatePair prompt results
  return (prompt, results)

/-- Strictly parse an exact `{prompt, expectedResults}` wrapper and jointly validate its pair. -/
def parseWrappedPair (source : String) : Except String (Prompt × Results) := do
  let wrapper ← StrictJson.parse source
  let object ← asObject "wrapped pair" wrapper
  requireKeys "wrapped pair" object ["prompt", "expectedResults"]
  let prompt ← parsePromptJson (← field "wrapped pair" object "prompt")
  let results ← parseResultsJson (← field "wrapped pair" object "expectedResults")
  validatePair prompt results
  return (prompt, results)

end SLHDSA.Test.ACVP
