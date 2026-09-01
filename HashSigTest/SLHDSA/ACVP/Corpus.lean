/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSigTest.SLHDSA.ACVP.Schema

/-!
# Lossless binary ACVP corpus

Fail-closed decoding for the compact corpus generated from the pinned NIST ACVP-Server SLH-DSA
sample suite. Unlike schema-only projections, the decoded records retain every seed, key, message,
context, randomizer, signature, prehash selector, and expected verification result.

The binary uses big-endian integers, 32-bit byte lengths, and explicit presence tags. The decoder
accepts only the exact 12/72/36 group and 120/624/504 case profile, validates all conditional fields
and FIPS parameter widths, and rejects trailing bytes.
-/

public section

namespace SLHDSA.Test.ACVP.Corpus

open SLHDSA.Test.ACVP

inductive TestType where
  | aft
  deriving BEq, Repr

structure KeyGenCase where
  tcId : Nat
  skSeed : ByteArray
  skPrf : ByteArray
  pkSeed : ByteArray
  pk : ByteArray
  sk : ByteArray
  deriving BEq

structure SigGenCase where
  tcId : Nat
  sk : ByteArray
  message : ByteArray
  context : Option ByteArray
  hashAlg : Option HashAlg
  additionalRandomness : Option ByteArray
  signature : ByteArray
  deriving BEq

structure SigVerCase where
  tcId : Nat
  pk : ByteArray
  message : ByteArray
  context : Option ByteArray
  hashAlg : Option HashAlg
  signature : ByteArray
  testPassed : Bool
  deriving BEq

structure GroupMetadata where
  tgId : Nat
  testType : TestType
  parameter : ParamInfo
  signatureInterface : Option SignatureInterface
  preHash : Option PreHash
  deterministic : Option Bool
  deriving BEq

structure KeyGenGroup where
  metadata : GroupMetadata
  tests : Array KeyGenCase
  deriving BEq

structure SigGenGroup where
  metadata : GroupMetadata
  tests : Array SigGenCase
  deriving BEq

structure SigVerGroup where
  metadata : GroupMetadata
  tests : Array SigVerCase
  deriving BEq

/-- The complete typed contents of the three pinned NIST sample vector sets. -/
structure Data where
  vsId : Nat
  keyGen : Array KeyGenGroup
  sigGen : Array SigGenGroup
  sigVer : Array SigVerGroup
  deriving BEq

private structure Decoder where
  input : ByteArray
  position : Nat := 0

private abbrev DecodeM := StateT Decoder (Except String)

private def reject {α : Type} (message : String) : DecodeM α :=
  throw message

private def ensure (condition : Bool) (message : String) : DecodeM Unit :=
  if condition then pure () else reject message

private def take (count : Nat) : DecodeM ByteArray := do
  let state ← get
  if state.position > state.input.size || count > state.input.size - state.position then
    reject s!"truncated corpus at byte {state.position}: need {count} bytes"
  let result := state.input.extract state.position (state.position + count)
  set { state with position := state.position + count }
  return result

private def readU8 : DecodeM Nat := do
  let bytes ← take 1
  return (bytes.get! 0).toNat

private def readU16 : DecodeM Nat := do
  let a ← readU8
  let b ← readU8
  return 256 * a + b

private def readU32 : DecodeM Nat := do
  let a ← readU8
  let b ← readU8
  let c ← readU8
  let d ← readU8
  return 16777216 * a + 65536 * b + 256 * c + d

private def readBlobBounded (label : String) (maximum : Nat) : DecodeM ByteArray := do
  let count ← readU32
  if count > maximum then reject s!"{label}: length {count} exceeds {maximum}"
  take count

private def readBlobExact (label : String) (expected : Nat) : DecodeM ByteArray := do
  let count ← readU32
  if count != expected then reject s!"{label}: expected {expected} bytes, got {count}"
  take count

private def readOptionBlobBounded (label : String) (maximum : Nat) : DecodeM (Option ByteArray) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => some <$> readBlobBounded label maximum
  | tag => reject s!"{label}: invalid presence tag {tag}"

private def readOptionBlobExact (label : String) (expected : Nat) : DecodeM (Option ByteArray) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => some <$> readBlobExact label expected
  | tag => reject s!"{label}: invalid presence tag {tag}"

private def readInterface : DecodeM (Option SignatureInterface) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => pure (some .internal)
  | 2 => pure (some .external)
  | tag => reject s!"signatureInterface: invalid tag {tag}"

private def readPreHash : DecodeM (Option PreHash) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => pure (some .pure)
  | 2 => pure (some .preHash)
  | tag => reject s!"preHash: invalid tag {tag}"

private def readDeterministic : DecodeM (Option Bool) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => pure (some false)
  | 2 => pure (some true)
  | tag => reject s!"deterministic: invalid tag {tag}"

private def readHashAlg : DecodeM (Option HashAlg) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => pure (some .sha2_224)
  | 2 => pure (some .sha2_256)
  | 3 => pure (some .sha2_384)
  | 4 => pure (some .sha2_512)
  | 5 => pure (some .sha2_512_224)
  | 6 => pure (some .sha2_512_256)
  | 7 => pure (some .sha3_224)
  | 8 => pure (some .sha3_256)
  | 9 => pure (some .sha3_384)
  | 10 => pure (some .sha3_512)
  | 11 => pure (some .shake128)
  | 12 => pure (some .shake256)
  | tag => reject s!"hashAlg: invalid tag {tag}"

private def readParameter : DecodeM ParamInfo := do
  let index ← readU8
  let some parameter := parameterSets[index]?
    | reject s!"parameterSet: invalid index {index}"
  return parameter

private def readTestType : DecodeM TestType := do
  match ← readU8 with
  | 1 => pure .aft
  | tag => reject s!"testType: invalid tag {tag}"

private def modeLabel : Mode → String
  | .keyGen => "keyGen"
  | .sigGen => "sigGen"
  | .sigVer => "sigVer"

private def readMetadata (mode : Mode) (expectedTgId : Nat) : DecodeM (GroupMetadata × Nat) := do
  let tgId ← readU32
  if tgId != expectedTgId then
    reject s!"{modeLabel mode}: expected tgId {expectedTgId}, got {tgId}"
  let testType ← readTestType
  let parameter ← readParameter
  let signatureInterface ← readInterface
  let preHash ← readPreHash
  let deterministic ← readDeterministic
  let testCount ← readU16
  if testCount == 0 then reject s!"{modeLabel mode} tgId {tgId}: empty test group"
  match mode with
  | .keyGen => do
      ensure (signatureInterface.isNone && preHash.isNone && deterministic.isNone)
        s!"keyGen tgId {tgId}: signature-only metadata present"
  | .sigGen => do
      ensure (signatureInterface.isSome && deterministic.isSome)
        s!"sigGen tgId {tgId}: interface/deterministic metadata absent"
      ensure ((signatureInterface == some .external) == preHash.isSome)
        s!"sigGen tgId {tgId}: preHash presence does not match interface"
  | .sigVer => do
      ensure (signatureInterface.isSome && deterministic.isNone)
        s!"sigVer tgId {tgId}: invalid interface/deterministic metadata"
      ensure ((signatureInterface == some .external) == preHash.isSome)
        s!"sigVer tgId {tgId}: preHash presence does not match interface"
  return (⟨tgId, testType, parameter, signatureInterface, preHash, deterministic⟩, testCount)

private def readTcId (mode : Mode) (expected : Nat) : DecodeM Nat := do
  let tcId ← readU32
  if tcId != expected then
    reject s!"{modeLabel mode}: expected tcId {expected}, got {tcId}"
  return tcId

private def readNonemptyMessage (mode : Mode) (tcId : Nat) : DecodeM ByteArray := do
  let message ← readBlobBounded s!"{modeLabel mode} tcId {tcId} message" 8192
  if message.isEmpty then reject s!"{modeLabel mode} tcId {tcId}: empty message"
  return message

private def decodeKeyGenGroups : DecodeM (Array KeyGenGroup) := do
  let mut groups := #[]
  let mut nextTcId := 1
  for tgOffset in [0 : 12] do
    let (metadata, testCount) ← readMetadata .keyGen (tgOffset + 1)
    let mut tests := #[]
    for _ in [0 : testCount] do
      let tcId ← readTcId .keyGen nextTcId
      let n := metadata.parameter.n
      let skSeed ← readBlobExact s!"keyGen tcId {tcId} skSeed" n
      let skPrf ← readBlobExact s!"keyGen tcId {tcId} skPrf" n
      let pkSeed ← readBlobExact s!"keyGen tcId {tcId} pkSeed" n
      let pk ← readBlobExact s!"keyGen tcId {tcId} pk" metadata.parameter.publicKeyBytes
      let sk ← readBlobExact s!"keyGen tcId {tcId} sk" metadata.parameter.secretKeyBytes
      tests := tests.push ⟨tcId, skSeed, skPrf, pkSeed, pk, sk⟩
      nextTcId := nextTcId + 1
    groups := groups.push ⟨metadata, tests⟩
  if nextTcId != 121 then reject s!"keyGen: expected 120 cases, got {nextTcId - 1}"
  return groups

private def decodeSigGenGroups : DecodeM (Array SigGenGroup) := do
  let mut groups := #[]
  let mut nextTcId := 1
  for tgOffset in [0 : 72] do
    let (metadata, testCount) ← readMetadata .sigGen (tgOffset + 1)
    let mut tests := #[]
    for _ in [0 : testCount] do
      let tcId ← readTcId .sigGen nextTcId
      let sk ← readBlobExact s!"sigGen tcId {tcId} sk" metadata.parameter.secretKeyBytes
      let message ← readNonemptyMessage .sigGen tcId
      let context ← readOptionBlobBounded s!"sigGen tcId {tcId} context" 255
      let hashAlg ← readHashAlg
      let randomness ← readOptionBlobExact s!"sigGen tcId {tcId} additionalRandomness"
        metadata.parameter.n
      let signature ← readBlobExact s!"sigGen tcId {tcId} signature"
        metadata.parameter.signatureBytes
      ensure ((metadata.signatureInterface == some .external) == context.isSome)
        s!"sigGen tcId {tcId}: context presence does not match interface"
      ensure ((metadata.preHash == some .preHash) == hashAlg.isSome)
        s!"sigGen tcId {tcId}: hashAlg presence does not match preHash"
      ensure ((metadata.deterministic == some false) == randomness.isSome)
        s!"sigGen tcId {tcId}: randomizer presence does not match deterministic flag"
      tests := tests.push ⟨tcId, sk, message, context, hashAlg, randomness, signature⟩
      nextTcId := nextTcId + 1
    groups := groups.push ⟨metadata, tests⟩
  if nextTcId != 625 then reject s!"sigGen: expected 624 cases, got {nextTcId - 1}"
  return groups

private def decodeSigVerGroups : DecodeM (Array SigVerGroup) := do
  let mut groups := #[]
  let mut nextTcId := 1
  for tgOffset in [0 : 36] do
    let (metadata, testCount) ← readMetadata .sigVer (tgOffset + 1)
    let mut tests := #[]
    for _ in [0 : testCount] do
      let tcId ← readTcId .sigVer nextTcId
      let pk ← readBlobExact s!"sigVer tcId {tcId} pk" metadata.parameter.publicKeyBytes
      let message ← readNonemptyMessage .sigVer tcId
      let context ← readOptionBlobBounded s!"sigVer tcId {tcId} context" 255
      let hashAlg ← readHashAlg
      let signature ← readBlobBounded s!"sigVer tcId {tcId} signature"
        (metadata.parameter.signatureBytes + 1)
      let passed ← match ← readU8 with
        | 0 => pure false
        | 1 => pure true
        | tag => reject s!"sigVer tcId {tcId}: invalid testPassed tag {tag}"
      let expected := metadata.parameter.signatureBytes
      ensure (signature.size == expected || signature.size + 1 == expected ||
          signature.size == expected + 1)
        s!"sigVer tcId {tcId}: signature is not canonical or a one-byte size mutation"
      ensure (!passed || signature.size == expected)
        s!"sigVer tcId {tcId}: positive result has noncanonical signature width"
      ensure ((metadata.signatureInterface == some .external) == context.isSome)
        s!"sigVer tcId {tcId}: context presence does not match interface"
      ensure ((metadata.preHash == some .preHash) == hashAlg.isSome)
        s!"sigVer tcId {tcId}: hashAlg presence does not match preHash"
      tests := tests.push ⟨tcId, pk, message, context, hashAlg, signature, passed⟩
      nextTcId := nextTcId + 1
    groups := groups.push ⟨metadata, tests⟩
  if nextTcId != 505 then reject s!"sigVer: expected 504 cases, got {nextTcId - 1}"
  return groups

private def expectBytes (expected : List Nat) : DecodeM Unit := do
  for byte in expected do
    let actual ← readU8
    if actual != byte then reject "invalid corpus magic"

private def expectSectionHeader (mode : Mode) (modeTag groupCount testCount : Nat) : DecodeM Unit := do
  if (← readU8) != modeTag then reject s!"{modeLabel mode}: section tag mismatch"
  if (← readU32) != 53 then reject s!"{modeLabel mode}: vsId must be 53"
  if (← readU16) != groupCount then reject s!"{modeLabel mode}: group-count header mismatch"
  if (← readU32) != testCount then reject s!"{modeLabel mode}: test-count header mismatch"

/-- Decode the complete binary corpus, rejecting malformed tags, lengths, IDs, widths, counts,
conditional fields, truncation, and trailing bytes. -/
def decode (input : ByteArray) : Except String Data := do
  let action : DecodeM Data := do
    expectBytes [86, 67, 86, 83, 76, 72, 49, 0]
    if (← readU16) != 1 then reject "unsupported corpus format version"
    if (← readU16) != 3 then reject "corpus must contain exactly three sections"
    expectSectionHeader .keyGen 1 12 120
    let keyGen ← decodeKeyGenGroups
    expectSectionHeader .sigGen 2 72 624
    let sigGen ← decodeSigGenGroups
    expectSectionHeader .sigVer 3 36 504
    let sigVer ← decodeSigVerGroups
    let state ← get
    if state.position != state.input.size then
      reject s!"trailing corpus bytes: consumed {state.position} of {state.input.size}"
    return ⟨53, keyGen, sigGen, sigVer⟩
  (action.run { input }).map (·.1)

/-- Count all key-generation cases in decoded data. -/
def Data.keyGenCount (data : Data) : Nat :=
  data.keyGen.foldl (fun count group => count + group.tests.size) 0

/-- Count all signature-generation cases in decoded data. -/
def Data.sigGenCount (data : Data) : Nat :=
  data.sigGen.foldl (fun count group => count + group.tests.size) 0

/-- Count all signature-verification cases in decoded data. -/
def Data.sigVerCount (data : Data) : Nat :=
  data.sigVer.foldl (fun count group => count + group.tests.size) 0

/-- Count expected-positive signature-verification cases. -/
def Data.sigVerPositiveCount (data : Data) : Nat :=
  data.sigVer.foldl (fun count group =>
    count + group.tests.foldl (fun subtotal test => subtotal + if test.testPassed then 1 else 0) 0) 0

end SLHDSA.Test.ACVP.Corpus
