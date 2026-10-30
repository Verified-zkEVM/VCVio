/-
Copyright (c) 2026 Nicolas Consigny, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Alexander Hicks
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import VCVioTest.Algorithms.Hash
public import Lean.Data.Json.Parser

/-!
# S04 SHA2, SHAKE, and SLH-DSA primitive tests

Runtime checks for the SHA2 rejecting address boundary and exact FIPS 205 Section 11 grammar
fingerprints for all twelve approved profiles. See `PrimitiveVectors/vectors.json` for the
evidence classification and expected fingerprints. Shared hash vectors run in `algorithm_tests`.
-/

public section

namespace SLHDSA.PrimitiveTests

open SLHDSA.Concrete
open VCVioTest.Algorithms.Hash
open VCVio.Algorithms.Sha2
open VCVio.Algorithms.Keccak

private def sequenceBytes (start count : ℕ) : Bytes count :=
  Vector.ofFn fun i : Fin count => (start + i.val).toUInt8

private def profileAddress : Adrs :=
  { layer := 7, tree := 0x0102030405060708, type := AddrType.forsTree.toCode,
    word1 := 1, word2 := 2, word3 := 3 }

private def profileExpected : FipsParameterSet → String
  | .SLHDSA_SHA2_128s => "126bdad7c0379199d768a61d767412a505785bfe348f013e97720384938e661e"
  | .SLHDSA_SHAKE_128s => "8c5c29c4ecfd8be0f2ab778a4d869846d3861b6a6639e6c54e9be8c66334bf3e"
  | .SLHDSA_SHA2_128f => "a70faae3a69a68a6dec37a659dc1c48baf005f868eb2a58a6dcb00a25f927bed"
  | .SLHDSA_SHAKE_128f => "d7d0222381c39e6ade4aa762907e9b31eda867b7a0428deafa12a7e20e220718"
  | .SLHDSA_SHA2_192s => "ad1bbec52bed4cb9ba363f500a484e75aa34412aef409ae6384bd0657622ac88"
  | .SLHDSA_SHAKE_192s => "1c6edf520ce447cef2b03cb676177efb882425d2489ea0f7f1ff3544c4da2a30"
  | .SLHDSA_SHA2_192f => "4bf0c27c23b639d49a0334550af4eba4f27db1a22add231f8579b2d3c79a95e5"
  | .SLHDSA_SHAKE_192f => "010573b253a885bcea685fb26c9b5aa7be0dec697412a3d6bb427fdf75f90cdc"
  | .SLHDSA_SHA2_256s => "412034667c7f084546c39cd6ee7b1426cf32705cff083e8dc41a2bb157aac89f"
  | .SLHDSA_SHAKE_256s => "5b7baf6c7e135155a66636c6670b55a68a1b54981cd903d265599f1af1780256"
  | .SLHDSA_SHA2_256f => "9352f0249a322a2a1397fcfd1cfca97200d1aefba55a083587cf42988e72c73b"
  | .SLHDSA_SHAKE_256f => "56217933da0de7175fed5d132c030717eea4cc9d9b827ae3e234bce79a0973d8"

private def profileOutputsWith (p : Params)
    (f : Bytes p.n → Adrs → Bytes p.n → Bytes p.n)
    (h : Bytes p.n → Adrs → Bytes p.n → Bytes p.n → Bytes p.n)
    (tlHash : Bytes p.n → Adrs → List (Bytes p.n) → Bytes p.n)
    (prf : Bytes p.n → Bytes p.n → Adrs → Bytes p.n)
    (prfMsg : Bytes p.n → Bytes p.n → List Byte → Bytes p.n)
    (hMsg : Bytes p.n → Bytes p.n → Bytes p.n → List Byte → Bytes p.m) : ByteArray :=
  let pkSeed := sequenceBytes 0 p.n
  let skSeed := sequenceBytes 0x20 p.n
  let pkRoot := sequenceBytes 0x40 p.n
  let randomizer := sequenceBytes 0x60 p.n
  let optRand := sequenceBytes 0x80 p.n
  let left := sequenceBytes 0xc0 p.n
  let right := sequenceBytes 0xe0 p.n
  let tl := [sequenceBytes 0xc0 p.n, sequenceBytes 0xd0 p.n, sequenceBytes 0xe0 p.n]
  let message : List Byte := [0xde, 0xad, 0xbe, 0xef, 0, 1]
  let append (out : ByteArray) (value : Bytes p.n) := out ++ bytesToByteArray value
  append (append (append (append (append ByteArray.empty
    (f pkSeed profileAddress left))
    (h pkSeed profileAddress left right))
    (tlHash pkSeed profileAddress tl))
    (prf pkSeed skSeed profileAddress))
    (prfMsg skSeed optRand message) ++
    bytesToByteArray (hMsg randomizer pkSeed pkRoot message)

/-- Exercise the six operations through the exact bundle exported for each approved profile.
Keeping this selector exhaustive makes a mutation in either the family dispatch or any bundle
field observable in the profile fingerprint. The fingerprints were generated with independent
tooling (a from-spec Python implementation of §11) but by the same authorship pipeline, so
they guard against implementation drift rather than a shared misreading of the standard;
reference-implementation ACVP cross-checks are the KAT slice's responsibility. -/
private def profileOutputs : FipsParameterSet → ByteArray
  | .SLHDSA_SHA2_128s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_128s)
      (approvedPrimitives .SLHDSA_SHA2_128s).F (approvedPrimitives .SLHDSA_SHA2_128s).H
      (approvedPrimitives .SLHDSA_SHA2_128s).Tl (approvedPrimitives .SLHDSA_SHA2_128s).PRF
      (approvedPrimitives .SLHDSA_SHA2_128s).PRFmsg (approvedPrimitives .SLHDSA_SHA2_128s).Hmsg
  | .SLHDSA_SHAKE_128s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_128s)
      (approvedPrimitives .SLHDSA_SHAKE_128s).F (approvedPrimitives .SLHDSA_SHAKE_128s).H
      (approvedPrimitives .SLHDSA_SHAKE_128s).Tl (approvedPrimitives .SLHDSA_SHAKE_128s).PRF
      (approvedPrimitives .SLHDSA_SHAKE_128s).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_128s).Hmsg
  | .SLHDSA_SHA2_128f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_128f)
      (approvedPrimitives .SLHDSA_SHA2_128f).F (approvedPrimitives .SLHDSA_SHA2_128f).H
      (approvedPrimitives .SLHDSA_SHA2_128f).Tl (approvedPrimitives .SLHDSA_SHA2_128f).PRF
      (approvedPrimitives .SLHDSA_SHA2_128f).PRFmsg (approvedPrimitives .SLHDSA_SHA2_128f).Hmsg
  | .SLHDSA_SHAKE_128f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_128f)
      (approvedPrimitives .SLHDSA_SHAKE_128f).F (approvedPrimitives .SLHDSA_SHAKE_128f).H
      (approvedPrimitives .SLHDSA_SHAKE_128f).Tl (approvedPrimitives .SLHDSA_SHAKE_128f).PRF
      (approvedPrimitives .SLHDSA_SHAKE_128f).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_128f).Hmsg
  | .SLHDSA_SHA2_192s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_192s)
      (approvedPrimitives .SLHDSA_SHA2_192s).F (approvedPrimitives .SLHDSA_SHA2_192s).H
      (approvedPrimitives .SLHDSA_SHA2_192s).Tl (approvedPrimitives .SLHDSA_SHA2_192s).PRF
      (approvedPrimitives .SLHDSA_SHA2_192s).PRFmsg (approvedPrimitives .SLHDSA_SHA2_192s).Hmsg
  | .SLHDSA_SHAKE_192s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_192s)
      (approvedPrimitives .SLHDSA_SHAKE_192s).F (approvedPrimitives .SLHDSA_SHAKE_192s).H
      (approvedPrimitives .SLHDSA_SHAKE_192s).Tl (approvedPrimitives .SLHDSA_SHAKE_192s).PRF
      (approvedPrimitives .SLHDSA_SHAKE_192s).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_192s).Hmsg
  | .SLHDSA_SHA2_192f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_192f)
      (approvedPrimitives .SLHDSA_SHA2_192f).F (approvedPrimitives .SLHDSA_SHA2_192f).H
      (approvedPrimitives .SLHDSA_SHA2_192f).Tl (approvedPrimitives .SLHDSA_SHA2_192f).PRF
      (approvedPrimitives .SLHDSA_SHA2_192f).PRFmsg (approvedPrimitives .SLHDSA_SHA2_192f).Hmsg
  | .SLHDSA_SHAKE_192f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_192f)
      (approvedPrimitives .SLHDSA_SHAKE_192f).F (approvedPrimitives .SLHDSA_SHAKE_192f).H
      (approvedPrimitives .SLHDSA_SHAKE_192f).Tl (approvedPrimitives .SLHDSA_SHAKE_192f).PRF
      (approvedPrimitives .SLHDSA_SHAKE_192f).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_192f).Hmsg
  | .SLHDSA_SHA2_256s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_256s)
      (approvedPrimitives .SLHDSA_SHA2_256s).F (approvedPrimitives .SLHDSA_SHA2_256s).H
      (approvedPrimitives .SLHDSA_SHA2_256s).Tl (approvedPrimitives .SLHDSA_SHA2_256s).PRF
      (approvedPrimitives .SLHDSA_SHA2_256s).PRFmsg (approvedPrimitives .SLHDSA_SHA2_256s).Hmsg
  | .SLHDSA_SHAKE_256s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_256s)
      (approvedPrimitives .SLHDSA_SHAKE_256s).F (approvedPrimitives .SLHDSA_SHAKE_256s).H
      (approvedPrimitives .SLHDSA_SHAKE_256s).Tl (approvedPrimitives .SLHDSA_SHAKE_256s).PRF
      (approvedPrimitives .SLHDSA_SHAKE_256s).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_256s).Hmsg
  | .SLHDSA_SHA2_256f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_256f)
      (approvedPrimitives .SLHDSA_SHA2_256f).F (approvedPrimitives .SLHDSA_SHA2_256f).H
      (approvedPrimitives .SLHDSA_SHA2_256f).Tl (approvedPrimitives .SLHDSA_SHA2_256f).PRF
      (approvedPrimitives .SLHDSA_SHA2_256f).PRFmsg (approvedPrimitives .SLHDSA_SHA2_256f).Hmsg
  | .SLHDSA_SHAKE_256f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_256f)
      (approvedPrimitives .SLHDSA_SHAKE_256f).F (approvedPrimitives .SLHDSA_SHAKE_256f).H
      (approvedPrimitives .SLHDSA_SHAKE_256f).Tl (approvedPrimitives .SLHDSA_SHAKE_256f).PRF
      (approvedPrimitives .SLHDSA_SHAKE_256f).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_256f).Hmsg

def testAddressAndProfiles : IO Unit := do
  ensure "fixed-width primitive projection rejects short input"
    (byteArrayPrefixChecked (ByteArray.mk #[0xaa]) 2 == .error (.invalidLength 2 1))
  ensure "profile address canonical" profileAddress.isCanonical
  match Sha2Address.ofAdrs profileAddress with
  | .error _ => throw (IO.userError "S04 primitive check failed: valid SHA2 address rejected")
  | .ok checked =>
      ensure "checked and concrete ADRSc agree"
        (checked.bytes.toList == profileAddress.compressSha2)
  let wideLayer := { profileAddress with layer := 256 }
  ensure "SHA2 adapter rejects wide layer"
    (match Sha2Address.ofAdrs wideLayer with
     | .error error => error == .outOfRange 1 256
     | .ok _ => false)
  let wideTree := { profileAddress with tree := 256 ^ 8 }
  ensure "SHA2 adapter rejects wide tree"
    (match Sha2Address.ofAdrs wideTree with
     | .error error => error == .outOfRange 8 (256 ^ 8)
     | .ok _ => false)
  let noncanonical := { profileAddress with type := AddrType.wotsPk.toCode, word2 := 1 }
  ensure "SHA2 adapter rejects noncanonical layout"
    (match Sha2Address.ofAdrs noncanonical with
     | .error error => error == .noncanonicalAddress
     | .ok _ => false)
  for set in FipsParameterSet.all do
    let outputs := profileOutputs set
    ensure s!"six output widths {set.name}"
      (outputs.size == 5 * set.params.n + set.params.m)
    checkHex s!"six exact grammars {set.name}" (sha256 outputs) (profileExpected set)

private def testProfileProjection : IO Unit := do
  let source ← IO.FS.readFile "HashSigTest/SLHDSA/PrimitiveVectors/vectors.json"
  checkHex "profile projection byte pin" (sha256 source.toUTF8)
    "6f1ab86939d50fbf5f1101e03a5f7c18f54dfa05a5f7e6572ed82cfe581584fe"
  let root ← IO.ofExcept (Lean.Json.parse source)
  let profiles ← IO.ofExcept (root.getObjVal? "profile_fingerprints")
  for set in FipsParameterSet.all do
    let projected ← IO.ofExcept (profiles.getObjValAs? String set.name)
    ensure s!"profile projection/runtime agreement {set.name}" (projected == profileExpected set)

def run : IO Unit := do
  testProfileProjection
  testAddressAndProfiles
  IO.println "SLH-DSA S04 primitive tests: PASS (address boundaries; 12 profile grammars)"

end SLHDSA.PrimitiveTests

def main : IO Unit := SLHDSA.PrimitiveTests.run
