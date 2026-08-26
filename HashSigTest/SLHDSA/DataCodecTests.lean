/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig

/-!
# S03 parameter, endian, ADRS, and codec regression tests

These fixtures exercise the exact FIPS 205 Table 2 values and Algorithms 2--4 semantics, plus
positive and negative fixed-width wire cases. They are specification regressions, not ACVP
implementation-conformance vectors.
-/

public section

namespace SLHDSA.DataCodecTests

structure ExpectedRow where
  name : String
  family : HashFamily
  n : ℕ
  h : ℕ
  d : ℕ
  hp : ℕ
  a : ℕ
  k : ℕ
  lgw : ℕ
  m : ℕ
  digest : ℕ
  treeIndex : ℕ
  leafIndex : ℕ
  category : ℕ
  pk : ℕ
  sk : ℕ
  signature : ℕ
deriving Repr, BEq

def expectedRows : List ExpectedRow :=
  [⟨"SLH-DSA-SHA2-128s", .sha2, 16, 63, 7, 9, 12, 14, 4, 30, 21, 7, 2, 1, 32, 64, 7856⟩,
   ⟨"SLH-DSA-SHAKE-128s", .shake, 16, 63, 7, 9, 12, 14, 4, 30, 21, 7, 2, 1, 32, 64, 7856⟩,
   ⟨"SLH-DSA-SHA2-128f", .sha2, 16, 66, 22, 3, 6, 33, 4, 34, 25, 8, 1, 1, 32, 64, 17088⟩,
   ⟨"SLH-DSA-SHAKE-128f", .shake, 16, 66, 22, 3, 6, 33, 4, 34, 25, 8, 1, 1, 32, 64, 17088⟩,
   ⟨"SLH-DSA-SHA2-192s", .sha2, 24, 63, 7, 9, 14, 17, 4, 39, 30, 7, 2, 3, 48, 96, 16224⟩,
   ⟨"SLH-DSA-SHAKE-192s", .shake, 24, 63, 7, 9, 14, 17, 4, 39, 30, 7, 2, 3, 48, 96, 16224⟩,
   ⟨"SLH-DSA-SHA2-192f", .sha2, 24, 66, 22, 3, 8, 33, 4, 42, 33, 8, 1, 3, 48, 96, 35664⟩,
   ⟨"SLH-DSA-SHAKE-192f", .shake, 24, 66, 22, 3, 8, 33, 4, 42, 33, 8, 1, 3, 48, 96, 35664⟩,
   ⟨"SLH-DSA-SHA2-256s", .sha2, 32, 64, 8, 8, 14, 22, 4, 47, 39, 7, 1, 5, 64, 128, 29792⟩,
   ⟨"SLH-DSA-SHAKE-256s", .shake, 32, 64, 8, 8, 14, 22, 4, 47, 39, 7, 1, 5, 64, 128, 29792⟩,
   ⟨"SLH-DSA-SHA2-256f", .sha2, 32, 68, 17, 4, 9, 35, 4, 49, 40, 8, 1, 5, 64, 128, 49856⟩,
   ⟨"SLH-DSA-SHAKE-256f", .shake, 32, 68, 17, 4, 9, 35, 4, 49, 40, 8, 1, 5, 64, 128, 49856⟩]

def observedRows : List ExpectedRow := ParameterSet.all.map fun s =>
  let p := s.params
  let q := s.profile
  ⟨q.name, q.family, p.n, p.h, p.d, p.hp, p.a, p.k, p.lgw, p.m,
    p.digestBytes, p.treeIdxBytes, p.leafIdxBytes, q.category,
    p.publicKeyBytes, p.secretKeyBytes, p.signatureBytes⟩

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"S03 data/codec check failed: {label}")

def testParameters : IO Unit := do
  ensure "all twelve FIPS Table 2 rows" (observedRows == expectedRows)
  ensure "Fintype and ordered-list cardinalities" (ParameterSet.all.length == 12)
  ensure "legacy reduced set excluded" (!slhdsaSha2_128_24.isApproved)
  for s in ParameterSet.all do
    ensure s!"approved profile {s.profile.name}" s.params.isApproved
    ensure s!"approved parameter lookup {s.profile.name}"
      (match ParameterSet.ofParams s.params with
       | some found => found.params == s.params
       | none => false)

def testEndian : IO Unit := do
  ensure "toInt MSB-first fixture" (toInt [0x12, 0x34, 0x56] == 0x123456)
  ensure "toByte MSB-first fixture" (toByte 0x123456 3 == [0x12, 0x34, 0x56])
  ensure "base2b nibbles" (base2b [0xab, 0xcd] 4 4 == [10, 11, 12, 13])
  ensure "base2b 12-bit digits" (base2b [0x12, 0x34, 0x56] 12 2 == [291, 1110])
  ensure "base2b crossing bytes"
    (base2b [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd] 14 4 ==
      [72, 13398, 7718, 11213])
  ensure "base2b rejects zero width"
    (base2bChecked [0] 0 1 == .error .zeroDigitWidth)
  ensure "base2b rejects short input"
    (base2bChecked [0] 9 1 == .error (.insufficientInput 9 8))
  ensure "toByte rejects overflow"
    (toByteChecked 256 1 == .error (.outOfRange 1 256))
  ensure "decodeExact rejects short"
    (decodeExact 2 [0] == .error (.invalidLength 2 1))
  ensure "decodeExact rejects long"
    (decodeExact 2 [0, 0, 0] == .error (.invalidLength 2 3))

def testAddress : IO Unit := do
  let dirty : Adrs := ⟨3, 9, 6, 11, 12, 13⟩
  let cleared := dirty.setTypeAndClear .tree
  ensure "setTypeAndClear type" (cleared.type == AddrType.tree.toCode)
  ensure "setTypeAndClear words" (cleared.word1 == 0 && cleared.word2 == 0 && cleared.word3 == 0)
  ensure "checked layer overflow"
    (Adrs.setLayerAddressChecked Adrs.zero (256 ^ 4) ==
      .error (.outOfRange 4 (256 ^ 4)))
  ensure "checked tree overflow"
    (Adrs.setTreeAddressChecked Adrs.zero (256 ^ 12) ==
      .error (.outOfRange 12 (256 ^ 12)))
  ensure "checked word overflow"
    (Adrs.setTreeIndexChecked Adrs.zero (256 ^ 4) ==
      .error (.outOfRange 4 (256 ^ 4)))
  let a := (((Adrs.zero.setLayerAddress 3).setTreeAddress 0x0102030405060708).setTypeAndClear
    .wotsHash).setKeyPairAddress 5 |>.setChainAddress 6 |>.setHashAddress 7
  ensure "canonical ADRS" a.isCanonical
  ensure "ADRS length" (a.toBytes.length == 32)
  ensure "ADRS layer big-endian" (a.toBytes.take 4 == [0, 0, 0, 3])
  ensure "ADRS tree big-endian"
    ((a.toBytes.drop 4).take 12 == [0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8])
  ensure "ADRSc length" (a.compressSha2.length == 22)
  ensure "ADRSc accepted" (match a.compressSha2Checked with | .ok _ => true | _ => false)
  match Adrs.decode a.toBytes with
  | .ok wire => ensure "nonzero ADRS parse" (Adrs.fromVector wire.bytes == a)
  | .error _ => throw (IO.userError "S03 data/codec check failed: nonzero ADRS rejected")
  let raw := List.replicate 32 (0 : Byte)
  ensure "ADRS rejects short input"
    (match Adrs.decode (raw.drop 1) with
     | .error error => error == .invalidLength 32 31
     | .ok _ => false)
  ensure "ADRS rejects long input"
    (match Adrs.decode (0 :: raw) with
     | .error error => error == .invalidLength 32 33
     | .ok _ => false)
  match Adrs.decode raw with
  | .error _ => throw (IO.userError "S03 data/codec check failed: canonical zero ADRS rejected")
  | .ok wire =>
      match Adrs.decode wire.encode with
      | .ok wire' => ensure "ADRS wire roundtrip" (wire'.bytes.toList == raw)
      | .error _ => throw (IO.userError "S03 data/codec check failed: ADRS roundtrip rejected")
  ensure "ADRS rejects unknown type"
    (match Adrs.decode (raw.set 19 7) with
     | .error error => error == .invalidAddressType 7
     | .ok _ => false)
  ensure "ADRS rejects nonzero padding"
    (match Adrs.decode ((raw.set 19 1).set 27 1) with
     | .error error => error == .noncanonicalAddress
     | .ok _ => false)
  ensure "ADRS rejects WOTS PRF trailing padding"
    (match Adrs.decode ((raw.set 19 5).set 31 1) with
     | .error error => error == .noncanonicalAddress
     | .ok _ => false)
  ensure "ADRS rejects FORS PRF middle padding"
    (match Adrs.decode ((raw.set 19 6).set 27 1) with
     | .error error => error == .noncanonicalAddress
     | .ok _ => false)
  let wideLayer := (Adrs.zero.setLayerAddress 256).setTypeAndClear .wotsHash
  ensure "ADRSc rejects 8-bit layer overflow"
    (wideLayer.compressSha2Checked == .error (.outOfRange 1 256))
  let wideTree := (Adrs.zero.setTreeAddress (256 ^ 8)).setTypeAndClear .wotsHash
  ensure "ADRSc rejects 64-bit tree overflow"
    (wideTree.compressSha2Checked == .error (.outOfRange 8 (256 ^ 8)))

def testFixedCodecs : IO Unit := do
  for s in ParameterSet.all do
    let p := s.params
    let pk := List.replicate p.publicKeyBytes (0 : Byte)
    let sk := List.replicate p.secretKeyBytes (0 : Byte)
    let sig := List.replicate p.signatureBytes (0 : Byte)
    ensure s!"public key exact {s.profile.name}"
      (match decodePublicKey s pk with | .ok bytes => bytes.toList == pk | _ => false)
    ensure s!"secret key exact {s.profile.name}"
      (match decodeSecretKey s sk with | .ok bytes => bytes.toList == sk | _ => false)
    ensure s!"signature exact {s.profile.name}"
      (match decodeSignature s sig with | .ok bytes => bytes.toList == sig | _ => false)
    ensure s!"public key short {s.profile.name}"
      (decodePublicKey s (pk.drop 1) ==
        .error (.invalidLength p.publicKeyBytes (p.publicKeyBytes - 1)))
    ensure s!"public key long {s.profile.name}"
      (decodePublicKey s (0 :: pk) ==
        .error (.invalidLength p.publicKeyBytes (p.publicKeyBytes + 1)))
    ensure s!"secret key short {s.profile.name}"
      (decodeSecretKey s (sk.drop 1) ==
        .error (.invalidLength p.secretKeyBytes (p.secretKeyBytes - 1)))
    ensure s!"secret key long {s.profile.name}"
      (decodeSecretKey s (0 :: sk) ==
        .error (.invalidLength p.secretKeyBytes (p.secretKeyBytes + 1)))
    ensure s!"signature short {s.profile.name}"
      (decodeSignature s (sig.drop 1) ==
        .error (.invalidLength p.signatureBytes (p.signatureBytes - 1)))
    ensure s!"signature long {s.profile.name}"
      (decodeSignature s (0 :: sig) ==
        .error (.invalidLength p.signatureBytes (p.signatureBytes + 1)))

def run : IO Unit := do
  testParameters
  testEndian
  testAddress
  testFixedCodecs
  IO.println "SLH-DSA S03 data/codec tests: PASS (12 profiles; endian, ADRS, rejection)"

end SLHDSA.DataCodecTests

def main : IO Unit := SLHDSA.DataCodecTests.run
