/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Concrete.Prehash

/-!
# SLH-DSA external-interface canaries

Direct boundary examples that distinguish the pure and pre-hash domains, context placement,
DER-OID placement, digest placement, and the required 255/256-byte rejection boundary.
-/

public section

namespace SLHDSA.ExternalTest

open SLHDSA.External
open SLHDSA.Concrete.Prehash

def failingDescriptor : PrehashDescriptor where
  oidDer := [0x06, 0x01, 0x2a]
  outputLength := 2
  digest := fun _ => .error (.digestLengthMismatch 2 0)

def fixedDescriptor : PrehashDescriptor where
  oidDer := [0x06, 0x01, 0x2a]
  outputLength := 2
  digest := fun _ => .ok #v[0xaa, 0xbb]

/-- Rejects a wrong pure domain byte or a missing empty-context length byte. -/
example : encodePureMessage [] [0xcc] = .ok [0x00, 0x00, 0xcc] := by
  decide

set_option maxRecDepth 2048 in
/-- The largest permitted context is accepted and contributes exactly 257 prefix bytes. -/
example : (encodePureMessage (List.replicate 255 0x7f) []).map List.length = .ok 257 := by
  decide

set_option maxRecDepth 2048 in
/-- The first forbidden context length is rejected with its observed size. -/
example : encodePureMessage (List.replicate 256 0x7f) [] = .error (.contextTooLong 256) := by
  decide

set_option maxRecDepth 2048 in
/-- Algorithm 23 rejects the context before evaluating even a failing pre-hash descriptor. -/
example : encodePrehashMessageWithDescriptor failingDescriptor
    (List.replicate 256 0x7f) [] = .error (.contextTooLong 256) := by
  decide

set_option maxRecDepth 2048 in
/-- The largest permitted pre-hash context remains accepted. -/
example : (encodePrehashMessageWithDescriptor fixedDescriptor
    (List.replicate 255 0x7f) []).map List.length = .ok 262 := by
  decide

set_option maxRecDepth 2048 in
/-- Context rejection also precedes the concrete strength-policy check. -/
example : SLHDSA.Concrete.Prehash.encodeMessage
    FipsParameterSet.SLHDSA_SHA2_256s.params .sha2_256 (List.replicate 256 0x7f) [] =
    .error (.contextTooLong 256) := by
  decide

/-- A category-5 parameter rejects the category-1 SHA-256 pre-hash before signing. -/
example : SLHDSA.Concrete.Prehash.encodeMessage
    FipsParameterSet.SLHDSA_SHA2_256s.params .sha2_256 [] [] =
    .error (.prehashTooWeak 32 32) := by
  decide

/-- Exact digest conversion fails closed rather than padding a short engine result. -/
example : digestBytesExact 2 (ByteArray.mk #[0xaa]) =
    .error (.digestLengthMismatch 2 1) := by
  decide

private def hexValue (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else 0

private def parseHex (hex : String) : ByteArray := Id.run do
  let chars := hex.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:chars.size / 2] do
    out := out.push (hexValue chars[2 * i]! <<< 4 ||| hexValue chars[2 * i + 1]!)
  return out

private def expectedAbc : Algorithm → String
  | .sha2_224 => "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
  | .sha2_256 => "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  | .sha2_384 =>
      "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed\
      8086072ba1e7cc2358baeca134c825a7"
  | .sha2_512 =>
      "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
      2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
  | .sha2_512_224 => "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa"
  | .sha2_512_256 => "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23"
  | .sha3_224 => "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf"
  | .sha3_256 => "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
  | .sha3_384 =>
      "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b\
      298d88cea927ac7f539f1edf228376d25"
  | .sha3_512 =>
      "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e\
      10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
  | .shake128 => "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"
  | .shake256 =>
      "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739\
      d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e4"

private def expectedOidArc : Algorithm → ℕ
  | .sha2_256 => 1
  | .sha2_384 => 2
  | .sha2_512 => 3
  | .sha2_224 => 4
  | .sha2_512_224 => 5
  | .sha2_512_256 => 6
  | .sha3_224 => 7
  | .sha3_256 => 8
  | .sha3_384 => 9
  | .sha3_512 => 10
  | .shake128 => 11
  | .shake256 => 12

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"SLH-DSA external-interface check failed: {label}")

private def checkDigest (label : String) (algorithm : Algorithm)
    (message : List Byte) (expected : String) : IO Unit := do
  match algorithm.digest message with
  | .error error => throw (IO.userError s!"{label}: unexpected digest error {repr error}")
  | .ok digest =>
      ensure label (ByteArray.mk digest.toArray == parseHex expected)

/-- Executable FIPS 180-4/FIPS 202 canaries for all twelve ACVP pre-hash choices, including
their exact DER OIDs and digest widths. -/
def run : IO Unit := do
  ensure "complete prehash menu" (SLHDSA.Concrete.Prehash.all.length == 12)
  let encoded ← match SLHDSA.Concrete.Prehash.encodeMessage
      FipsParameterSet.SLHDSA_SHA2_128s.params
      .sha2_256 [0x10, 0x11] [0xff] with
    | .error error => throw (IO.userError s!"prehash encoding failed: {repr error}")
    | .ok value => pure value
  ensure "domain/context/OID order"
    (encoded.take 15 == [0x01, 0x02, 0x10, 0x11, 0x06, 0x09, 0x60, 0x86,
      0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01])
  ensure "digest placement"
    (ByteArray.mk (encoded.drop 15).toArray ==
      parseHex "a8100ae6aa1940d0b663bb31cd466142ebbdbd5187131b92d93818987832eb89")
  ensure "pure/prehash domain separation"
    (encodePureMessage [] [] !=
      SLHDSA.Concrete.Prehash.encodeMessage
        FipsParameterSet.SLHDSA_SHA2_128s.params .sha2_256 [] [])
  for algorithm in SLHDSA.Concrete.Prehash.all do
    ensure s!"{algorithm.name}: ACVP name round-trip"
      (Algorithm.ofName? algorithm.name == some algorithm)
    ensure s!"{algorithm.name}: DER OID width" (algorithm.oidDer.length == 11)
    ensure s!"{algorithm.name}: DER OID arc"
      (algorithm.oidDer.getLast? == some (UInt8.ofNat (expectedOidArc algorithm)))
    checkDigest s!"{algorithm.name}: abc digest" algorithm [0x61, 0x62, 0x63]
      (expectedAbc algorithm)
  ensure "SHA2-224 is below category 1"
    (!Algorithm.sha2_224.validFor FipsParameterSet.SLHDSA_SHA2_128s.params)
  ensure "SHA2-256 reaches category 1"
    (Algorithm.sha2_256.validFor FipsParameterSet.SLHDSA_SHA2_128s.params)
  ensure "SHA2-256 is below category 3"
    (!Algorithm.sha2_256.validFor FipsParameterSet.SLHDSA_SHA2_192s.params)
  ensure "SHA2-384 reaches category 3"
    (Algorithm.sha2_384.validFor FipsParameterSet.SLHDSA_SHA2_192s.params)
  ensure "SHA2-384 is below category 5"
    (!Algorithm.sha2_384.validFor FipsParameterSet.SLHDSA_SHA2_256s.params)
  ensure "SHA2-512 reaches category 5"
    (Algorithm.sha2_512.validFor FipsParameterSet.SLHDSA_SHA2_256s.params)
  ensure "SHAKE128 reaches category 1"
    (Algorithm.shake128.validFor FipsParameterSet.SLHDSA_SHAKE_128s.params)
  ensure "SHAKE128 is below category 3"
    (!Algorithm.shake128.validFor FipsParameterSet.SLHDSA_SHAKE_192s.params)
  ensure "SHAKE256 reaches category 5"
    (Algorithm.shake256.validFor FipsParameterSet.SLHDSA_SHAKE_256s.params)
  checkDigest "SHA3-224 exact-rate padding" .sha3_224 (List.replicate 144 0x61)
    "f9019111996dcf160e284e320fd6d8825cabcd41a5ffdc4c5e9d64b6"
  checkDigest "SHA3-384 exact-rate padding" .sha3_384 (List.replicate 104 0x61)
    "3a4f3b6284e571238884e95655e8c8a60e068e4059a9734abc08823a900d1615\
    92860243f00619ae699a29092ed91a16"
  checkDigest "SHA3-512 exact-rate padding" .sha3_512 (List.replicate 72 0x61)
    "a8ae722a78e10cbbc413886c02eb5b369a03f6560084aff566bd597bb7ad8c1c\
    cd86e81296852359bf2faddb5153c0a7445722987875e74287adac21adebe952"
  checkDigest "SHAKE128 exact-rate padding" .shake128 (List.replicate 168 0x61)
    "c22e11586c22b713bde373fce93314d76829de2c21d940a28eb659b8dec953a2"
  IO.println "SLH-DSA external-interface tests: PASS (12 bound OIDs/digests; strength/context)"

end SLHDSA.ExternalTest

def main : IO Unit := SLHDSA.ExternalTest.run
