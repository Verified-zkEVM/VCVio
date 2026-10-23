/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Scheme
public import HashSigTest.SLHDSA.SHAKE128s.Shake

/-!
# Running the specification on NIST's ACVP test vectors

The random oracle is instantiated with SHAKE256: a 30-byte answer, whose 16-byte prefix is the
short hash, exactly as in the specification. `vectors.txt` holds the SLH-DSA-SHAKE-128s cases of
the ACVP key generation, deterministic signing and verification tests.
-/

@[expose] public section

open SlhDsaSecurity OracleComp

namespace SlhDsaTest

/-- The oracle is SHAKE256 with a 30-byte output, read big-endian. -/
def shakeAnswer (input : Bytes) : HashOutput :=
  (shake256 (ByteArray.mk input.toArray) messageDigestBytes).toList.foldl
    (fun (value : HashOutput) byte => (value <<< 8) ||| BitVec.ofNat _ byte.toNat) 0

instance : HasQuery HashSpec Id where
  query input := shakeAnswer input

def parseHex (s : String) : Option Bytes :=
  if s = "-" then some [] else
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go : List Char → Option Bytes
    | [] => some []
    | a :: b :: rest => do
      let hi ← digit a
      let lo ← digit b
      return (hi * 16 + lo).toUInt8 :: (← go rest)
    | [_] => none
  go s.toList

def toDigest (bytes : Bytes) : Digest :=
  bytes.foldl (fun value byte => (value <<< 8) ||| BitVec.ofNat _ byte.toNat) 0

/-- `PK.seed ‖ PK.root`. -/
def toPublicKey (bytes : Bytes) : PublicKey :=
  { seed := toDigest (bytes.take 16), root := toDigest (bytes.drop 16) }

/-- `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`. -/
def toSecretKey (bytes : Bytes) : SecretKey :=
  { seed := toDigest (bytes.take 16), prf := toDigest ((bytes.drop 16).take 16),
    publicKey := toPublicKey (bytes.drop 32) }

/-- Run one line of `vectors.txt`; `some ok` if it was understood. -/
def check (line : String) : Option Bool := do
  match line.splitOn " " with
  | ["keygen", _, skSeed, skPrf, pkSeed, pk] =>
    let (_, key) := Id.run (Scheme.keygenInternal (toDigest (← parseHex skSeed))
      (toDigest (← parseHex skPrf)) (toDigest (← parseHex pkSeed)))
    return key == toPublicKey (← parseHex pk)
  | ["sign", _, sk, message, context, signature] =>
    let request : Message := { message := ← parseHex message, context := ← parseHex context }
    return Id.run (Scheme.sign (toSecretKey (← parseHex sk)) request) == some (← parseHex signature)
  | ["signInternal", _, sk, message, signature] =>
    let signed := Id.run (Scheme.signInternal (toSecretKey (← parseHex sk)) (← parseHex message))
    return signed.toBytes == (← parseHex signature)
  | ["verify", _, pk, message, context, signature, expected] =>
    let request : Message := { message := ← parseHex message, context := ← parseHex context }
    let accepted := Id.run (Scheme.verify (toPublicKey (← parseHex pk)) request
      (← parseHex signature))
    return accepted == (expected == "true")
  | ["verifyInternal", _, pk, message, signature, expected] =>
    let key := toPublicKey (← parseHex pk)
    let body ← parseHex message
    let accepted := match Signature.fromBytes? (← parseHex signature) with
      | none => false
      | some parsed => Id.run (Scheme.verifyInternal key body parsed)
    return accepted == (expected == "true")
  | _ => none

end SlhDsaTest

open SlhDsaTest in
def main (args : List String) : IO UInt32 := do
  let path := args.headD "SLH-DSA-SHAKE-128s/Test/vectors.txt"
  let only := args.drop 1
  let mut failures := 0
  let mut count := 0
  for line in (← IO.FS.lines path) do
    let fields := line.splitOn " "
    if line.isEmpty || (!only.isEmpty && !only.contains (fields.headD "")) then continue
    let label := s!"{fields.headD ""} {fields.getD 1 ""}"
    match check line with
    | some true => count := count + 1; IO.println s!"ok   {label}"
    | some false => failures := failures + 1; IO.println s!"FAIL {label}"
    | none => failures := failures + 1; IO.println s!"BAD  {label}"
    (← IO.getStdout).flush
  IO.println s!"{count} passed, {failures} failed"
  return if failures = 0 then 0 else 1
