/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.ExternalCodec

/-!
# Structured external-codec regressions

All approved profiles exercise semantic key/signature round trips, exact short/long/trailing
rejection, and row-major sentinels at every FIPS 205 signature component boundary.  One bounded
SHA2-128f construction additionally carries an honest key and signature through the structured
wire boundary before verification.  These are derived regressions, not ACVP or KAT evidence.
-/

public section

namespace SLHDSA.ExternalCodecTests

open ExternalCodec

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"structured codec check failed: {label}")

def rejectsWith {α : Type} (result : Except CodecError α) (expected : CodecError) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

def fixedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

def publicKeyFixture (set : FipsParameterSet) : ExternalCodec.PublicKey set :=
  ⟨Vector.ofFn fun i => fixedBytes set.params.n (11 + 43 * i.val)⟩

def secretKeyFixture (set : FipsParameterSet) : ExternalCodec.SecretKey set :=
  ⟨Vector.ofFn fun i => fixedBytes set.params.n (19 + 41 * i.val)⟩

def signatureFixture (set : FipsParameterSet) : ExternalCodec.Signature set :=
  ⟨Vector.ofFn fun i => fixedBytes set.params.n (29 + 37 * i.val)⟩

def checkSignatureBlock (set : FipsParameterSet) (signature : ExternalCodec.Signature set)
    (decoded : ExternalCodec.Signature set) (raw : Array Byte)
    (label : String) (offset : Fin (signatureNodeCount set.params)) : IO Unit := do
  let expected := signature.blocks[offset.val]
  ensure s!"{set.name}: {label} decoded block"
    (decoded.blocks[offset.val]? == some expected)
  ensure s!"{set.name}: {label} byte offset"
    (raw[offset.val * set.params.n]? == expected.toList[0]?)

def checkProfile (set : FipsParameterSet) : IO Unit := do
  let p := set.params
  let publicKey := publicKeyFixture set
  let secretKey := secretKeyFixture set
  let signature := signatureFixture set
  let publicRaw := ExternalCodec.PublicKey.encode publicKey
  let secretRaw := ExternalCodec.SecretKey.encode secretKey
  let signatureRaw := ExternalCodec.Signature.encode signature
  ensure s!"{set.name}: public-key exact length" (publicRaw.length == p.publicKeyBytes)
  ensure s!"{set.name}: secret-key exact length" (secretRaw.length == p.secretKeyBytes)
  ensure s!"{set.name}: signature exact length" (signatureRaw.length == p.signatureBytes)
  ensure s!"{set.name}: signature node arithmetic"
    (signatureNodeCount p * p.n == p.signatureBytes)
  match decodePublicKeyCore set (encodePublicKeyCore publicKey.toInternal) with
  | .error error =>
      throw (IO.userError s!"{set.name}: public-key roundtrip rejected: {reprStr error}")
  | .ok decoded =>
      ensure s!"{set.name}: public-key semantic roundtrip"
        (ExternalCodec.PublicKey.ofInternal decoded == publicKey)
      ensure s!"{set.name}: public-key successful decode preserves wire"
        (encodePublicKeyCore decoded == publicRaw)
  match decodeSecretKeyCore set (encodeSecretKeyCore secretKey.toInternal) with
  | .error error =>
      throw (IO.userError s!"{set.name}: secret-key roundtrip rejected: {reprStr error}")
  | .ok decoded =>
      ensure s!"{set.name}: secret-key semantic roundtrip"
        (ExternalCodec.SecretKey.ofInternal decoded == secretKey)
      ensure s!"{set.name}: secret-key successful decode preserves wire"
        (encodeSecretKeyCore decoded == secretRaw)
  let decodedSignature ←
    match decodeSignatureCore set (encodeSignatureCore signature.toInternal) with
    | .error error =>
        throw (IO.userError s!"{set.name}: signature roundtrip rejected: {reprStr error}")
    | .ok decoded =>
        ensure s!"{set.name}: signature semantic roundtrip"
          (ExternalCodec.Signature.ofInternal decoded == signature)
        ensure s!"{set.name}: signature successful decode preserves wire"
          (encodeSignatureCore decoded == signatureRaw)
        pure (ExternalCodec.Signature.ofInternal decoded)
  ensure s!"{set.name}: public-key short rejection"
    (rejectsWith (decodePublicKeyCore set (publicRaw.drop 1))
      (.invalidLength p.publicKeyBytes (p.publicKeyBytes - 1)))
  ensure s!"{set.name}: public-key long rejection"
    (rejectsWith (decodePublicKeyCore set (0 :: publicRaw))
      (.invalidLength p.publicKeyBytes (p.publicKeyBytes + 1)))
  ensure s!"{set.name}: public-key trailing rejection"
    (rejectsWith (decodePublicKeyCore set (publicRaw ++ [0xa5]))
      (.invalidLength p.publicKeyBytes (p.publicKeyBytes + 1)))
  ensure s!"{set.name}: secret-key short rejection"
    (rejectsWith (decodeSecretKeyCore set (secretRaw.drop 1))
      (.invalidLength p.secretKeyBytes (p.secretKeyBytes - 1)))
  ensure s!"{set.name}: secret-key long rejection"
    (rejectsWith (decodeSecretKeyCore set (0 :: secretRaw))
      (.invalidLength p.secretKeyBytes (p.secretKeyBytes + 1)))
  ensure s!"{set.name}: secret-key trailing rejection"
    (rejectsWith (decodeSecretKeyCore set (secretRaw ++ [0xa5]))
      (.invalidLength p.secretKeyBytes (p.secretKeyBytes + 1)))
  ensure s!"{set.name}: signature short rejection"
    (rejectsWith (decodeSignatureCore set (signatureRaw.drop 1))
      (.invalidLength p.signatureBytes (p.signatureBytes - 1)))
  ensure s!"{set.name}: signature long rejection"
    (rejectsWith (decodeSignatureCore set (0 :: signatureRaw))
      (.invalidLength p.signatureBytes (p.signatureBytes + 1)))
  ensure s!"{set.name}: signature trailing rejection"
    (rejectsWith (decodeSignatureCore set (signatureRaw ++ [0xa5]))
      (.invalidLength p.signatureBytes (p.signatureBytes + 1)))
  let publicArray := publicRaw.toArray
  ensure s!"{set.name}: PK.seed byte offset"
    (publicArray[0]? == publicKey.blocks[0].toList[0]?)
  ensure s!"{set.name}: PK.root byte offset"
    (publicArray[p.n]? == publicKey.blocks[1].toList[0]?)
  let secretArray := secretRaw.toArray
  for field in List.finRange 4 do
    ensure s!"{set.name}: secret-key field {field.val} byte offset"
      (secretArray[field.val * p.n]? == secretKey.blocks[field.val].toList[0]?)
  let rawArray := signatureRaw.toArray
  checkSignatureBlock set signature decodedSignature rawArray "R" ⟨0, by
    simp [signatureNodeCount]⟩
  for tree in List.finRange p.k do
    checkSignatureBlock set signature decodedSignature rawArray
      s!"FORS tree {tree.val} secret" (forsSecretOffset set.validatedParams tree)
    for height in List.finRange p.a do
      checkSignatureBlock set signature decodedSignature rawArray
        s!"FORS tree {tree.val} auth {height.val}"
        (forsAuthOffset set.validatedParams tree height)
  for layer in List.finRange p.d do
    for chain in List.finRange p.len do
      checkSignatureBlock set signature decodedSignature rawArray
        s!"XMSS layer {layer.val} WOTS {chain.val}"
        (xmssWotsOffset set.validatedParams layer chain)
    for height in List.finRange p.hp do
      checkSignatureBlock set signature decodedSignature rawArray
        s!"XMSS layer {layer.val} auth {height.val}"
        (xmssAuthOffset set.validatedParams layer height)

def exerciseHonestSha2_128f : IO Unit := do
  let set := FipsParameterSet.SLHDSA_SHA2_128f
  let prims := Concrete.approvedPrimitives set
  letI : DecidableEq prims.Y := by
    change DecidableEq (Bytes 16)
    infer_instance
  let (publicKey, secretKey) := GeneralScheme.keygenInternal set.validatedParams prims
    (fixedBytes set.params.n 1) (fixedBytes set.params.n 2) (fixedBytes set.params.n 3)
  let message : List Byte := [0x53, 0x30, 0x39, 0x61]
  let signature := GeneralScheme.signInternal set.validatedParams prims message secretKey
    (fixedBytes set.params.n 4)
  let publicRaw := encodePublicKeyCore publicKey
  let secretRaw := encodeSecretKeyCore secretKey
  let signatureRaw := encodeSignatureCore signature
  match decodePublicKeyCore set publicRaw, decodeSecretKeyCore set secretRaw,
      decodeSignatureCore set signatureRaw with
  | .ok publicDecoded, .ok secretDecoded, .ok signatureDecoded => do
      ensure "SHA2-128f: decoded secret key preserves associated public key"
        (prims.core.yToBytes secretDecoded.pkRoot == prims.core.yToBytes publicDecoded.pkRoot)
      ensure "SHA2-128f: structured honest signature verifies"
        (GeneralScheme.verifyInternal set.validatedParams prims message
          signatureDecoded publicDecoded)
  | _, _, _ => throw (IO.userError "SHA2-128f: honest structured codec rejected")

def main : IO Unit := do
  for set in FipsParameterSet.all do
    checkProfile set
  exerciseHonestSha2_128f
  IO.println "SLH-DSA structured external codec tests: PASS \
    (12-profile exact layouts/rejection; all R/FORS/XMSS boundaries; SHA2-128f honest verification)"

end SLHDSA.ExternalCodecTests

def main : IO Unit := SLHDSA.ExternalCodecTests.main
