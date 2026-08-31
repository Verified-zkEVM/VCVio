/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Encoding
public import HashSig.SLHDSA.FipsParams

/-!
# SLH-DSA Fixed-Width Wire Codecs

Transparent, exactly width-indexed carrier aliases for public keys, secret keys, and signatures.
These codecs enforce the FIPS 205 Table 2 lengths for every approved parameter set; they
intentionally make no semantic claim about the bytes until later construction sessions supply
structured key and signature decoders.
-/

@[expose] public section

namespace SLHDSA

/-- Exact public-key wire bytes (`PK.seed || PK.root`). -/
abbrev PublicKeyBytes (s : FipsParameterSet) := Bytes s.params.publicKeyBytes

/-- Exact secret-key wire bytes (`SK.seed || SK.prf || PK.seed || PK.root`). -/
abbrev SecretKeyBytes (s : FipsParameterSet) := Bytes s.params.secretKeyBytes

/-- Exact signature wire bytes for the selected approved profile. -/
abbrev SignatureBytes (s : FipsParameterSet) := Bytes s.params.signatureBytes

/-- Reject any public-key input whose length is not exactly `2n`. -/
def decodePublicKey (s : FipsParameterSet) (raw : List Byte) :
    Except CodecError (PublicKeyBytes s) :=
  decodeExact s.params.publicKeyBytes raw

/-- Reject any secret-key input whose length is not exactly `4n`. -/
def decodeSecretKey (s : FipsParameterSet) (raw : List Byte) :
    Except CodecError (SecretKeyBytes s) :=
  decodeExact s.params.secretKeyBytes raw

/-- Reject any signature input whose length is not the exact FIPS Table 2 size. -/
def decodeSignature (s : FipsParameterSet) (raw : List Byte) :
    Except CodecError (SignatureBytes s) :=
  decodeExact s.params.signatureBytes raw

def encodePublicKey {s : FipsParameterSet} (key : PublicKeyBytes s) : List Byte := encodeExact key

def encodeSecretKey {s : FipsParameterSet} (key : SecretKeyBytes s) : List Byte := encodeExact key

def encodeSignature {s : FipsParameterSet} (signature : SignatureBytes s) : List Byte :=
  encodeExact signature

@[simp] theorem decodePublicKey_encode {s : FipsParameterSet} (key : PublicKeyBytes s) :
    decodePublicKey s (encodePublicKey key) = .ok key := by
  exact decodeExact_encode key

@[simp] theorem decodeSecretKey_encode {s : FipsParameterSet} (key : SecretKeyBytes s) :
    decodeSecretKey s (encodeSecretKey key) = .ok key := by
  exact decodeExact_encode key

@[simp] theorem decodeSignature_encode {s : FipsParameterSet} (signature : SignatureBytes s) :
    decodeSignature s (encodeSignature signature) = .ok signature := by
  exact decodeExact_encode signature

end SLHDSA
