/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.GeneralScheme
public import HashSig.SLHDSA.Concrete.Sha2
public import HashSig.SLHDSA.Concrete.Keccak
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# SLH-DSA external interfaces

The pure and pre-hash message encodings and the external key-generation, signing, and
verification interfaces from FIPS 205 Algorithms 21--25. The randomized definitions use the
repository's ideal, total `SampleableType` source. An implementation whose random-bit generator
can fail must translate that failure before calling the explicit-seed or explicit-randomizer
boundary exposed here.

## References

- NIST FIPS 205, Section 10, Algorithms 21--25
-/

@[expose] public section

namespace SLHDSA.External

open OracleComp
open Concrete

/-- Failures rejected at the FIPS external-message boundary. -/
inductive Error where
  /-- FIPS 205 limits the context string to at most 255 bytes. -/
  | contextTooLong (actual : ℕ)
deriving Repr, DecidableEq

/-- A pre-hash function together with the complete DER encoding of its object identifier.
The output width is intrinsic, so the encoded pre-hash message cannot disagree with the
descriptor's declared digest length. -/
structure PrehashDescriptor where
  oidDer : List Byte
  outputLength : ℕ
  digest : List Byte → Bytes outputLength

/-- The complete pre-hash algorithm menu accepted by the FIPS 205 ACVP external interface.
SHAKE128 is squeezed to 256 bits and SHAKE256 to 512 bits, as required by Algorithm 23. -/
inductive PrehashAlgorithm where
  | sha2_224
  | sha2_256
  | sha2_384
  | sha2_512
  | sha2_512_224
  | sha2_512_256
  | sha3_224
  | sha3_256
  | sha3_384
  | sha3_512
  | shake128
  | shake256
deriving Repr, DecidableEq, BEq

/-- Every approved pre-hash algorithm, in the ACVP registration order. -/
def allPrehashAlgorithms : List PrehashAlgorithm :=
  [.sha2_224, .sha2_256, .sha2_384, .sha2_512, .sha2_512_224, .sha2_512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512, .shake128, .shake256]

/-- ACVP spelling of an approved pre-hash algorithm. -/
def PrehashAlgorithm.name : PrehashAlgorithm → String
  | .sha2_224 => "SHA2-224"
  | .sha2_256 => "SHA2-256"
  | .sha2_384 => "SHA2-384"
  | .sha2_512 => "SHA2-512"
  | .sha2_512_224 => "SHA2-512/224"
  | .sha2_512_256 => "SHA2-512/256"
  | .sha3_224 => "SHA3-224"
  | .sha3_256 => "SHA3-256"
  | .sha3_384 => "SHA3-384"
  | .sha3_512 => "SHA3-512"
  | .shake128 => "SHAKE-128"
  | .shake256 => "SHAKE-256"

/-- Parse the exact ACVP spelling of an approved pre-hash algorithm. -/
def PrehashAlgorithm.ofName? : String → Option PrehashAlgorithm
  | "SHA2-224" => some .sha2_224
  | "SHA2-256" => some .sha2_256
  | "SHA2-384" => some .sha2_384
  | "SHA2-512" => some .sha2_512
  | "SHA2-512/224" => some .sha2_512_224
  | "SHA2-512/256" => some .sha2_512_256
  | "SHA3-224" => some .sha3_224
  | "SHA3-256" => some .sha3_256
  | "SHA3-384" => some .sha3_384
  | "SHA3-512" => some .sha3_512
  | "SHAKE-128" => some .shake128
  | "SHAKE-256" => some .shake256
  | _ => none

@[simp] theorem PrehashAlgorithm.ofName?_name (algorithm : PrehashAlgorithm) :
    PrehashAlgorithm.ofName? algorithm.name = some algorithm := by
  cases algorithm <;> rfl

/-- Digest widths fixed by FIPS 180-4/FIPS 202 and the FIPS 205 SHAKE choices. -/
def PrehashAlgorithm.outputLength : PrehashAlgorithm → ℕ
  | .sha2_224 | .sha2_512_224 | .sha3_224 => 28
  | .sha2_256 | .sha2_512_256 | .sha3_256 | .shake128 => 32
  | .sha2_384 | .sha3_384 => 48
  | .sha2_512 | .sha3_512 | .shake256 => 64

/-- Complete DER encoding of the NIST hash-algorithm object identifier (`hashAlgs` arcs 1–12). -/
def PrehashAlgorithm.oidDer : PrehashAlgorithm → List Byte
  | .sha2_256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
  | .sha2_384 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02]
  | .sha2_512 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03]
  | .sha2_224 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x04]
  | .sha2_512_224 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x05]
  | .sha2_512_256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x06]
  | .sha3_224 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x07]
  | .sha3_256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x08]
  | .sha3_384 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x09]
  | .sha3_512 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0a]
  | .shake128 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b]
  | .shake256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0c]

/-- Project an exact-width digest engine into its intrinsic byte-vector boundary. Each approved
engine below has the corresponding fixed output width; executable KATs pin that invariant. -/
def digestBytes (n : ℕ) (digest : ByteArray) : Bytes n :=
  Vector.ofFn fun i : Fin n => digest[i.val]?.getD 0

/-- The concrete, FFI-free digest for an approved pre-hash algorithm. -/
def PrehashAlgorithm.digest (algorithm : PrehashAlgorithm) (message : List Byte) :
    Bytes algorithm.outputLength :=
  let input := ByteArray.mk message.toArray
  match algorithm with
  | .sha2_224 => digestBytes 28 (Sha2.sha224 input)
  | .sha2_256 => digestBytes 32 (Sha2.sha256 input)
  | .sha2_384 => digestBytes 48 (Sha2.sha384 input)
  | .sha2_512 => digestBytes 64 (Sha2.sha512 input)
  | .sha2_512_224 => digestBytes 28 (Sha2.sha512_224 input)
  | .sha2_512_256 => digestBytes 32 (Sha2.sha512_256 input)
  | .sha3_224 => digestBytes 28 (Keccak.sha3_224 input)
  | .sha3_256 => digestBytes 32 (Keccak.sha3_256 input)
  | .sha3_384 => digestBytes 48 (Keccak.sha3_384 input)
  | .sha3_512 => digestBytes 64 (Keccak.sha3_512 input)
  | .shake128 => digestBytes 32 (Keccak.shake128 input 32)
  | .shake256 => digestBytes 64 (Keccak.shake256 input 64)

/-- Canonical FIPS descriptor for an approved pre-hash algorithm. -/
def PrehashAlgorithm.descriptor (algorithm : PrehashAlgorithm) : PrehashDescriptor where
  oidDer := algorithm.oidDer
  outputLength := algorithm.outputLength
  digest := algorithm.digest

/-- Common FIPS external-message encoder. Domain `0` denotes pure signing and domain `1`
denotes pre-hash signing. -/
def encodeMessage (domain : Byte) (context body : List Byte) : Except Error (List Byte) :=
  if context.length ≤ 255 then
    .ok ([domain, UInt8.ofNat context.length] ++ context ++ body)
  else
    .error (.contextTooLong context.length)

/-- Algorithm 22/24 message input: `0x00 || toByte(|ctx|, 1) || ctx || M`. -/
def encodePureMessage (context message : List Byte) : Except Error (List Byte) :=
  encodeMessage 0 context message

/-- Algorithm 23/25 message input:
`0x01 || toByte(|ctx|, 1) || ctx || OID || PH(M)`. -/
def encodePrehashMessage (prehash : PrehashDescriptor) (context message : List Byte) :
    Except Error (List Byte) :=
  encodeMessage 1 context (prehash.oidDer ++ (prehash.digest message).toList)

/-- Algorithm 21 after its approved random-bit generator has produced the three seeds. This
explicit boundary is the deterministic entry point used by ACVP key-generation vectors. -/
def keygenWithSeeds (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    PublicKeyCore prims.core × SecretKeyCore prims.core :=
  GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed

/-- Algorithm 21 under the repository's ideal total random source. -/
noncomputable def keygen (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] :
    ProbComp (PublicKeyCore prims.core × SecretKeyCore prims.core) := do
  let skSeed ← $ᵗ prims.SkSeed
  let skPrf ← $ᵗ prims.SkPrf
  let pkSeed ← $ᵗ prims.PkSeed
  pure (keygenWithSeeds vp prims skSeed skPrf pkSeed)

/-- Algorithm 22 with caller-supplied hedging randomness. -/
def signPureWithRandomizer (vp : ValidatedParams) (prims : Primitives vp.params)
    (message context : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  let encoded ← encodePureMessage context message
  return GeneralScheme.signInternal vp prims encoded sk addrnd

/-- Deterministic Algorithm 22. FIPS sets `opt_rand = PK.seed`; the conversion is explicit
because the proof-level primitive interface deliberately keeps `PkSeed` and `Y` independent. -/
def signPureDeterministic (vp : ValidatedParams) (prims : Primitives vp.params)
    (pkSeedToRandomizer : prims.PkSeed → prims.Y) (message context : List Byte)
    (sk : SecretKeyCore prims.core) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) :=
  signPureWithRandomizer vp prims message context sk (pkSeedToRandomizer sk.pkSeed)

/-- Default hedged Algorithm 22 under the repository's ideal total random source. -/
noncomputable def signPure (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] (message context : List Byte) (sk : SecretKeyCore prims.core) :
    ProbComp (Except Error (GeneralScheme.SignatureCore vp prims.core)) :=
  match encodePureMessage context message with
  | .error error => pure (.error error)
  | .ok encoded => do
      let addrnd ← $ᵗ prims.Y
      pure (.ok (GeneralScheme.signInternal vp prims encoded sk addrnd))

/-- Algorithm 23 with caller-supplied hedging randomness. -/
def signPrehashWithRandomizer (vp : ValidatedParams) (prims : Primitives vp.params)
    (prehash : PrehashDescriptor) (message context : List Byte)
    (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  let encoded ← encodePrehashMessage prehash context message
  return GeneralScheme.signInternal vp prims encoded sk addrnd

/-- Deterministic Algorithm 23 with explicit `PK.seed`-to-node conversion. -/
def signPrehashDeterministic (vp : ValidatedParams) (prims : Primitives vp.params)
    (pkSeedToRandomizer : prims.PkSeed → prims.Y) (prehash : PrehashDescriptor)
    (message context : List Byte) (sk : SecretKeyCore prims.core) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) :=
  signPrehashWithRandomizer vp prims prehash message context sk
    (pkSeedToRandomizer sk.pkSeed)

/-- Default hedged Algorithm 23 under the repository's ideal total random source. -/
noncomputable def signPrehash (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] (prehash : PrehashDescriptor) (message context : List Byte)
    (sk : SecretKeyCore prims.core) :
    ProbComp (Except Error (GeneralScheme.SignatureCore vp prims.core)) :=
  match encodePrehashMessage prehash context message with
  | .error error => pure (.error error)
  | .ok encoded => do
      let addrnd ← $ᵗ prims.Y
      pure (.ok (GeneralScheme.signInternal vp prims encoded sk addrnd))

/-- Algorithm 24. An overlong context is rejected as `false`. -/
def verifyPure (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) : Bool :=
  match encodePureMessage context message with
  | .error _ => false
  | .ok encoded => GeneralScheme.verifyInternal vp prims encoded signature pk

/-- Algorithm 25. An overlong context is rejected as `false`. -/
def verifyPrehash (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (prehash : PrehashDescriptor) (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) : Bool :=
  match encodePrehashMessage prehash context message with
  | .error _ => false
  | .ok encoded => GeneralScheme.verifyInternal vp prims encoded signature pk

end SLHDSA.External
