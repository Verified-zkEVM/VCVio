/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.External
public import HashSig.SLHDSA.Concrete.Sha2
public import HashSig.SLHDSA.Concrete.Keccak

/-!
# Checked FIPS 205 pre-hash adapter

This module closes the descriptor-parametric external semantics over the twelve hash algorithms
named by ACVP. An `Algorithm` determines the digest implementation, exact output width, and DER
OID together. The public signing and verification entry points also enforce FIPS 205 §10.2's
`2n`-byte collision-strength boundary.
-/

@[expose] public section

namespace SLHDSA.Concrete.Prehash

open OracleComp
open SLHDSA.External

/-- The complete pre-hash algorithm menu named by the FIPS 205 ACVP external interface. -/
inductive Algorithm where
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

/-- Every ACVP pre-hash algorithm, in registration order. -/
def all : List Algorithm :=
  [.sha2_224, .sha2_256, .sha2_384, .sha2_512, .sha2_512_224, .sha2_512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512, .shake128, .shake256]

/-- Exact ACVP spelling. -/
def Algorithm.name : Algorithm → String
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

/-- Parse an exact ACVP algorithm name. -/
def Algorithm.ofName? : String → Option Algorithm
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

@[simp] theorem Algorithm.ofName?_name (algorithm : Algorithm) :
    Algorithm.ofName? algorithm.name = some algorithm := by
  cases algorithm <;> rfl

/-- Digest width, including FIPS 205's fixed 32/64-byte SHAKE outputs. -/
def Algorithm.outputLength : Algorithm → ℕ
  | .sha2_224 | .sha2_512_224 | .sha3_224 => 28
  | .sha2_256 | .sha2_512_256 | .sha3_256 | .shake128 => 32
  | .sha2_384 | .sha3_384 => 48
  | .sha2_512 | .sha3_512 | .shake256 => 64

/-- FIPS 205 §10.2 compatibility: collision strength requires at least `2n` digest bytes. -/
def Algorithm.validFor (algorithm : Algorithm) (p : Params) : Bool :=
  2 * p.n ≤ algorithm.outputLength

/-- Proposition-level strength requirement. -/
def Algorithm.ValidFor (algorithm : Algorithm) (p : Params) : Prop :=
  2 * p.n ≤ algorithm.outputLength

theorem Algorithm.validFor_iff (algorithm : Algorithm) (p : Params) :
    algorithm.validFor p = true ↔ algorithm.ValidFor p := by
  simp [Algorithm.validFor, Algorithm.ValidFor]

/-- Complete DER encoding of the NIST hash-algorithm OID (`hashAlgs` arcs 1–12). -/
def Algorithm.oidDer : Algorithm → List Byte
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

/-- Concrete FFI-free digest bytes. -/
def Algorithm.digestRaw (algorithm : Algorithm) (message : List Byte) : ByteArray :=
  let input := ByteArray.mk message.toArray
  match algorithm with
  | .sha2_224 => Sha2.sha224 input
  | .sha2_256 => Sha2.sha256 input
  | .sha2_384 => Sha2.sha384 input
  | .sha2_512 => Sha2.sha512 input
  | .sha2_512_224 => Sha2.sha512_224 input
  | .sha2_512_256 => Sha2.sha512_256 input
  | .sha3_224 => Keccak.sha3_224 input
  | .sha3_256 => Keccak.sha3_256 input
  | .sha3_384 => Keccak.sha3_384 input
  | .sha3_512 => Keccak.sha3_512 input
  | .shake128 => Keccak.squeeze (Keccak.absorb input 168 0x1f) 32
  | .shake256 => Keccak.squeeze (Keccak.absorb input 136 0x1f) 64

@[simp] theorem Algorithm.digestRaw_size (algorithm : Algorithm) (message : List Byte) :
    (algorithm.digestRaw message).size = algorithm.outputLength := by
  cases algorithm <;> simp [Algorithm.digestRaw, Algorithm.outputLength]

/-- Fail-closed exact-width projection; there is no padding or truncation path. -/
def digestBytesExact (n : ℕ) (digest : ByteArray) : Except Error (Bytes n) :=
  if h : digest.size = n then
    .ok (Vector.ofFn fun i : Fin n => digest[i.val]'(by omega))
  else
    .error (.digestLengthMismatch n digest.size)

/-- Exact-width digest checked against the engine's advertised width. -/
def Algorithm.digest (algorithm : Algorithm) (message : List Byte) :
    Except Error (Bytes algorithm.outputLength) :=
  .ok (Vector.ofFn fun i : Fin algorithm.outputLength =>
    (algorithm.digestRaw message)[i.val]'(by
      rw [algorithm.digestRaw_size message]
      exact i.isLt))

/-- Canonical binding of one registry entry's DER OID and digest implementation. -/
def Algorithm.descriptor (algorithm : Algorithm) : PrehashDescriptor where
  oidDer := algorithm.oidDer
  outputLength := algorithm.outputLength
  digest := algorithm.digest

/-- Reject a pre-hash algorithm below the selected parameter set's claimed strength. -/
def requireStrength (p : Params) (algorithm : Algorithm) : Except Error Unit :=
  if algorithm.validFor p then
    .ok ()
  else
    .error (.prehashTooWeak p.n algorithm.outputLength)

/-- Checked Algorithm 23/25 message encoding. -/
def encodeMessage (p : Params) (algorithm : Algorithm) (context message : List Byte) :
    Except Error (List Byte) := do
  requireStrength p algorithm
  encodePrehashMessageWithDescriptor algorithm.descriptor context message

/-- Checked Algorithm 23 with caller-supplied hedging randomness. -/
def signWithRandomizer (vp : ValidatedParams) (prims : Primitives vp.params)
    (algorithm : Algorithm) (message context : List Byte) (sk : SecretKeyCore prims.core)
    (addrnd : prims.Y) : Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  requireStrength vp.params algorithm
  signPrehashWithDescriptorAndRandomizer vp prims algorithm.descriptor message context sk addrnd

/-- Checked deterministic Algorithm 23. -/
def signDeterministic (vp : ValidatedParams) (prims : Primitives vp.params)
    (pkSeedToRandomizer : prims.PkSeed → prims.Y) (algorithm : Algorithm)
    (message context : List Byte) (sk : SecretKeyCore prims.core) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  requireStrength vp.params algorithm
  signPrehashWithDescriptorDeterministic vp prims pkSeedToRandomizer algorithm.descriptor
    message context sk

/-- Checked hedged Algorithm 23 under the ideal total random source. -/
noncomputable def sign (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] (algorithm : Algorithm) (message context : List Byte)
    (sk : SecretKeyCore prims.core) :
    ProbComp (Except Error (GeneralScheme.SignatureCore vp prims.core)) :=
  match requireStrength vp.params algorithm with
  | .error error => pure (.error error)
  | .ok _ => signPrehashWithDescriptor vp prims algorithm.descriptor message context sk

/-- Checked Algorithm 25. Weak pairings and message-boundary failures reject as `false`. -/
def verify (vp : ValidatedParams) (prims : Primitives vp.params) [DecidableEq prims.Y]
    (algorithm : Algorithm) (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) : Bool :=
  match requireStrength vp.params algorithm with
  | .error _ => false
  | .ok _ => verifyPrehashWithDescriptor vp prims algorithm.descriptor message signature context pk

end SLHDSA.Concrete.Prehash
