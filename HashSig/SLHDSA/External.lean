/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.GeneralScheme
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

/-- Failures rejected at the FIPS external-message boundary. -/
inductive Error where
  /-- FIPS 205 limits the context string to at most 255 bytes. -/
  | contextTooLong (actual : ℕ)
  /-- FIPS 205 requires at least `2n` digest bytes for the claimed SLH-DSA security strength. -/
  | prehashTooWeak (n digestBytes : ℕ)
  /-- A built-in digest engine violated its advertised exact output width. -/
  | digestLengthMismatch (expected actual : ℕ)
deriving Repr, DecidableEq

/-- Abstract pre-hash/OID binding used by the descriptor-parametric semantics. This is an
extension boundary, not by itself an assertion that the pair is FIPS approved. Concrete FIPS
adapters provide a closed algorithm registry and strength checks. -/
structure PrehashDescriptor where
  oidDer : List Byte
  outputLength : ℕ
  digest : List Byte → Except Error (Bytes outputLength)

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

/-- Descriptor-parametric Algorithm 23/25 message input:
`0x01 || toByte(|ctx|, 1) || ctx || OID || PH(M)`. FIPS-facing adapters must bind the descriptor
to an approved algorithm and enforce the security-strength requirement. -/
def encodePrehashMessageWithDescriptor (prehash : PrehashDescriptor)
    (context message : List Byte) : Except Error (List Byte) := do
  let digest ← prehash.digest message
  encodeMessage 1 context (prehash.oidDer ++ digest.toList)

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

/-- Descriptor-parametric Algorithm 23 core with caller-supplied hedging randomness. -/
def signPrehashWithDescriptorAndRandomizer (vp : ValidatedParams)
    (prims : Primitives vp.params) (prehash : PrehashDescriptor) (message context : List Byte)
    (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  let encoded ← encodePrehashMessageWithDescriptor prehash context message
  return GeneralScheme.signInternal vp prims encoded sk addrnd

/-- Deterministic descriptor-parametric Algorithm 23 core. -/
def signPrehashWithDescriptorDeterministic (vp : ValidatedParams)
    (prims : Primitives vp.params) (pkSeedToRandomizer : prims.PkSeed → prims.Y)
    (prehash : PrehashDescriptor)
    (message context : List Byte) (sk : SecretKeyCore prims.core) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) :=
  signPrehashWithDescriptorAndRandomizer vp prims prehash message context sk
    (pkSeedToRandomizer sk.pkSeed)

/-- Descriptor-parametric hedged Algorithm 23 core under the ideal total random source. -/
noncomputable def signPrehashWithDescriptor (vp : ValidatedParams)
    (prims : Primitives vp.params) [SampleableType prims.Y] (prehash : PrehashDescriptor)
    (message context : List Byte)
    (sk : SecretKeyCore prims.core) :
    ProbComp (Except Error (GeneralScheme.SignatureCore vp prims.core)) :=
  match encodePrehashMessageWithDescriptor prehash context message with
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

/-- Descriptor-parametric Algorithm 25 core. An overlong context or digest failure is rejected. -/
def verifyPrehashWithDescriptor (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (prehash : PrehashDescriptor) (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) : Bool :=
  match encodePrehashMessageWithDescriptor prehash context message with
  | .error _ => false
  | .ok encoded => GeneralScheme.verifyInternal vp prims encoded signature pk

end SLHDSA.External
