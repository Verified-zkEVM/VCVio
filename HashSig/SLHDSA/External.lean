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
deriving Repr, DecidableEq

/-- A pre-hash function together with the complete DER encoding of its object identifier.
The output width is intrinsic, so the encoded pre-hash message cannot disagree with the
descriptor's declared digest length. -/
structure PrehashDescriptor where
  oidDer : List Byte
  outputLength : ℕ
  digest : List Byte → Bytes outputLength

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
