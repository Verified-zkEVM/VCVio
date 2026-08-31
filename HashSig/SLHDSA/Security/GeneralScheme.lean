/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.GeneralScheme
public import HashSig.SLHDSA.Security.OracleSurface

/-!
# General SLH-DSA security interface

This module instantiates the security experiment boundary with the arbitrary-depth construction.
Key generation samples all three FIPS seeds, signing samples fresh optional randomness, and both
signing and verification use the same external-message encoder.

The encoder is deliberately a parameter.  A master EUF-CMA theorem must either assume it is
injective on `MessageInput` or add a collision/second-preimage term for non-injective pre-hashing.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA.GeneralScheme

/-- Generate a key pair whose public fields are definitionally shared with the secret key. -/
def generateKeyPair (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    Security.GeneratedKeyPair prims :=
  let pkRoot := GeneralHypertree.root vp prims skSeed pkSeed
  {
    publicKey := ⟨pkSeed, pkRoot⟩
    secretKey := ⟨skSeed, skPrf, pkSeed, pkRoot⟩
    seed_eq := rfl
    root_eq := rfl
  }

/-- The actual arbitrary-`d` construction as the scheme attacked by the classical EUF/SUF
experiments.  Public hashing is interpreted by `prims`; probabilistic choices are limited to key
material and the per-signature optional randomizer. -/
noncomputable def securityInterface (vp : ValidatedParams)
    (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y]
    (encode : Security.MessageInput → List Byte) : Security.SchemeInterface prims where
  Signature := SignatureCore vp prims.core
  randomizer := SignatureCore.randomness
  keygen := do
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    let pkSeed ← $ᵗ prims.PkSeed
    return generateKeyPair vp prims skSeed skPrf pkSeed
  sign := fun sk request => do
    let addrnd ← $ᵗ prims.Y
    return signInternal vp prims (encode request) sk addrnd
  verify := fun pk request sig => verifyInternal vp prims (encode request) sig pk

@[simp]
theorem securityInterface_randomizer (vp : ValidatedParams)
    (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y]
    (encode : Security.MessageInput → List Byte) (sig : SignatureCore vp prims.core) :
    (securityInterface vp prims encode).randomizer sig = sig.randomness := rfl

@[simp]
theorem securityInterface_verify (vp : ValidatedParams)
    (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y]
    (encode : Security.MessageInput → List Byte) (pk : PublicKeyCore prims.core)
    (request : Security.MessageInput) (sig : SignatureCore vp prims.core) :
    (securityInterface vp prims encode).verify pk request sig =
      verifyInternal vp prims (encode request) sig pk := rfl

end SLHDSA.GeneralScheme
