/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Game
public import HashSig.SLHDSA.Security.ByteModel
public import HashSig.SLHDSA.External
public import HashSig.SLHDSA.Concrete.Codec

/-!
# SLH-DSA-SHAKE-128s over one SHAKE256 random oracle, in pure mode

`scheme` is the library's FIPS 205 SLH-DSA (`HashSig.SLHDSA`) at the SLH-DSA-SHAKE-128s
parameters, with deterministic signing (`opt_rand = PK.seed`) and every SHAKE256 call one query of
a shared random oracle on byte strings (`SLHDSA.Security.shakeRomScheme`), exposed through the
pure-mode external interface of FIPS 205 Algorithms 22 and 24:

* a request's message and context are framed by `SLHDSA.External.encodePureMessage`, which rejects a
  context longer than 255 bytes;
* signatures are byte strings in the library's canonical encoding
  (`SLHDSA.encodeSignature`, `SLHDSA.decodeSignature` at `SLHDSA.Concrete.shakeWireCodec`), and
  verification rejects a string that does not decode.

The random oracle answers `m = 30` bytes (`SLHDSA.Security.shakeSpec`); FIPS 205 reads the first
`n = 16` of them for `F`, `H`, `T_ℓ`, `PRF` and `PRF_msg`, and all of them for `H_msg`.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.FIPS205

open SLHDSA SLHDSA.Security SLHDSA.Concrete SLHDSA.External

/-- The validated SLH-DSA-SHAKE-128s parameters. -/
abbrev params : ValidatedParams := FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams

/-- The SHAKE256 primitive context at those parameters. -/
abbrev core : CorePrimitives params.params := shakeCore params

/-- The random oracle's answers: `m = 30` bytes. -/
abbrev Answer : Type := SLHDSA.Bytes params.params.m

/-- Deterministic signing: `opt_rand` is the public seed. -/
@[expose] def deterministicRand (pk : PublicKeyCore core) : ProbComp core.Y :=
  pure pk.pkSeed

/-- FIPS 205's internal algorithms over one SHAKE256 random oracle, deterministic signing, with a
uniform public seed. -/
noncomputable abbrev internal :=
  shakeRomScheme params deterministicRand ($ᵗ core.PkSeed)

/-- The public key a secret key carries. -/
@[expose] def SecretKeyCore.publicKey (sk : SecretKeyCore core) : PublicKeyCore core :=
  ⟨sk.pkSeed, sk.pkRoot⟩

/-- **SLH-DSA-SHAKE-128s in pure mode over one SHAKE256 random oracle.** Key generation is
FIPS 205 Algorithm 21's; signing frames the request (Algorithm 22) and signs the framed message
with the internal signer, returning the canonical byte encoding of the signature, or `none` when
the context is too long; verification frames the request, decodes the signature and runs the
internal verifier (Algorithm 24), rejecting a request it cannot frame or a string it cannot
decode. -/
@[expose] noncomputable def scheme :
    Game.ExternalScheme Answer (PublicKeyCore core) (SecretKeyCore core) where
  keygen := (fun keys => (keys.2, keys.1)) <$> internal.keygen
  sign sk request :=
    match encodePureMessage request.context request.message with
    | .error _ => pure none
    | .ok message =>
      (fun signature => some (encodeSignature params (shakeWireCodec params.params) signature)) <$>
        internal.sign (SecretKeyCore.publicKey sk) sk message
  verify pk request signature :=
    match encodePureMessage request.context request.message with
    | .error _ => pure false
    | .ok message =>
      match decodeSignature params (shakeWireCodec params.params) signature with
      | .error _ => pure false
      | .ok decoded => internal.verify pk message decoded

end SLHDSA.SHAKE128s.FIPS205
