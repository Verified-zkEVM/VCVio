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
public import HashSig.SLHDSA.SHAKE128s.FIPS205.Params
public import HashSig.SLHDSA.SigningView.Encoding

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

/-- The strict signing view of the actual deterministic internal algorithms. -/
@[expose] noncomputable def signingView :=
  SLHDSA.SigningView.fromInternalPure params (shakeWireCodec params.params) internal
    (fun request : Message => (encodePureMessage request.context request.message).toOption)

/-- Invalid contexts reject; valid requests sign with the public key and encode fully. -/
@[simp] theorem signingView_sign (pk : PublicKeyCore core) (sk : SecretKeyCore core)
    (request : Message) :
    signingView.sign pk sk request =
      match encodePureMessage request.context request.message with
      | .error _ => pure none
      | .ok message =>
        (fun signature => some (encodeSignature params
          (shakeWireCodec params.params) signature)) <$>
          internal.sign pk sk message := by
  cases framed : encodePureMessage request.context request.message <;>
    simp only [signingView, SLHDSA.SigningView.fromInternalPure,
      SignatureAlg.SigningView.rejectingEncoding, SignatureAlg.SigningView.Encoding.sign,
      framed, Except.toOption, Function.comp_def]

/-- Framing or complete decoding rejects before verification; decoded candidates execute it. -/
@[simp] theorem signingView_verify (pk : PublicKeyCore core) (request : Message)
    (wire : Bytes) :
    signingView.verify pk request wire =
      match encodePureMessage request.context request.message with
      | .error _ => pure false
      | .ok message =>
        match decodeSignature params (shakeWireCodec params.params) wire with
        | .error _ => pure false
        | .ok signature => internal.verify pk message signature := by
  cases framed : encodePureMessage request.context request.message <;>
    cases decoded : decodeSignature params (shakeWireCodec params.params) wire <;>
    simp only [signingView, SLHDSA.SigningView.fromInternalPure,
      SignatureAlg.SigningView.rejectingEncoding, SignatureAlg.SigningView.Encoding.verify,
      framed, decoded, Except.toOption]

/-- **SLH-DSA-SHAKE-128s in pure mode over one SHAKE256 random oracle.** Key generation is
FIPS 205 Algorithm 21's; signing frames the request (Algorithm 22) and signs the framed message
with the internal signer, returning the canonical byte encoding of the signature, or `none` when
the context is too long; verification frames the request, decodes the signature and runs the
internal verifier (Algorithm 24), rejecting a request it cannot frame or a string it cannot
decode. -/
@[expose] noncomputable def scheme :
    Game.ExternalScheme Answer (PublicKeyCore core) (SecretKeyCore core) where
  keygen := Prod.swap <$> signingView.keygen
  sign sk request := signingView.sign (SecretKeyCore.publicKey sk) sk request
  verify := signingView.verify

end SLHDSA.SHAKE128s.FIPS205
