/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.SigningView.Encoding
public import HashSig.SLHDSA.Codec

/-!
# Canonical byte signatures around an internal SLH-DSA algorithm

A supplied partial byte-message frame determines the request interface. The strict canonical
signature codec keeps the optional service reply separate from the raw forged signature.
-/

public section

universe v

namespace SLHDSA.SigningView

/-- Frame requests and expose canonical signatures around the supplied internal algorithm. -/
@[expose] def fromInternalPure {m : Type → Type v} [Monad m] {Request : Type}
    (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core)
    (alg : SignatureAlg m (List Byte) (PublicKeyCore core) (SecretKeyCore core)
      (SLHDSA.SignatureCore vp.params core)) (frame : Request → Option (List Byte)) :
    SignatureAlg.SigningView m Request (PublicKeyCore core) (SecretKeyCore core)
      (List Byte) (Option (List Byte)) :=
  SignatureAlg.SigningView.rejectingEncoding alg frame
    (encodeSignature vp atomic) (fun wire => (decodeSignature vp atomic wire).toOption)

end SLHDSA.SigningView
