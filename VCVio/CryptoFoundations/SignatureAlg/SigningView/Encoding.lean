/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.SigningView

/-!
# Request framing and signature encoding for a signing service

The optional reply carrier records pure service rejection separately from forged signatures.
The same supplied public key and underlying algorithms handle successful requests.
-/

public section

universe v

namespace SignatureAlg.SigningView.Encoding

/-- Reject an invalid request before signing, otherwise encode its actual signature reply. -/
@[expose] def sign {m : Type → Type v} [Monad m] {Request Msg SK Sig WireSig : Type}
    (frame : Request → Option Msg) (encode : Sig → WireSig) (signer : SK → Msg → m Sig)
    (sk : SK) (request : Request) : m (Option WireSig) :=
  match frame request with
  | none => pure none
  | some message => (some ∘ encode) <$> signer sk message

/-- Reject invalid framing or parsing; decoded candidates execute the verifier. -/
@[expose] def verify {m : Type → Type v} [Monad m] {Request Msg PK Sig WireSig : Type}
    (frame : Request → Option Msg) (decode : WireSig → Option Sig)
    (verifier : PK → Msg → Sig → m Bool) (pk : PK) (request : Request) (wire : WireSig) : m Bool :=
  match frame request with
  | none => pure false
  | some message => match decode wire with
    | none => pure false
    | some signature => verifier pk message signature

end SignatureAlg.SigningView.Encoding

namespace SignatureAlg.SigningView

/-- A partial request frame and signature codec around the same internal algorithms. -/
@[expose] def rejectingEncoding {m : Type → Type v} [Monad m]
    {Request Msg PK SK Sig WireSig : Type} (alg : SignatureAlg m Msg PK SK Sig)
    (frame : Request → Option Msg) (encode : Sig → WireSig) (decode : WireSig → Option Sig) :
    SignatureAlg.SigningView m Request PK SK WireSig (Option WireSig) where
  keygen := alg.keygen
  sign pk sk request := Encoding.sign frame encode (fun key message => alg.sign pk key message)
    sk request
  verify := Encoding.verify frame decode alg.verify
  readback := id

/-- Request and signature encoding preserve the entire internal key-generation program. -/
@[simp] theorem rejectingEncoding_keygen {m : Type → Type v} [Monad m]
    {Request Msg PK SK Sig WireSig : Type} (alg : SignatureAlg m Msg PK SK Sig)
    (frame : Request → Option Msg) (encode : Sig → WireSig) (decode : WireSig → Option Sig) :
    (rejectingEncoding alg frame encode decode).keygen = alg.keygen := rfl

/-- Successful signing uses the supplied public key and encodes the returned signature. -/
@[simp] theorem rejectingEncoding_sign {m : Type → Type v} [Monad m]
    {Request Msg PK SK Sig WireSig : Type} (alg : SignatureAlg m Msg PK SK Sig)
    (frame : Request → Option Msg) (encode : Sig → WireSig) (decode : WireSig → Option Sig)
    (pk : PK) (sk : SK) (request : Request) :
    (rejectingEncoding alg frame encode decode).sign pk sk request =
      match frame request with
      | none => pure none
      | some message => (some ∘ encode) <$> alg.sign pk sk message := rfl

/-- An invalid frame or signature rejects before running the internal verifier. -/
@[simp] theorem rejectingEncoding_verify {m : Type → Type v} [Monad m]
    {Request Msg PK SK Sig WireSig : Type} (alg : SignatureAlg m Msg PK SK Sig)
    (frame : Request → Option Msg) (encode : Sig → WireSig) (decode : WireSig → Option Sig)
    (pk : PK) (request : Request) (wire : WireSig) :
    (rejectingEncoding alg frame encode decode).verify pk request wire =
      match frame request with
      | none => pure false
      | some message => match decode wire with
        | none => pure false
        | some signature => alg.verify pk message signature := rfl

/-- Optional wire replies are read without a default signature or an additional wrapper. -/
@[simp] theorem rejectingEncoding_readback {m : Type → Type v} [Monad m]
    {Request Msg PK SK Sig WireSig : Type} (alg : SignatureAlg m Msg PK SK Sig)
    (frame : Request → Option Msg) (encode : Sig → WireSig) (decode : WireSig → Option Sig) :
    (rejectingEncoding alg frame encode decode).readback = id := rfl

end SignatureAlg.SigningView
