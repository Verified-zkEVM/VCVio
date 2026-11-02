/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SigningView.Encoding
public import HashSig.SLHDSA.Codec.Option
public import HashSig.SLHDSA.External.Framing
public import HashSig.SLHDSA.Concrete.Codec
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure

/-!
# Canonical signing-view framing and data flow

Patterned signatures and distinct keys exercise the actual internal-view constructor, pure
message frame and canonical codecs at three SHAKE widths. The supplied internal algorithm records
its exact arguments; the fixture does not perform cryptographic signing or key generation.
-/

public section

namespace SLHDSA.Refactor.SigningViewEncoding

private abbrev TraceEntry := Nat × List Byte × List Byte × List Byte × List Byte
private abbrev Trace := List TraceEntry
private abbrev Core (vp : ValidatedParams) := (Concrete.shakePrimitives vp.params).core

private def pattern (length salt : Nat) : List Byte :=
  List.ofFn fun i : Fin length => UInt8.ofNat (17 * i.val + 29 * (i.val / 251) + salt)

private def publicKey (vp : ValidatedParams) : PublicKeyCore (Core vp) :=
  ⟨Vector.ofFn (fun i => UInt8.ofNat (3 * i.val + 7)),
    Vector.ofFn (fun i => UInt8.ofNat (5 * i.val + 19))⟩

private def secretKey (vp : ValidatedParams) : SecretKeyCore (Core vp) :=
  ⟨Vector.ofFn (fun i => UInt8.ofNat (7 * i.val + 31)),
    Vector.ofFn (fun i => UInt8.ofNat (11 * i.val + 43)),
    Vector.ofFn (fun i => UInt8.ofNat (13 * i.val + 59)),
    Vector.ofFn (fun i => UInt8.ofNat (19 * i.val + 71))⟩

private def tracedAlg (vp : ValidatedParams) (reply : SignatureCore vp.params (Core vp)) :
    SignatureAlg (StateM Trace) (List Byte) (PublicKeyCore (Core vp))
      (SecretKeyCore (Core vp)) (SignatureCore vp.params (Core vp)) where
  keygen := pure (publicKey vp, secretKey vp)
  sign pk sk message := do
    modify (· ++ [(1, encodePublicKey (Concrete.shakeWireCodec vp.params) pk,
      encodeSecretKey (Concrete.shakeWireCodec vp.params) sk, message,
      encodeSignature vp (Concrete.shakeWireCodec vp.params) reply)])
    return reply
  verify pk message signature := do
    modify (· ++ [(2, encodePublicKey (Concrete.shakeWireCodec vp.params) pk, [], message,
      encodeSignature vp (Concrete.shakeWireCodec vp.params) signature)])
    return true

private def frame (request : List Byte × List Byte) : Option (List Byte) :=
  (External.encodePureMessage request.1 request.2).toOption

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def requireSignature (vp : ValidatedParams) (wire : List Byte) :
    IO (SignatureCore vp.params (Core vp)) :=
  match decodeSignature vp (Concrete.shakeWireCodec vp.params) wire with
  | .ok signature => pure signature
  | .error _ => throw (IO.userError "patterned exact-width signature must decode")

private def runCase (set : FipsParameterSet) : IO Unit := do
  let vp := set.validatedParams
  let atomic := Concrete.shakeWireCodec vp.params
  let returnedWire := pattern vp.params.signatureBytes 37
  let candidateWire := pattern vp.params.signatureBytes 113
  let returned ← requireSignature vp returnedWire
  let candidate ← requireSignature vp candidateWire
  check (encodeSignature vp atomic returned == returnedWire &&
    encodeSignature vp atomic candidate == candidateWire && returnedWire != candidateWire)
    "canonical patterned signatures retain every byte and distinguish candidate from reply"
  let pk := publicKey vp
  let sk := secretKey vp
  let pkWire := encodePublicKey atomic pk
  let skWire := encodeSecretKey atomic sk
  let expectedPk := (List.ofFn fun i : Fin vp.params.n => UInt8.ofNat (3 * i.val + 7)) ++
    (List.ofFn fun i : Fin vp.params.n => UInt8.ofNat (5 * i.val + 19))
  let expectedSk := (List.ofFn fun i : Fin vp.params.n => UInt8.ofNat (7 * i.val + 31)) ++
    (List.ofFn fun i : Fin vp.params.n => UInt8.ofNat (11 * i.val + 43)) ++
    (List.ofFn fun i : Fin vp.params.n => UInt8.ofNat (13 * i.val + 59)) ++
    (List.ofFn fun i : Fin vp.params.n => UInt8.ofNat (19 * i.val + 71))
  check (pkWire == expectedPk && skWire == expectedSk &&
    pkWire != skWire.drop (2 * vp.params.n) && pkWire.any (· != 0) && skWire.any (· != 0))
    "distinct nonzero public and secret fields retain their canonical order"
  let view := SigningView.fromInternalPure vp atomic (tracedAlg vp returned) frame
  let context : List Byte := [0xa3, 0x16, 0xc7]
  let message : List Byte := [0xd9, 0x52, 0xb1, 0x08]
  let expectedFrame : List Byte := [0, 3] ++ context ++ message
  let (reply, signTrace) := (view.sign pk sk (context, message)).run []
  check (reply == some returnedWire &&
    signTrace == [(1, pkWire, skWire, expectedFrame, returnedWire)])
    "signing forwards the supplied PK, SK, framed bytes and encoded returned signature"
  let (verified, verifyTrace) := (view.verify pk (context, message) candidateWire).run []
  check (verified && verifyTrace == [(2, pkWire, [], expectedFrame, candidateWire)])
    "verification forwards the supplied PK, framed bytes and distinct decoded candidate"
  let longContext := pattern 255 149
  let longFrame : List Byte := [0, 255] ++ longContext ++ message
  let (longReply, longTrace) := (view.sign pk sk (longContext, message)).run []
  check (longReply == some returnedWire &&
    longTrace == [(1, pkWire, skWire, longFrame, returnedWire)])
    "context255 executes the exact successful pure frame"
  let invalidContext := pattern 256 173
  let (rejected, rejectedTrace) := (view.sign pk sk (invalidContext, message)).run []
  check (rejected == none && rejectedTrace == [])
    "context256 returns None before the internal signer"
  let (invalid, invalidTrace) := (view.verify pk (invalidContext, message) candidateWire).run []
  check (!invalid && invalidTrace == []) "context256 rejects before the internal verifier"
  let (malformed, malformedTrace) := (view.verify pk (context, message) []).run []
  check (!malformed && malformedTrace == []) "malformed wire rejects before the internal verifier"
  IO.println s!"canonical signing-view patterned data flow PASS: {set.name} (n={vp.params.n})"

/-- Execute exact canonical codec and framed argument checks at 128s, 192f and 256s. -/
def run : IO Unit := do
  runCase .SLHDSA_SHAKE_128s
  runCase .SLHDSA_SHAKE_192f
  runCase .SLHDSA_SHAKE_256s
  IO.println "SLH signing-view constructor checks passed"

end SLHDSA.Refactor.SigningViewEncoding

/-- Run the canonical signing-view argument and rejection controls. -/
def main : IO Unit := SLHDSA.Refactor.SigningViewEncoding.run
