/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SigningView.Encoding
public import HashSig.SLHDSA.External.Framing
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Encoding

/-!
# Pure contexts at the canonical signing-view boundary

Concrete accepted and 256-byte contexts instantiate the production partial frame. A supplied
internal SLH algorithm and canonical codec are observed through the production counted engine.
Rejected attempts retain raw replies and their charge, then continue; invalid final requests
perform no internal verification work. No key-generation or signing algorithm is executed here.
-/

public section

open OracleComp OracleSpec
open SLHDSA

namespace SLHDSA.Examples.ContextRejection

/-- Context and payload bytes at the pure signing boundary. -/
abbrev Request := List Byte × List Byte

/-- Context precedes payload in this request pair. -/
@[expose] def frame (request : Request) : Option (List Byte) :=
  (External.encodePureMessage request.1 request.2).toOption

/-- A two-byte context and one-byte payload accepted by pure message framing. -/
@[expose] def accepted : Request := ([0xCA, 0xFE], [0x41])

/-- A 256-byte context and one-byte payload rejected by the pure context length limit. -/
@[expose] def oversized : Request := (List.replicate 256 0, [0x41])

/-- The accepted example encodes the pure tag, context length, context and payload exactly. -/
theorem accepted_frame : frame accepted = some [0, 2, 0xCA, 0xFE, 0x41] := by decide

/-- The oversized example fails pure message framing. -/
theorem oversized_frame : frame oversized = none := by
  have hlen : 255 < (List.replicate 256 (0 : Byte)).length := by
    simpa only [List.length_replicate] using (show 255 < 256 by decide)
  change (External.encodePureMessage (List.replicate 256 (0 : Byte)) [0x41]).toOption = none
  unfold External.encodePureMessage External.encodeMessage
  rw [External.requireContext_eq_error _ hlen]
  rfl

variable {ι : Type} {spec : OracleSpec ι} (vp : ValidatedParams)
variable {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
variable (alg : SignatureAlg (OracleComp spec) (List Byte)
  (PublicKeyCore core) (SecretKeyCore core) (SignatureCore vp.params core))

/-- The canonical strict wire codec around the supplied internal algorithms. -/
@[expose] def view := SLHDSA.SigningView.fromInternalPure vp atomic alg frame

/-- An accepted request uses its exact frame and canonical returned-signature encoder. -/
theorem accepted_sign (pk : PublicKeyCore core) (sk : SecretKeyCore core) :
    (view vp atomic alg).sign pk sk accepted =
      (some ∘ encodeSignature vp atomic) <$> alg.sign pk sk [0, 2, 0xCA, 0xFE, 0x41] := by
  simp only [view, SLHDSA.SigningView.fromInternalPure,
    SignatureAlg.SigningView.rejectingEncoding_sign, accepted_frame]

/-- A rejected request contributes exactly its actual None reply and attempted-signing charge. -/
theorem rejection_logged {C : Type} [AddMonoid C]
    (policy : SignatureAlg.SigningView.Event spec Request → C)
    (pk : PublicKeyCore core) (sk : SecretKeyCore core) :
    (SignatureAlg.SigningView.countedPhase policy (view vp atomic alg) pk sk
      (liftM ((spec + (Request →ₒ Option (List Byte))).query (.inr oversized)))).runAdd =
        pure ((none, [⟨oversized, none⟩]), policy (.signingAttempt oversized)) := by
  exact SignatureAlg.SigningView.countedPhase_rejectingEncoding_of_none policy alg frame
    (encodeSignature vp atomic) (fun wire => (decodeSignature vp atomic wire).toOption)
    pk sk oversized oversized_frame

/-- The client continues on None while retaining the chronological rejection and its cost. -/
theorem rejection_then_continue {C α : Type} [AddMonoid C]
    (policy : SignatureAlg.SigningView.Event spec Request → C)
    (pk : PublicKeyCore core) (sk : SecretKeyCore core)
    (next : Option (List Byte) → OracleComp (spec + (Request →ₒ Option (List Byte))) α) :
    (SignatureAlg.SigningView.countedPhase policy (view vp atomic alg) pk sk
      (liftM ((spec + (Request →ₒ Option (List Byte))).query (.inr oversized)) >>= next)).runAdd =
      (do
        let result ← (SignatureAlg.SigningView.countedPhase policy (view vp atomic alg)
          pk sk (next none)).runAdd
        return ((result.1.1, ⟨oversized, none⟩ :: result.1.2),
          policy (.signingAttempt oversized) + result.2)) := by
  rw [SignatureAlg.SigningView.countedPhase_bind, AddWriterT.runAdd_bind]
  rw [rejection_logged vp atomic alg policy pk sk]
  simp [Prod.map]

/-- An oversized final request returns false with zero verifier cost and no fallback execution. -/
theorem invalid_final {C : Type} [AddMonoid C]
    (policy : SignatureAlg.SigningView.Event spec Request → C)
    (pk : PublicKeyCore core) (wire : List Byte) :
    (SignatureAlg.SigningView.costed policy .verification
      ((view vp atomic alg).verify pk oversized wire)).runAdd = pure (false, 0) :=
  SignatureAlg.SigningView.costed_rejectingEncoding_verify_of_none policy alg frame
    (encodeSignature vp atomic) (fun bytes => (decodeSignature vp atomic bytes).toOption)
    pk oversized wire (Or.inl oversized_frame)

end SLHDSA.Examples.ContextRejection
