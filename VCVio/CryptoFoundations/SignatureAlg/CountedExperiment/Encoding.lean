/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.SigningView.Encoding
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment

/-!
# Cost and raw replies at the encoded signing boundary

Rejected requests and candidates perform no internal hash work. Every returned signing reply,
including None, keeps its declared attempt charge and chronological raw log entry.
-/

public section

open OracleComp OracleSpec

namespace SignatureAlg.SigningView

/-- A rejected request has no inner signing cost under any declared policy. -/
theorem costed_rejectingEncoding_sign_of_none {ι : Type} {spec : OracleSpec ι}
    {Request Msg PK SK Sig WireSig C : Type} [AddMonoid C]
    (policy : Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Msg PK SK Sig) (frame : Request → Option Msg)
    (encode : Sig → WireSig) (decode : WireSig → Option Sig)
    (pk : PK) (sk : SK) (request : Request) (hframe : frame request = none) :
    (costed policy .signer
      ((rejectingEncoding alg frame encode decode).sign pk sk request)).runAdd =
        pure (none, 0) := by
  simp only [rejectingEncoding_sign, hframe, costed_pure, AddWriterT.runAdd_pure]

/-- An invalid final frame or signature has no verifier cost under any declared policy. -/
theorem costed_rejectingEncoding_verify_of_none {ι : Type} {spec : OracleSpec ι}
    {Request Msg PK SK Sig WireSig C : Type} [AddMonoid C]
    (policy : Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Msg PK SK Sig) (frame : Request → Option Msg)
    (encode : Sig → WireSig) (decode : WireSig → Option Sig)
    (pk : PK) (request : Request) (wire : WireSig)
    (h : frame request = none ∨ decode wire = none) :
    (costed policy .verification
      ((rejectingEncoding alg frame encode decode).verify pk request wire)).runAdd =
        pure (false, 0) := by
  rcases h with hframe | hdecode
  · simp only [rejectingEncoding_verify, hframe, costed_pure, AddWriterT.runAdd_pure]
  · cases hframe : frame request <;>
      simp only [rejectingEncoding_verify, hframe, hdecode, costed_pure, AddWriterT.runAdd_pure]

/-- A returned rejection keeps exactly its attempt charge and its raw None log entry. -/
theorem countedPhase_rejectingEncoding_of_none {ι : Type} {spec : OracleSpec ι}
    {Request Msg PK SK Sig WireSig C : Type} [AddMonoid C]
    (policy : Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Msg PK SK Sig) (frame : Request → Option Msg)
    (encode : Sig → WireSig) (decode : WireSig → Option Sig)
    (pk : PK) (sk : SK) (request : Request) (hframe : frame request = none) :
    (countedPhase policy (rejectingEncoding alg frame encode decode) pk sk
      (liftM ((spec + (Request →ₒ Option WireSig)).query (.inr request)))).runAdd =
        pure ((none, [⟨request, none⟩]), policy (.signingAttempt request)) := by
  rw [countedPhase_signingQuery]
  simp [rejectingEncoding_sign, hframe, costed_pure, AddWriterT.runAdd_addTell]

end SignatureAlg.SigningView
