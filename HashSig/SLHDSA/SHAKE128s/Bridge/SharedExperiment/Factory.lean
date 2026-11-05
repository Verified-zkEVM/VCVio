/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.KeyLog

/-!
# Canonical pure SHAKE signing views of the complete FIPS experiment

Generated-key consistency aligns the supplied-public-key signer with the FIPS service signer.
The chronological free program retains actual keys, raw replies, forged candidate and verification;
key generation uses the original sampling computation with its pair presentation restored.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.Security

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The external presentation swaps the actual internal key-generation pair back unchanged. -/
theorem externalView_fips205_keygen :
    (externalView FIPS205.scheme).keygen = FIPS205.internal.keygen := by
  change Prod.swap <$> (Prod.swap <$> FIPS205.internal.keygen) = _
  simp only [Functor.map_map, Prod.swap_swap, id_map']

/-- The actual pure and service views agree on all algorithms at generated keys. -/
private theorem pureShakeView_fips205_generated_coherence :
    let left := pureShakeView FIPS205.params FIPS205.deterministicRand
      ($ᵗ FIPS205.core.PkSeed)
    let right := externalView FIPS205.scheme
    left.keygen = right.keygen ∧
      (∀ pk request wire, left.verify pk request wire = right.verify pk request wire) ∧
      (∀ keys ∈ support left.keygen, ∀ request,
        left.sign keys.1 keys.2 request = right.sign keys.1 keys.2 request) := by
  dsimp only
  refine ⟨(pureShakeView_keygen _ _ _).trans externalView_fips205_keygen.symm, ?_, ?_⟩
  · intro pk request wire
    cases hf : External.encodePureMessage request.context request.message with
    | error error =>
      simp [pureShakeView, SLHDSA.SigningView.fromInternalPure,
        SignatureAlg.SigningView.rejectingEncoding,
        SignatureAlg.SigningView.Encoding.sign, SignatureAlg.SigningView.Encoding.verify,
        externalView, FIPS205.scheme, hf, Except.toOption]
    | ok message =>
      cases hd : decodeSignature FIPS205.params
          (Concrete.shakeWireCodec FIPS205.params.params) wire <;>
        simp [pureShakeView, SLHDSA.SigningView.fromInternalPure,
          SignatureAlg.SigningView.rejectingEncoding,
        SignatureAlg.SigningView.Encoding.sign, SignatureAlg.SigningView.Encoding.verify,
          externalView, FIPS205.scheme, hf, hd, Except.toOption]
  · intro keys member request
    have consistent : keys.1 = FIPS205.SecretKeyCore.publicKey keys.2 :=
      Bridge.internal_keygen_consistent keys member
    cases hf : External.encodePureMessage request.context request.message <;>
      simp [pureShakeView, SLHDSA.SigningView.fromInternalPure,
        SignatureAlg.SigningView.rejectingEncoding,
        SignatureAlg.SigningView.Encoding.sign,
        externalView, FIPS205.scheme, hf, Except.toOption, consistent]; rfl


/-- The actual FIPS constructors share the full key-bearing chronological source. -/
theorem fullExperiment_pureShakeView_fips205
    (adversary : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) :
    SigningView.Events.fullExperiment
        (pureShakeView FIPS205.params FIPS205.deterministicRand ($ᵗ FIPS205.core.PkSeed))
        (Game.Counted.externalMain adversary) =
      SigningView.Events.fullExperiment (Game.Counted.externalView FIPS205.scheme)
        (Game.Counted.externalMain adversary) := by
  obtain ⟨keygen, verify, sign⟩ := pureShakeView_fips205_generated_coherence
  exact SigningView.Events.fullExperiment_congr_generated _ _ keygen verify sign
    (Game.Counted.externalMain adversary)

/-- The actual constructor refines the complete FIPS experiment without a caller key premise. -/
theorem countedExperiment_pureShakeView_fips205
    (adversary : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) :
    SigningView.countedExperiment sourcePolicy
      (pureShakeView FIPS205.params FIPS205.deterministicRand ($ᵗ FIPS205.core.PkSeed))
      (externalMain adversary) = canonicalExperiment FIPS205.scheme adversary := by
  have chronological := congrArg
    (fun program => (simulateQ (SigningView.Events.costImpl sourcePolicy) program).runAdd)
    (fullExperiment_pureShakeView_fips205 adversary)
  simp only [SigningView.Events.simulateQ_fullKeys] at chronological
  have observed := congrArg
    (fun program => (fun result :
      (((PublicKeyCore FIPS205.core × SecretKeyCore FIPS205.core) ×
        SigningView.Outcome Message Bytes (Option Bytes)) × SourceCounts) =>
      ({ toOutcome := result.1.2, cost := result.2 } :
        SigningView.Observation Message Bytes (Option Bytes) SourceCounts)) <$> program)
    chronological
  simpa only [canonicalExperiment, SigningView.countedExperiment,
    AddWriterT.runAdd_bind, AddWriterT.runAdd_pure, map_bind, map_pure, Functor.map_map,
    Prod.map, id_eq, add_zero, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_apply] using observed

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
