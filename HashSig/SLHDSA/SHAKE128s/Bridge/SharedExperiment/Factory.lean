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
The entire counted free program retains raw replies, forged candidate, verification and costs;
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

private theorem countedExperiment_congr_generated
    {ι : Type} {spec : OracleSpec ι} {Request PK SK Sig Reply C : Type} [AddMonoid C]
    (policy : SigningView.Event spec Request → C)
    (left right : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (hkeygen : left.keygen = right.keygen)
    (hverify : ∀ pk request sig, left.verify pk request sig = right.verify pk request sig)
    (hsign : ∀ keys ∈ support left.keygen, ∀ request,
      left.sign keys.1 keys.2 request = right.sign keys.1 keys.2 request)
    (adversary : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    SigningView.countedExperiment policy left adversary =
      SigningView.countedExperiment policy right adversary := by
  have phaseEq (keys : PK × SK) (member : keys ∈ support left.keygen) :
      SigningView.countedPhase policy left keys.1 keys.2 (adversary keys.1) =
        SigningView.countedPhase policy right keys.1 keys.2 (adversary keys.1) := by
    have signEq : left.sign keys.1 keys.2 = right.sign keys.1 keys.2 :=
      funext (hsign keys member)
    have handlerEq : SigningView.countedHandler policy left keys.1 keys.2 =
        SigningView.countedHandler policy right keys.1 keys.2 := by
      unfold SigningView.countedHandler SigningView.countedSigningOracle
      rw [signEq]
    simp only [SigningView.countedPhase, handlerEq]
  unfold SigningView.countedExperiment
  congr 1
  simp only [AddWriterT.runAdd_bind, AddWriterT.runAdd_pure]
  rw [← hkeygen]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro tagged member
  have hkeys : tagged.1 ∈ support left.keygen := by
    rw [← SigningView.costed_erases policy .keygen left.keygen, support_map]
    exact ⟨tagged, member, rfl⟩
  rw [phaseEq tagged.1 hkeys]
  simp only [hverify]

/-- The actual constructor refines the complete FIPS experiment without a caller key premise. -/
theorem countedExperiment_pureShakeView_fips205
    (adversary : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) :
    SigningView.countedExperiment sourcePolicy
      (pureShakeView FIPS205.params FIPS205.deterministicRand ($ᵗ FIPS205.core.PkSeed))
      (externalMain adversary) = canonicalExperiment FIPS205.scheme adversary := by
  unfold canonicalExperiment
  apply countedExperiment_congr_generated
  · exact (pureShakeView_keygen _ _ _).trans externalView_fips205_keygen.symm
  · intro pk request wire
    cases hf : External.encodePureMessage request.context request.message with
    | error error =>
      simp [pureShakeView, SLHDSA.SigningView.fromInternalPure,
        SignatureAlg.SigningView.rejectingEncoding,
        externalView, FIPS205.scheme, hf, Except.toOption]
    | ok message =>
      cases hd : decodeSignature FIPS205.params
          (Concrete.shakeWireCodec FIPS205.params.params) wire <;>
        simp [pureShakeView, SLHDSA.SigningView.fromInternalPure,
          SignatureAlg.SigningView.rejectingEncoding,
          externalView, FIPS205.scheme, hf, hd, Except.toOption]
  · intro keys member request
    have consistent : keys.1 = FIPS205.SecretKeyCore.publicKey keys.2 :=
      Bridge.internal_keygen_consistent keys member
    cases hf : External.encodePureMessage request.context request.message <;>
      simp [pureShakeView, SLHDSA.SigningView.fromInternalPure,
        SignatureAlg.SigningView.rejectingEncoding,
        externalView, FIPS205.scheme, hf, Except.toOption, consistent]; rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
