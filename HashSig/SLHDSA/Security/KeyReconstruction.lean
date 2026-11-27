/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.SeedCoupling
public import HashSig.SLHDSA.SigningView.Encoding
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.CryptoFoundations.SignatureAlg.Routed
public import VCVio.OracleComp.QueryTracking.Enforcement

/-!
# Reconstructing the secret key after sampling a signing prefix

For arbitrary validated SLH-DSA parameters, an encoded signing experiment can sample its seeds
before the marked continuation. The equality preserves the signing replies, forgery and state
of a guarded oracle interpreter.
-/

public section

open OracleSpec OracleComp SignatureAlg

namespace SLHDSA.Security

/-- Secret derivations at sampled seeds reconstruct the complete marked and guarded signing view. -/
theorem romScheme_partial_key_reconstruction :
  ∀ {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    {ιraw Request : Type} (raw : OracleSpec.{0, 0} ιraw)
    (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (atomic : CoreWireCodec vp.params core)
    (frame : Request → Option (List Byte)),
    let H := hashSpec core
    let Native := unifSpec + (H + raw)
    let Reply := Option (List Byte)
    let Sign := Request →ₒ Reply
    let PK := PublicKeyCore core
    let seedPrefix : OracleComp Native (core.SkSeed × core.SkPrf) :=
      liftM ($ᵗ (core.SkSeed × core.SkPrf))
    let left := SigningView.rejectingEncoding
      ((romScheme core e optRand (pure pkSeed)).map
        (simulateQ' (liftTypedImpl (hs := H) (ext := raw))))
      frame (SLHDSA.encodeSignature vp atomic)
      (fun wire => (SLHDSA.decodeSignature vp atomic wire).toOption)
    let right : (core.SkSeed × core.SkPrf) →
        SigningView (OracleComp Native) Request PK PK (List Byte) Reply := fun secret =>
      SigningView.rejectingEncoding
        (((deriveScheme core optRand pkSeed).map
          (simulateQ' ((secretEncoding core e pkSeed).deriveImpl secret))).map
            (simulateQ' (liftTypedImpl (hs := H) (ext := raw))))
        frame (SLHDSA.encodeSignature vp atomic)
        (fun wire => (SLHDSA.decodeSignature vp atomic wire).toOption)
    let mapKeys := fun (secret : core.SkSeed × core.SkPrf) (keys : PK × PK) =>
      (keys.1, fillSecretKey core secret keys.2)
    (left.keygen = (do
      let secret ← seedPrefix
      mapKeys secret <$> (right secret).keygen)) ∧
    ∀ main : PK → OracleComp (Native + Sign) (Request × List Byte),
      let source := SigningView.Events.fullExperiment left main
      let reconstructed := (do
        let secret ← simulateQ (SigningView.Events.phaseImpl Native Request .keygen) seedPrefix
        (fun result => (mapKeys secret result.1, result.2)) <$>
          SigningView.Events.fullExperiment (right secret) main)
      source = reconstructed ∧
      ∀ {κ σ : Type} (common : OracleSpec.{0, 0} κ)
        (project : QueryImpl (SigningView.Events.Spec Native Request) (OracleComp common))
        (handler : QueryImpl common (StateT σ ProbComp))
        (caps : Nat × Nat) (cost : common.Domain → Nat × Nat)
        (fallback : (input : common.Domain) → common.Range input)
        (initial : σ × ((Nat × Nat) × Bool)),
        (simulateQ (QueryImpl.guardQueryBudget caps cost handler fallback)
          (simulateQ project source)).run initial =
        (simulateQ (QueryImpl.guardQueryBudget caps cost handler fallback)
          (simulateQ project reconstructed)).run initial := by
  intro vp core instY instEq instSeed instPrf ιraw Request raw e optRand pkSeed atomic frame
    H Native Reply Sign PK seedPrefix left right mapKeys
  let Typed := unifSpec + H
  let roots (secret : core.SkSeed × core.SkPrf) : OracleComp Typed core.Y :=
    GeneralScheme.keygenInternalWithSecretM core
      (oracleSecret core e pkSeed secret.1) pkSeed
  let publicPair (root : core.Y) : PK × PK := (⟨pkSeed, root⟩, ⟨pkSeed, root⟩)
  let hom (secret : core.SkSeed × core.SkPrf) :
      HasQuery.QueryHom (publicHashSpec core) (OracleComp (deriveSpec core))
        (OracleComp Typed) :=
    { toMonadHom := simulateQ' ((secretEncoding core e pkSeed).deriveImpl secret)
      map_query' := fun _ => rfl }
  have hkgCore (secret : core.SkSeed × core.SkPrf) :
      simulateQ ((secretEncoding core e pkSeed).deriveImpl secret)
        (deriveScheme core optRand pkSeed).keygen = publicPair <$> roots secret := by
    have hnat : simulateQ ((secretEncoding core e pkSeed).deriveImpl secret)
        (GeneralScheme.keygenInternalWithSecretM core (deriveSecret core) pkSeed) =
          roots secret :=
      GeneralScheme.keygenInternalWithSecretM_natural core (hom secret)
        (deriveSecret core) (oracleSecret core e pkSeed secret.1)
        (fun _ ha => simulateQ_deriveImpl_deriveSecret core e pkSeed secret ha) pkSeed
    simp only [deriveScheme, simulateQ_bind, simulateQ_pure, hnat, map_eq_bind_pure_comp]
    rfl
  have hromCore : (romScheme core e optRand (pure pkSeed)).keygen = (do
      let secret ← (liftM ($ᵗ (core.SkSeed × core.SkPrf)) : OracleComp Typed _)
      (fun root => ((⟨pkSeed, root⟩ : PK),
        fillSecretKey core secret (⟨pkSeed, root⟩ : PK))) <$> roots secret) := by
    rw [romScheme_keygen, uniformSample_prod]
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp, liftM_bind, liftM_pure,
      bind_assoc, pure_bind, Function.comp_def, fillSecretKey, roots]
  have liftSample {α : Type} (oa : ProbComp α) :
      simulateQ (liftTypedImpl (hs := H) (ext := raw))
        (liftM oa : OracleComp Typed α) = (liftM oa : OracleComp Native α) := by
    rw [QueryImpl.simulateQ_liftM_eq_of_query _ (fun t => liftM (unifSpec.query t))
      fun _ => rfl]
    rfl
  have hrightGen (secret : core.SkSeed × core.SkPrf) :
      (right secret).keygen = publicPair <$>
        simulateQ (liftTypedImpl (hs := H) (ext := raw)) (roots secret) := by
    dsimp only [right]
    simp only [SigningView.rejectingEncoding_keygen, map_keygen, hkgCore,
      simulateQ_map]
  have hkeygen : left.keygen = (do
      let secret ← seedPrefix
      mapKeys secret <$> (right secret).keygen) := by
    dsimp only [left]
    simp only [SigningView.rejectingEncoding_keygen, map_keygen, hromCore,
      simulateQ_bind, simulateQ_map, liftSample, hrightGen, Functor.map_map]
    rfl
  have hsignCore (secret : core.SkSeed × core.SkPrf) (root : core.Y)
      (message : List Byte) :
      (romScheme core e optRand (pure pkSeed)).sign (⟨pkSeed, root⟩ : PK)
        (fillSecretKey core secret (⟨pkSeed, root⟩ : PK)) message =
      simulateQ ((secretEncoding core e pkSeed).deriveImpl secret)
        ((deriveScheme core optRand pkSeed).sign (⟨pkSeed, root⟩ : PK)
          (⟨pkSeed, root⟩ : PK) message) := by
    have hnat : ∀ R, simulateQ ((secretEncoding core e pkSeed).deriveImpl secret)
        (GeneralScheme.signInternalWithSecretRandomizerM core (deriveSecret core)
          message pkSeed root R) =
        GeneralScheme.signInternalWithSecretRandomizerM core
          (oracleSecret core e pkSeed secret.1) message pkSeed root R := fun R =>
      GeneralScheme.signInternalWithSecretRandomizerM_natural core (hom secret)
        (deriveSecret core) (oracleSecret core e pkSeed secret.1)
        (fun _ ha => simulateQ_deriveImpl_deriveSecret core e pkSeed secret ha)
        message pkSeed root R
    rw [romScheme_sign]
    simp only [deriveScheme, fillSecretKey, simulateQ_bind, hnat,
      SecretEncoding.simulateQ_deriveImpl_liftM]
    rfl
  have hsign (secret : core.SkSeed × core.SkPrf) :
      ∀ keys ∈ support (right secret).keygen, ∀ request,
        left.sign keys.1 (fillSecretKey core secret keys.2) request =
          (right secret).sign keys.1 keys.2 request := by
    intro keys member request
    rw [hrightGen] at member
    obtain ⟨root, _rootMember, hkeys⟩ := mem_support_map_peel publicPair _ member
    subst keys
    dsimp only [publicPair, left, right]
    simp only [SigningView.rejectingEncoding_sign, map_sign]
    cases frame request with
    | none => rfl
    | some message => simp only [hsignCore]
  have hverify (secret : core.SkSeed × core.SkPrf) (pk : PK)
      (request : Request) (signature : List Byte) :
      left.verify pk request signature = (right secret).verify pk request signature := by
    dsimp only [left, right]
    simp only [SigningView.rejectingEncoding_verify, map_verify]
    cases frame request with
    | none => rfl
    | some message =>
      cases (SLHDSA.decodeSignature vp atomic signature).toOption with
      | none => rfl
      | some internalSig =>
        simp only [romScheme_verify, deriveScheme]
        exact congrArg (simulateQ (liftTypedImpl (hs := H) (ext := raw)))
          (GeneralScheme.verifyInternalM_natural vp core (hom secret)
            message internalSig pk).symm
  refine ⟨hkeygen, ?_⟩
  intro main source reconstructed
  have hfull : source = reconstructed := by
    have hk : left.keygen = (do
        let secret ← seedPrefix
        let keys ← (right secret).keygen
        pure (keys.1, fillSecretKey core secret keys.2)) := by
      simpa only [map_eq_bind_pure_comp, Function.comp_def, mapKeys] using hkeygen
    simpa only [source, reconstructed, mapKeys] using
      (SignatureAlg.SigningView.Events.fullExperiment_keyPrefix left right seedPrefix
        (fun secret _ sk => fillSecretKey core secret sk) hk hsign hverify main)
  refine ⟨hfull, ?_⟩
  intro κ σ common project handler caps cost fallback initial
  exact congrArg (fun program =>
    (simulateQ (QueryImpl.guardQueryBudget caps cost handler fallback)
      (simulateQ project program)).run initial) hfull

end SLHDSA.Security
