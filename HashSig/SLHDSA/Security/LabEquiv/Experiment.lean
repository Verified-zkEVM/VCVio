/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabEquiv.Tree
public import VCVio.CryptoFoundations.SignatureAlg.TranscriptCongr

/-!
# The lab experiment in the eager game

The transcript experiment of the secret-free scheme `deriveScheme` against `deriveAdversary`,
lifted to `labSpec core`, and the lab experiment `labExperiment` have the same output-and-state
measure in the eager game of the canonical graph, from every state
(`evalDist_eagerImpl_liftComp_eq_labExperiment`).

The lifted experiment is the experiment of the lifted scheme against the program of
`labAdversary` (`liftComp_unforgeableTranscriptExperiment_deriveAdversary`), whose key generation
and signing are the honest programs with every secret read by `labSecret`
(`map_labLiftHom_deriveScheme_keygen`, `map_labLiftHom_deriveScheme_sign`) and whose verification
is that of `labScheme`. The stages are related by `LabTriple`:

* **The hypertree** (`signFromPositionWithSecret_labTriple`), by induction on the remaining
  layers: each layer signs (`xmssSignWithSecret_labTriple`), which leaves the signature held by
  the state, and recovers its root from the signature (`xmssPkFromSigWith_labTriple`); the root is
  the next layer's message, on which no precondition is needed, since a WOTS+ signature uses its
  message only to choose its step counts.
* **Key generation** (`keygenInternalWithSecretM_labTriple`) is the root of the top tree.
* **Signing** (`signInternalWithSecretRandomizerM_labTriple`) makes the same `H_msg` query on both
  sides, signs with FORS, recovers the FORS public key and signs it with the hypertree.

The experiments then agree by the experiment congruence
`SignatureAlg.evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr_of_inv`, with the
invariant that the secret key carries the scheme's public seed: lab signing signs at the
public seed of `labScheme`, the lifted scheme at the public seed of the secret key, and lifted key
generation sets it to the scheme's.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) [SampleableType core.Y]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf] [SampleableType (Bytes vp.params.m)]
  (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)

include hd in
/-- **The hypertree.** Honest hypertree signing from a reachable position, with every secret read
by `labSecret`, is related to lab hypertree signing. -/
theorem signFromPositionWithSecret_labTriple (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      LabTriple core pkSeed (fun _ ↦ True)
        (GeneralHypertree.signFromPositionWithSecret core (PublicHash.f core pkSeed)
          (PublicHash.tl core pkSeed) (PublicHash.h core pkSeed) (labSecret core) recoverFinal
          pos layers h msg)
        (labSignFromPosition core recoverFinal pos layers h msg) fun _ _ ↦ True
  | 0, _, _ => QueryImpl.EqDistTriple.pure _ fun _ _ ↦ trivial
  | 1, _, msg => by
    rw [GeneralHypertree.signFromPositionWithSecret, labSignFromPosition]
    refine (xmssSignWithSecret_labTriple core hd pkSeed pos msg).bind fun sig ↦ ?_
    cases recoverFinal
    · exact QueryImpl.EqDistTriple.pure _ fun _ _ ↦ trivial
    · exact (xmssPkFromSigWith_labTriple core hd pkSeed pos sig msg).bind fun _ ↦
        QueryImpl.EqDistTriple.pure _ fun _ _ ↦ trivial
  | layers + 2, _, msg => by
    rw [GeneralHypertree.signFromPositionWithSecret, labSignFromPosition]
    exact (xmssSignWithSecret_labTriple core hd pkSeed pos msg).bind fun sig ↦
      (xmssPkFromSigWith_labTriple core hd pkSeed pos sig msg).bind fun root ↦
        ((signFromPositionWithSecret_labTriple false _ (layers + 1) _ root).mono
          (fun _ _ ↦ trivial) fun _ _ h ↦ h).bind fun _ ↦
          QueryImpl.EqDistTriple.pure _ fun _ _ ↦ trivial

include hd in
/-- **Key generation.** Honest key generation, with every secret read by `labSecret`, is related
to lab key generation. -/
theorem keygenInternalWithSecretM_labTriple :
    LabTriple core pkSeed (fun _ ↦ True)
      (GeneralScheme.keygenInternalWithSecretM core (labSecret core) pkSeed) (labKeygen core)
      fun _ _ ↦ True :=
  (xmssNodeWithSecret_labTriple core hd pkSeed
    ⟨⟨vp.params.d - 1, Nat.sub_one_lt vp.valid.d_pos.ne'⟩, ⟨0, by positivity⟩⟩).mono
    (fun _ h ↦ h) fun _ _ _ ↦ trivial

include hd in
/-- **Signing.** Honest signing at public seed `pkSeed` and randomizer `R`, with every secret read
by `labSecret`, is related to lab signing. -/
theorem signInternalWithSecretRandomizerM_labTriple (msg : List Byte) (pkRoot R : core.Y) :
    LabTriple core pkSeed (fun _ ↦ True)
      (GeneralScheme.signInternalWithSecretRandomizerM core (labSecret core) msg pkSeed pkRoot R)
      (labSignInternal core pkSeed msg pkRoot R) fun _ _ ↦ True := by
  rw [GeneralScheme.signInternalWithSecretRandomizerM, labSignInternal]
  refine (labTriple_refl core pkSeed _ _).bind fun digest ↦ ?_
  dsimp only
  rw [← BottomPosition.forsAdrs_ofDigestParts vp (splitDigest vp.params digest)]
  exact (forsSignWithSecret_labTriple core hd pkSeed _ _).bind fun forsSig ↦
    (forsPkFromSigWith_labTriple core hd pkSeed _ forsSig _).bind fun forsPk ↦
      ((signFromPositionWithSecret_labTriple core hd pkSeed _ _ _ _ forsPk).mono
        (fun _ _ ↦ trivial) fun _ _ h ↦ h).bind fun _ ↦
        QueryImpl.EqDistTriple.pure _ fun _ _ ↦ trivial

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

include hd in
/-- **The lab experiment in the eager game.** In the eager game of the canonical graph at
`pkSeed`, from every state, the transcript experiment of the secret-free scheme against
`deriveAdversary`, lifted to `labSpec core`, and the lab experiment have the same
output-and-state measure. -/
theorem evalDist_eagerImpl_liftComp_eq_labExperiment {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (st : LabState core)
    [MeasurableSpace (DeriveOutcome core × LabState core)] :
    𝒟[(simulateQ (slhGraph core pkSeed).eagerImpl
        (liftComp (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))
          (labSpec core))).run st] =
      𝒟[(simulateQ (slhGraph core pkSeed).eagerImpl (labExperiment core adv pkSeed)).run st] := by
  have hkeygen : LabTriple core pkSeed (fun _ ↦ True)
      ((deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom).keygen
      (labScheme core optRand pkSeed).keygen fun kp _ ↦ kp.2.pkSeed = pkSeed := by
    rw [map_labLiftHom_deriveScheme_keygen]
    exact (keygenInternalWithSecretM_labTriple core hd pkSeed).bind fun _ ↦
      QueryImpl.EqDistTriple.pure _ fun _ _ ↦ rfl
  have hsign : ∀ pk (sk : PublicKeyCore core) msg, sk.pkSeed = pkSeed →
      LabTriple core pkSeed (fun _ ↦ True)
        (((deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom).sign pk sk msg)
        ((labScheme core optRand pkSeed).sign pk sk msg) fun _ _ ↦ True := by
    rintro pk ⟨_, pkRoot⟩ msg rfl
    rw [map_labLiftHom_deriveScheme_sign]
    exact (labTriple_refl core _ _ _).bind fun R ↦
      signInternalWithSecretRandomizerM_labTriple core hd _ msg pkRoot R
  rw [liftComp_unforgeableTranscriptExperiment_deriveAdversary]
  exact evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr_of_inv _
    (allowed := fun _ ↦ True) (fun _ (sk : PublicKeyCore core) _ ↦ sk.pkSeed = pkSeed)
    (hkeygen.evalDist_run_eq trivial)
    (fun z hz ↦ ((OracleComp.EqDistTriple.symm hkeygen) st trivial).2 z hz |>.2)
    (fun _ _ _ _ _ h _ _ ↦ h)
    (fun pk sk msg s h ↦ (hsign pk sk msg h).evalDist_run_eq trivial)
    (fun _ _ _ _ h _ _ ↦ h)
    (fun pk _ msg sig _ _ ↦ by
      rw [map_labLiftHom_deriveScheme_verify]
      intros
      rfl)
    _ fun _ ↦ allQueriesSatisfy_of_forall (by rintro (_ | _) <;> trivial) _

end SLHDSA.Security
