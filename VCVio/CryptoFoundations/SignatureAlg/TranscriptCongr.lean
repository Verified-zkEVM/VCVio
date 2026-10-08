/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Transcript
import all VCVio.CryptoFoundations.SignatureAlg.Transcript

/-!
# Congruence of the transcript experiment

Two signature schemes `A` and `B` over the same oracles, run under one stateful interpretation
`so` of those oracles, have the same transcript-experiment measure when their key generations,
signings and verifications have the same measures. The stages need to agree only on the states
the experiment of `A` reaches: an invariant `I pk sk s` of the key pair and the state, established
by the key generation of `A` and preserved by its signing and by every ambient step the
adversary may take, restricts where signing and verification must agree
(`SignatureAlg.evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr_of_inv`). Through
`I`, the stages may be compared under a relation between the key pair and the state, such as a
component of the key being a value the state holds. Stages agreeing from every state give equal
experiments from every state
(`SignatureAlg.evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr`).

The signing stage is compared under an arbitrary continuation
(`SignatureAlg.evalDist_simulateQ_run_runWithSigningOracle_bind_congr_of_inv`): the ambient
steps of the adversary are the same in both runs, and each signing query is answered by runs of
the two signing algorithms with equal measures.
-/

public section

open OracleSpec OracleComp MeasureTheory

namespace SignatureAlg

variable {ι : Type} {spec : OracleSpec ι} {M PK SK S σ : Type}

/-- Computations with equal measures under every measurable structure on their outputs have
equal measures after a common continuation. -/
private theorem evalDist_bind_congr_left_of_forall {α γ : Type} [MeasurableSpace γ]
    {mx my : ProbComp α} (h : ∀ [MeasurableSpace α], 𝒟[mx] = 𝒟[my]) (f : α → ProbComp γ) :
    𝒟[mx >>= f] = 𝒟[my >>= f] := by
  let : MeasurableSpace α := ⊤
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, h]

/-- Signing stages agree under every continuation. Let `I` be a predicate on the state of a
stateful interpretation `so` of the ambient oracles, preserved by every step at an `allowed`
ambient query and by every run of the signing algorithm of `A`, and let the signing algorithms of
`A` and `B` have equal measures from every state satisfying `I`. A program whose ambient queries
are all `allowed`, run with the signing oracle of `A` or of `B` from a state satisfying `I`, has
the same measure followed by any continuation. -/
theorem evalDist_simulateQ_run_runWithSigningOracle_bind_congr_of_inv
    (so : QueryImpl spec (StateT σ ProbComp)) {A B : SignatureAlg (OracleComp spec) M PK SK S}
    (pk : PK) (sk : SK) {allowed : ι → Prop} (I : σ → Prop)
    (hamb : ∀ t, allowed t → ∀ s, I s → ∀ z ∈ support ((so t).run s), I z.2)
    (hsign : ∀ msg s, I s → ∀ [MeasurableSpace (S × σ)],
      𝒟[(simulateQ so (A.sign pk sk msg)).run s] = 𝒟[(simulateQ so (B.sign pk sk msg)).run s])
    (hsignI : ∀ msg s, I s → ∀ z ∈ support ((simulateQ so (A.sign pk sk msg)).run s), I z.2)
    {α : Type} (oa : OracleComp (spec + (M →ₒ S)) α)
    (hoa : AllQueriesSatisfy oa (Sum.elim allowed fun _ ↦ True)) {s : σ} (hs : I s)
    {γ : Type} [MeasurableSpace γ] (f : (α × QueryLog (M →ₒ S)) × σ → ProbComp γ) :
    𝒟[(simulateQ so (A.runWithSigningOracle pk sk oa)).run s >>= f] =
      𝒟[(simulateQ so (B.runWithSigningOracle pk sk oa)).run s >>= f] := by
  induction oa using OracleComp.inductionOn generalizing s f with
  | pure x => simp only [runWithSigningOracle, simulateQ_pure, WriterT.run_pure]
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    simp only [runWithSigningOracle, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind',
      simulateQ_map, StateT.run_bind, StateT.run_map, bind_assoc, bind_map_left]
    cases t with
    | inl t =>
      simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
      refine evalDist_bind_congr_of_support _ _ _ fun z hz ↦ ih z.1.1 (hoa.2 z.1.1) ?_ _
      simp only [WriterT.run_monadLift', simulateQ_map, StateT.run_map, support_map,
        Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [QueryImpl.id'_apply, simulateQ_spec_query] at hw
      exact hamb t hoa.1 s hs w hw
    | inr msg =>
      simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inr, signingOracle,
        QueryImpl.run_withLogging_apply, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, bind_assoc, pure_bind]
      exact (evalDist_bind_congr_of_support _ _ _ fun z hz ↦
        ih z.1 (hoa.2 z.1) (hsignI msg s hs z hz) _).trans
        (evalDist_bind_congr_left_of_forall (hsign msg s hs) _)

/-- **Experiment congruence.** Let `I pk sk s` be a predicate on a key pair and the state of a
stateful interpretation `so` of the ambient oracles. Suppose the key generations of `A` and `B`
have equal measures from `s₀` and every key pair and state that of `A` reaches satisfy `I`, every
step at an `allowed` ambient query and every run of the signing algorithm of `A` preserve `I`,
and the signing and verification algorithms of `A` and `B` have equal measures from every state
satisfying `I`. Against an adversary whose ambient queries are all `allowed`, the transcript
experiments of `A` and `B` have equal measures from `s₀`. -/
theorem evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr_of_inv
    (so : QueryImpl spec (StateT σ ProbComp)) {A B : SignatureAlg (OracleComp spec) M PK SK S}
    {allowed : ι → Prop} (I : PK → SK → σ → Prop) {s₀ : σ}
    (hkeygen : ∀ [MeasurableSpace ((PK × SK) × σ)],
      𝒟[(simulateQ so A.keygen).run s₀] = 𝒟[(simulateQ so B.keygen).run s₀])
    (hkeygenI : ∀ z ∈ support ((simulateQ so A.keygen).run s₀), I z.1.1 z.1.2 z.2)
    (hamb : ∀ t, allowed t → ∀ pk sk s, I pk sk s → ∀ z ∈ support ((so t).run s), I pk sk z.2)
    (hsign : ∀ pk sk msg s, I pk sk s → ∀ [MeasurableSpace (S × σ)],
      𝒟[(simulateQ so (A.sign pk sk msg)).run s] = 𝒟[(simulateQ so (B.sign pk sk msg)).run s])
    (hsignI : ∀ pk sk msg s, I pk sk s →
      ∀ z ∈ support ((simulateQ so (A.sign pk sk msg)).run s), I pk sk z.2)
    (hverify : ∀ pk sk msg sig s, I pk sk s → ∀ [MeasurableSpace (Bool × σ)],
      𝒟[(simulateQ so (A.verify pk msg sig)).run s] =
        𝒟[(simulateQ so (B.verify pk msg sig)).run s])
    (adv : UnforgeableAdversary A)
    (hadv : ∀ pk, AllQueriesSatisfy (adv.main pk) (Sum.elim allowed fun _ ↦ True))
    [MeasurableSpace (UnforgeableTranscript M PK SK S × σ)] :
    𝒟[(simulateQ so (unforgeableTranscriptExperiment adv)).run s₀] =
      𝒟[(simulateQ so (unforgeableTranscriptExperiment (sigAlg := B) ⟨adv.main⟩)).run s₀] := by
  simp only [unforgeableTranscriptExperiment, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure]
  refine (evalDist_bind_congr_of_support _ _ _ fun z hz ↦ ?_).trans
    (evalDist_bind_congr_left_of_forall hkeygen _)
  have hI := hkeygenI z hz
  refine (evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_).trans
    (evalDist_simulateQ_run_runWithSigningOracle_bind_congr_of_inv so z.1.1 z.1.2 (I z.1.1 z.1.2)
      (fun t ht ↦ hamb t ht z.1.1 z.1.2) (hsign z.1.1 z.1.2) (hsignI z.1.1 z.1.2) _
      (hadv z.1.1) hI _)
  have hw' := holds_of_mem_support_run_runWithSigningOracle so A z.1.1 z.1.2 (fun _ ↦ I z.1.1 z.1.2)
    (fun t ht _ ↦ hamb t ht z.1.1 z.1.2) (fun msg _ ↦ hsignI z.1.1 z.1.2 msg) (hadv z.1.1) hI hw
  exact evalDist_bind_congr_left_of_forall (hverify z.1.1 z.1.2 _ _ w.2 hw') _

/-- **Experiment congruence from every state.** If the key generations, signing algorithms and
verification algorithms of `A` and `B` have equal measures from every state of a stateful
interpretation `so` of the ambient oracles, the transcript experiments of `A` and `B` have equal
measures from every state. -/
theorem evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr
    (so : QueryImpl spec (StateT σ ProbComp)) {A B : SignatureAlg (OracleComp spec) M PK SK S}
    (hkeygen : ∀ s, ∀ [MeasurableSpace ((PK × SK) × σ)],
      𝒟[(simulateQ so A.keygen).run s] = 𝒟[(simulateQ so B.keygen).run s])
    (hsign : ∀ pk sk msg s, ∀ [MeasurableSpace (S × σ)],
      𝒟[(simulateQ so (A.sign pk sk msg)).run s] = 𝒟[(simulateQ so (B.sign pk sk msg)).run s])
    (hverify : ∀ pk msg sig s, ∀ [MeasurableSpace (Bool × σ)],
      𝒟[(simulateQ so (A.verify pk msg sig)).run s] =
        𝒟[(simulateQ so (B.verify pk msg sig)).run s])
    (adv : UnforgeableAdversary A) [MeasurableSpace (UnforgeableTranscript M PK SK S × σ)]
    (s₀ : σ) :
    𝒟[(simulateQ so (unforgeableTranscriptExperiment adv)).run s₀] =
      𝒟[(simulateQ so (unforgeableTranscriptExperiment (sigAlg := B) ⟨adv.main⟩)).run s₀] :=
  evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr_of_inv so (allowed := fun _ ↦ True)
    (fun _ _ _ ↦ True) (hkeygen s₀) (fun _ _ ↦ trivial) (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun pk sk msg s _ ↦ hsign pk sk msg s) (fun _ _ _ _ _ _ _ ↦ trivial)
    (fun pk _ msg sig s _ ↦ hverify pk msg sig s) adv
    (fun _ ↦ allQueriesSatisfy_of_forall (by rintro (_ | _) <;> trivial) _)

end SignatureAlg
