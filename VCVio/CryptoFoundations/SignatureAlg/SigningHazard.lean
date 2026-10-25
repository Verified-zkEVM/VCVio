/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Transcript
public import VCVio.EvalDist.ProbabilityBounds

/-!
# A hazard raised only by signing

Let a stateful interpretation of the ambient oracles carry a *hazard*, a predicate on its state,
that no step at an allowed ambient query raises, and that each run of the signing algorithm raises
with probability at most `ε`. Then a program making at most `q` signing queries, run with the
logged signing oracle from a state outside the hazard, ends in the hazard with probability at most
`q * ε` (`QueryImpl.prEvent_run_add_withLogging_le`). When key generation and verification never
raise it either, the same bound holds at the end of the unforgeability experiment
(`SignatureAlg.prEvent_run_unforgeableTranscriptExperiment_le`).

A typical hazard is a value drawn inside signing, such as a hedged signer's fresh randomness,
hitting a fixed point: the draw itself is not an oracle query of the experiment, so a query
budget alone does not bound it, but the hazard reaches the interpreting state through the queries
that consume it.

The statements are the probabilistic counterparts of
`QueryImpl.holds_of_mem_support_run_add_withLogging` and
`SignatureAlg.holds_of_mem_support_run_unforgeableTranscriptExperiment`.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace QueryImpl

variable {ι κ : Type} {spec : OracleSpec.{0, 0} ι} {sigSpec : OracleSpec.{0, 0} κ} {σ : Type}

/-- **A hazard raised only by the logged handler.** Let `bad` be a predicate on an outer state
that no outer step at an `allowed` ambient query raises, and that every outer run of the logged
inner handler's program raises with probability at most `ε`. A program whose ambient queries are
all `allowed` and which makes at most `q` queries of a predicate `p` holding at every logged
query, run through the logged handler under the outer simulation from a state outside `bad`, ends
in `bad` with probability at most `q * ε`. -/
theorem prEvent_run_add_withLogging_le (outer : QueryImpl spec (StateT σ ProbComp))
    (sign : QueryImpl sigSpec (OracleComp spec)) {allowed : ι → Prop} (bad : σ → Prop)
    {ε : ℝ≥0∞} (hamb : ∀ t, allowed t → ∀ s, ¬bad s → ∀ z ∈ support ((outer t).run s), ¬bad z.2)
    (hsign : ∀ t s, ¬bad s → Pr{let z ← (simulateQ outer (sign t)).run s}[bad z.2] ≤ ε)
    {p : (spec + sigSpec).Domain → Prop} [DecidablePred p] (hp : ∀ t, p (.inr t))
    {α : Type} {oa : OracleComp (spec + sigSpec) α}
    (hoa : AllQueriesSatisfy oa (Sum.elim allowed fun _ ↦ True)) {q : ℕ}
    (hq : IsQueryBoundP oa p q) {s₀ : σ} (h₀ : ¬bad s₀) :
    Pr{let z ← (simulateQ outer ((simulateQ
      ((HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog sigSpec) (OracleComp spec)) + sign.withLogging) oa).run)).run s₀}[
      bad z.2] ≤ q * ε := by
  induction oa using OracleComp.inductionOn generalizing q s₀ with
  | pure x =>
    simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure]
    exact (prEvent_eq_zero_of_forall_mem_support _ _ (by simpa using h₀)).trans_le zero_le
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', simulateQ_bind, StateT.run_bind]
    cases t with
    | inl t =>
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun w hw ↦ ?_
      have hs : ¬bad w.2 := by
        simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          HasQuery.toQueryImpl_apply, HasQuery.instOfMonadLift_query, WriterT.run_monadLift',
          simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hw
        obtain ⟨⟨v, s₁⟩, hv, rfl⟩ := hw
        rw [simulateQ_spec_query] at hv
        exact hamb t hoa.1 s₀ h₀ _ hv
      obtain ⟨⟨a, w₁⟩, s'⟩ := w
      simp only [simulateQ_map, StateT.run_map, prEvent_map]
      exact (ih a (hoa.2 a) (hq.2 a) hs).trans (by gcongr; split_ifs <;> omega)
    | inr t =>
      have hq0 : 0 < q := hq.1.resolve_left (not_not_intro (hp t))
      rw [QueryImpl.add_apply_inr, QueryImpl.run_withLogging_apply, simulateQ_bind,
        StateT.run_bind, bind_assoc]
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun w ↦ bad w.2) _
        (ε := (q - 1 : ℕ) * ε) fun w _ hw ↦ ?_).trans ?_
      · simp only [simulateQ_pure, StateT.run_pure, pure_bind, simulateQ_map, StateT.run_map,
          prEvent_map]
        have h := hq.2 w.1
        simp only [hp t, ↓reduceIte] at h
        exact ih w.1 (hoa.2 _) h hw
      · calc _ ≤ ε + (q - 1 : ℕ) * ε := add_le_add (hsign t s₀ h₀) le_rfl
          _ = q * ε := by
            rw [← one_add_mul]
            norm_cast
            rw [Nat.add_sub_cancel' hq0]

end QueryImpl

namespace SignatureAlg

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {M PK SK S σ : Type}

/-- **A hazard raised only by signing, over the unforgeability experiment.** Let `bad` be a
predicate on the state of a stateful interpretation of the ambient oracles. Suppose that no run of
key generation from `s₀` ends in `bad`, that no step at an `allowed` ambient query and no run of
verification enters `bad`, and that every run of signing enters `bad` with probability at most
`ε`. Against an adversary whose ambient queries are all `allowed` and which makes at most `q`
queries of a predicate `p` holding at every signing query, the experiment run from `s₀` ends in
`bad` with probability at most `q * ε`. -/
theorem prEvent_run_unforgeableTranscriptExperiment_le (so : QueryImpl spec (StateT σ ProbComp))
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} {allowed : ι → Prop} (bad : σ → Prop)
    {ε : ℝ≥0∞} {s₀ : σ} (hkeygen : ∀ z ∈ support ((simulateQ so sigAlg.keygen).run s₀), ¬bad z.2)
    (hamb : ∀ t, allowed t → ∀ s, ¬bad s → ∀ z ∈ support ((so t).run s), ¬bad z.2)
    (hsign : ∀ pk sk msg s, ¬bad s →
      Pr{let z ← (simulateQ so (sigAlg.sign pk sk msg)).run s}[bad z.2] ≤ ε)
    (hverify : ∀ pk msg sig s, ¬bad s →
      ∀ z ∈ support ((simulateQ so (sigAlg.verify pk msg sig)).run s), ¬bad z.2)
    (adv : UnforgeableAdversary sigAlg)
    (hadv : ∀ pk, AllQueriesSatisfy (adv.main pk) (Sum.elim allowed fun _ ↦ True))
    {p : (spec + (M →ₒ S)).Domain → Prop} [DecidablePred p] (hp : ∀ msg, p (.inr msg)) {q : ℕ}
    (hq : ∀ pk, IsQueryBoundP (adv.main pk) p q) :
    Pr{let z ← (simulateQ so (unforgeableTranscriptExperiment adv)).run s₀}[bad z.2] ≤ q * ε := by
  rw [unforgeableTranscriptExperiment_def]
  simp only [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ⟨⟨pk, sk⟩, s₁⟩ h₁ ↦ ?_
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun w ↦ bad w.2) _ (ε := 0)
    fun ⟨⟨⟨msg, sig⟩, log⟩, s₂⟩ _ h₂ ↦ ?_).trans ?_
  · rw [add_zero]
    exact QueryImpl.prEvent_run_add_withLogging_le so (sigAlg.sign pk sk) bad hamb
      (fun msg s hs ↦ hsign pk sk msg s hs) hp (hadv pk) (hq pk) (hkeygen _ h₁)
  · refine (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_).le
    simp only [simulateQ_pure, mem_support_bind_iff, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨⟨v, s₃⟩, hv, rfl⟩ := hz
    exact hverify pk msg sig s₂ h₂ _ hv

end SignatureAlg
