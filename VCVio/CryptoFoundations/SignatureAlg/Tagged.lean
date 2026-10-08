/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Transcript
public import VCVio.OracleComp.QueryTracking.QueryBound.Tagged
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# The tagged unforgeability experiment

A budget on an unforgeability adversary, `IsQueryBoundP (adv.main pk) p n`, counts the queries
of the adversary's own program. The experiment around it also queries the ambient oracles, to
generate keys, answer signing queries and verify the forgery, so the budget is not a bound on the
queries of the experiment. Tagging separates the two: the *tagged experiment* runs the scheme
with every query tagged `k₀` and the adversary with every ambient query tagged `k₁`, over
`spec.tagged K`.

* `simulateQ_untag_unforgeableExperiment_tagWith`: forgetting the tags of the tagged experiment
  gives the unforgeability experiment, so any statement about a run of the experiment under a
  handler `so` is a statement about a run of the tagged experiment under `so ∘ₛ untag`.
* `isQueryBoundP_unforgeableExperiment_tagWith`: the adversary's budget `n` for `p` is a budget
  `n` of the whole tagged experiment for any predicate `q` that no `k₀`-tagged query satisfies
  and whose `k₁`-tagged queries are `p`-queries.

With `IsQueryBoundP.cnt_le_of_mem_support_run_extendState`, the two give a pathwise count of the
adversary's queries on every run of the experiment under any stateful handler.

The budget transport rests on `isQueryBoundP_runWithSigningOracle_simulateQ_addLift`: running a
program through an interpretation of its ambient oracles and a signing oracle whose algorithm
makes no `q`-query, a budget of the program becomes a `q`-budget of the run. For an adversary whose
ambient oracles are interpreted through `G` against a scheme whose key generation, signing and
verification make no `q`-query, the budget is a budget of the whole experiment
(`isQueryBoundP_unforgeableExperiment_mapOracles`) and of its transcript
(`isQueryBoundP_unforgeableTranscriptExperiment_mapOracles`); the tagged experiment is the instance
in which `G` tags. When verification makes up to `V` `q`-queries, the budget of the experiment
is `n + V` (`isQueryBoundP_unforgeableExperiment_mapOracles_add` and
`isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add`). The interpreted adversary makes
only ambient queries of a predicate that every interpretation `G t` respects
(`allQueriesSatisfy_mapOracles`).
-/

public section

open OracleSpec OracleComp QueryImpl

namespace SignatureAlg

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {M PK SK S : Type}

/-! ## Query budgets through the signing oracle -/

/-- Run a `p`-bounded-by-`n` program through an interpretation `G` of its ambient oracles and the
signing oracle of `sigAlg`. If `G` spends at most one `q`-query on each `p`-query and none on any
other query, and signing makes no `q`-query, the run is `q`-bounded by `n`. -/
theorem isQueryBoundP_runWithSigningOracle_simulateQ_addLift
    (sigAlg : SignatureAlg (OracleComp spec') M PK SK S) (pk : PK) (sk : SK)
    (G : QueryImpl spec (OracleComp spec')) {p : ι ⊕ M → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q] {α : Type} {oa : OracleComp (spec + (M →ₒ S)) α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hG_p : ∀ t, p (.inl t) → IsQueryBoundP (G t) q 1)
    (hG_np : ∀ t, ¬ p (.inl t) → IsQueryBoundP (G t) q 0)
    (hsign : ∀ msg, IsQueryBoundP (sigAlg.sign pk sk msg) q 0) :
    IsQueryBoundP (sigAlg.runWithSigningOracle pk sk
      (simulateQ (G.addLift (QueryImpl.id' (M →ₒ S))) oa)) q n := by
  rw [runWithSigningOracle, ← QueryImpl.simulateQ_compose]
  have hinl : ∀ t, (((spec'.passthrough + sigAlg.signingOracle pk sk) ∘ₛ
      G.addLift (QueryImpl.id' (M →ₒ S))) (.inl t)).run = (·, ∅) <$> G t := fun t => by
    simp [QueryImpl.simulateQ_add_liftM_left, writerT_run_simulateQ_liftTarget]
  have hinr : ∀ msg, IsQueryBoundP (((spec'.passthrough + sigAlg.signingOracle pk sk) ∘ₛ
      G.addLift (QueryImpl.id' (M →ₒ S))) (.inr msg)).run q 0 := fun msg => by
    simpa [QueryImpl.simulateQ_add_liftM_right, signingOracle] using hsign msg
  refine IsQueryBoundP.simulateQ_run_writerT_of_step h ?_ ?_
  · rintro (t | msg) hp
    · rw [hinl, isQueryBoundP_map_iff]
      exact hG_p t hp
    · exact (hinr msg).mono zero_le_one
  · rintro (t | msg) hp
    · rw [hinl, isQueryBoundP_map_iff]
      exact hG_np t hp
    · exact hinr msg

/-! ## Query budgets of the experiment -/

section MapOracles

variable {SK' : Type} {sigAlg' : SignatureAlg (OracleComp spec') M PK SK' S}
  (G : QueryImpl spec (OracleComp spec')) {p : ι ⊕ M → Prop} [DecidablePred p]
  {q : ι' → Prop} [DecidablePred q] {n : ℕ}

/-- Let `G` spend at most one `q`-query on each ambient `p`-query and none on any other ambient
query, let key generation and signing of `sigAlg'` make no `q`-query, and let verification make at
most `V`. Then the experiment of `sigAlg'` against an adversary with `p`-budget `n` whose ambient
oracles are interpreted through `G` makes at most `n + V` `q`-queries. -/
theorem isQueryBoundP_unforgeableExperiment_mapOracles_add
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} {adv : UnforgeableAdversary sigAlg}
    {V : ℕ} (hadv : ∀ pk, IsQueryBoundP (adv.main pk) p n)
    (hG_p : ∀ t, p (.inl t) → IsQueryBoundP (G t) q 1)
    (hG_np : ∀ t, ¬ p (.inl t) → IsQueryBoundP (G t) q 0)
    (hkeygen : IsQueryBoundP sigAlg'.keygen q 0)
    (hsign : ∀ pk sk msg, IsQueryBoundP (sigAlg'.sign pk sk msg) q 0)
    (hverify : ∀ pk msg sig, IsQueryBoundP (sigAlg'.verify pk msg sig) q V) :
    IsQueryBoundP (unforgeableExperiment (adv.mapOracles G (sigAlg' := sigAlg'))) q (n + V) := by
  rw [unforgeableExperiment, show n + V = 0 + (n + (V + 0)) by omega]
  refine isQueryBoundP_bind hkeygen fun ⟨pk, sk⟩ _ => ?_
  refine isQueryBoundP_bind ?_ fun ⟨⟨msg, sig⟩, _⟩ _ =>
    isQueryBoundP_bind (hverify pk msg sig) fun _ _ => isQueryBoundP_pure _ _ _
  rw [UnforgeableAdversary.mapOracles_main]
  exact isQueryBoundP_runWithSigningOracle_simulateQ_addLift _ pk sk _ (hadv pk) hG_p hG_np
    (hsign pk sk)

/-- Let `G` spend at most one `q`-query on each ambient `p`-query and none on any other ambient
query, and let key generation, signing and verification of `sigAlg'` make no `q`-query. Then
the experiment of `sigAlg'` against an adversary with `p`-budget `n` whose ambient oracles are
interpreted through `G` makes at most `n` `q`-queries. -/
theorem isQueryBoundP_unforgeableExperiment_mapOracles
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} {adv : UnforgeableAdversary sigAlg}
    (hadv : ∀ pk, IsQueryBoundP (adv.main pk) p n)
    (hG_p : ∀ t, p (.inl t) → IsQueryBoundP (G t) q 1)
    (hG_np : ∀ t, ¬ p (.inl t) → IsQueryBoundP (G t) q 0)
    (hkeygen : IsQueryBoundP sigAlg'.keygen q 0)
    (hsign : ∀ pk sk msg, IsQueryBoundP (sigAlg'.sign pk sk msg) q 0)
    (hverify : ∀ pk msg sig, IsQueryBoundP (sigAlg'.verify pk msg sig) q 0) :
    IsQueryBoundP (unforgeableExperiment (adv.mapOracles G (sigAlg' := sigAlg'))) q n :=
  isQueryBoundP_unforgeableExperiment_mapOracles_add G hadv hG_p hG_np hkeygen hsign hverify

/-- The bound of `isQueryBoundP_unforgeableExperiment_mapOracles_add` for the transcript
experiment. -/
theorem isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} {adv : UnforgeableAdversary sigAlg}
    {V : ℕ} (hadv : ∀ pk, IsQueryBoundP (adv.main pk) p n)
    (hG_p : ∀ t, p (.inl t) → IsQueryBoundP (G t) q 1)
    (hG_np : ∀ t, ¬ p (.inl t) → IsQueryBoundP (G t) q 0)
    (hkeygen : IsQueryBoundP sigAlg'.keygen q 0)
    (hsign : ∀ pk sk msg, IsQueryBoundP (sigAlg'.sign pk sk msg) q 0)
    (hverify : ∀ pk msg sig, IsQueryBoundP (sigAlg'.verify pk msg sig) q V) :
    IsQueryBoundP (unforgeableTranscriptExperiment (adv.mapOracles G (sigAlg' := sigAlg'))) q
      (n + V) :=
  (isQueryBoundP_iff_of_map_eq (map_wins_unforgeableTranscriptExperiment _)).2 <|
    isQueryBoundP_unforgeableExperiment_mapOracles_add G hadv hG_p hG_np hkeygen hsign hverify

/-- The bound of `isQueryBoundP_unforgeableExperiment_mapOracles` for the transcript
experiment. -/
theorem isQueryBoundP_unforgeableTranscriptExperiment_mapOracles
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} {adv : UnforgeableAdversary sigAlg}
    (hadv : ∀ pk, IsQueryBoundP (adv.main pk) p n)
    (hG_p : ∀ t, p (.inl t) → IsQueryBoundP (G t) q 1)
    (hG_np : ∀ t, ¬ p (.inl t) → IsQueryBoundP (G t) q 0)
    (hkeygen : IsQueryBoundP sigAlg'.keygen q 0)
    (hsign : ∀ pk sk msg, IsQueryBoundP (sigAlg'.sign pk sk msg) q 0)
    (hverify : ∀ pk msg sig, IsQueryBoundP (sigAlg'.verify pk msg sig) q 0) :
    IsQueryBoundP (unforgeableTranscriptExperiment (adv.mapOracles G (sigAlg' := sigAlg'))) q n :=
  isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add G hadv hG_p hG_np hkeygen hsign
    hverify

/-- An adversary whose ambient oracles are interpreted through `G` makes only `allowed` ambient
queries when every interpretation `G t` does: its signing queries are passed on unchanged. -/
theorem allQueriesSatisfy_mapOracles {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) {allowed : ι' → Prop}
    (hG : ∀ t, AllQueriesSatisfy (G t) allowed) (pk : PK) :
    AllQueriesSatisfy ((adv.mapOracles G (sigAlg' := sigAlg')).main pk)
      (Sum.elim allowed fun _ ↦ True) := by
  classical
  rw [UnforgeableAdversary.mapOracles_main, ← isQueryBoundP_zero_iff]
  have h₀ := (isQueryBoundP_zero_iff (adv.main pk) (fun _ ↦ True)).2
    (allQueriesSatisfy_of_forall (fun _ ↦ trivial) _)
  simp only [not_true_eq_false] at h₀
  refine IsQueryBoundP.simulateQ_of_step h₀ (fun _ h ↦ h.elim) ?_
  rintro (t | m) -
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
    exact IsQueryBoundP.liftComp_subSpec (fun _ ↦ Iff.rfl)
      ((isQueryBoundP_zero_iff (G t) allowed).2 (hG t))
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
    exact IsQueryBoundP.liftComp_subSpec (q := fun t ↦ ¬Sum.elim allowed (fun _ ↦ True) t)
      (p := fun _ ↦ False) (fun _ ↦ iff_of_false not_false (not_not_intro trivial)) (by simp)

end MapOracles

/-! ## The tagged experiment -/

variable {K : Type} {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}

/-- Forgetting the tags of the experiment of the scheme tagged `k₀` against the adversary tagged
`k₁` gives the unforgeability experiment. -/
theorem simulateQ_untag_unforgeableExperiment_tagWith (k₀ k₁ : K)
    (adv : UnforgeableAdversary sigAlg) :
    simulateQ untag (unforgeableExperiment (sigAlg := sigAlg.map (simulateQ' (tagWith k₀)))
      (adv.mapOracles (tagWith k₁))) = unforgeableExperiment adv := by
  rw [simulateQ_unforgeableExperiment, UnforgeableAdversary.mapOracles_mapOracles,
    map_simulateQ'_map_simulateQ', untag_comp_tagWith, untag_comp_tagWith, map_simulateQ'_id',
    UnforgeableAdversary.mapOracles_id']

/-- A budget `n` of the adversary for `p` is a budget `n` of the tagged experiment for every
predicate `q` that no `k₀`-tagged query satisfies and whose `k₁`-tagged queries are ambient
`p`-queries. -/
theorem isQueryBoundP_unforgeableExperiment_tagWith {k₀ k₁ : K} {p : ι ⊕ M → Prop}
    [DecidablePred p] {q : K × ι → Prop} [DecidablePred q] (hq₀ : ∀ t, ¬ q (k₀, t))
    (hq₁ : ∀ t, q (k₁, t) → p (.inl t)) {adv : UnforgeableAdversary sigAlg} {n : ℕ}
    (hadv : ∀ pk, IsQueryBoundP (adv.main pk) p n) :
    IsQueryBoundP (unforgeableExperiment (sigAlg := sigAlg.map (simulateQ' (tagWith k₀)))
      (adv.mapOracles (tagWith k₁))) q n :=
  isQueryBoundP_unforgeableExperiment_mapOracles _ hadv (fun _ _ => by simp)
    (fun t hp => by simpa using fun h => hp (hq₁ t h)) (isQueryBoundP_simulateQ_tagWith_zero hq₀ _)
    (fun _ _ _ => isQueryBoundP_simulateQ_tagWith_zero hq₀ _)
    fun _ _ _ => isQueryBoundP_simulateQ_tagWith_zero hq₀ _

end SignatureAlg
