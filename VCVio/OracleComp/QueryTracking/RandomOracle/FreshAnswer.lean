/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.EvalDist.Monad.Measure

/-!
# The fresh-answer bound for a shared lazy random oracle

A bad event of a random-oracle run is typically a predicate on the answer table that, once it
holds, keeps holding, and that a *fresh* answer makes fire with mass at most `ε` whatever the
query and whatever the not-yet-firing table.  This module turns that per-answer bound into a
bound on the whole run: along a run of `unifFwdImpl spec + spec.randomOracle` started from the
empty cache, such a predicate holds of the final cache with mass at most `q * ε` on the paths
whose final cache has at most `q` entries (`evalDist_run_setOf_le_of_fresh_bound`).  The
accompanying charge bound (`enncard_le_add_cost_of_mem_support_runAdd_run_withAddCost`) says the
final cache holds at most as many entries as the initial cache plus the cost-instrumented run's
total charge, so at most the total charge from the empty cache, which is how a query budget
discharges the `enncard ≤ q` side condition.

The engine is `evalDist_apply_setOf_and_le_of_potential`: for an arbitrary
`QueryImpl spec (StateT σ ProbComp)`, an arbitrary state predicate `P` and an arbitrary potential
`Φ` that never decreases along a step, if every step out of a non-firing state is either
deterministic and still non-firing, or a sample whose firing mass is at most the increment of `Φ`
that the step pays, then the mass of the paths that fire with `Φ ≤ K` is at most `K - Φ s`.  The
cache-size potential `enncard · * ε` instantiates this, since a fresh answer pays exactly `ε`.

The private-sampling step shape hands its sampler back existentially
(`exists_run_unifFwdImpl_add_randomOracle_inl`) instead of naming it, because the
`liftM (OracleSpec.query i)` that realises the step does not unify across a lemma boundary.

## Scope

* No bad event is defined here and no union bound over several bad events is taken.  `P` is an
  arbitrary predicate; the only thing assumed of it is that it does not hold of the empty cache
  and that a fresh answer makes it fire with mass at most `ε`.
* `hfresh` demands one `ε` uniformly over every non-firing cache, so the theorem bounds
  *target-hitting* events: those whose set of firing fresh answers stays small however full the
  cache already is.  A bad event whose fresh-answer bad set grows with the cache — any collision
  event — admits no `ε < 1`, because an injective cache covering the range does not yet fire
  while every fresh answer makes it fire.  Such an event must carry the budget in the predicate
  itself, as `P c := … ∧ QueryCache.enncard c ≤ q`, which then satisfies `hfresh` with an `ε`
  proportional to `q` over the size of the range.
* The measurable-space arguments of the `𝒟[…] {z | …}` statements are pinned to `⊤` by a `letI`
  inside the statement rather than taken as instance arguments: the induction of the engine
  changes the result type, so no instance argument could be fixed across it.  Pinning `⊤` is
  lossless wherever `DiscreteMeasurableSpace` holds, since that instance makes every set
  measurable and so equals `⊤`; the statement is therefore the one a
  `[MeasurableSpace] [DiscreteMeasurableSpace]` formulation would give, and strictly stronger in
  general.  A consumer must fix `⊤` as well, and rewriting a set equality under such a `𝒟[…]`
  needs `simp [h]` rather than `rw [h]`, since the instance is not syntactically the ambient one.
* `ε` is an arbitrary `ℝ≥0∞ ≠ ⊤`.  The uniform instance `ε = k / |spec.Range t|` for a bad set of
  at most `k` answers is `SampleableType.evalDist_uniformSample_le_of_encard_le`.
* The charge bound is stated for a cost function charging at least `1` per public-hash query; it
  says nothing about private sampling queries, which may be charged anything.
* Nothing here is quantum: `spec.randomOracle` is a classical lazily-sampled table and `enncard`
  is a classical query count.

## Labels

Eleven declarations.

*The potential engine*:

* `OracleComp.le_of_mem_support_run_simulateQ_of_step`,
  `OracleComp.evalDist_apply_setOf_and_le_of_potential`.

*Step shapes of the shared lazy oracle*:

* `OracleComp.snd_eq_of_mem_support_run_unifFwdImpl`,
  `OracleComp.exists_run_unifFwdImpl_add_randomOracle_inl`,
  `OracleComp.run_unifFwdImpl_add_randomOracle_inr_some`,
  `OracleComp.run_unifFwdImpl_add_randomOracle_inr_none`.

*The fresh-answer bound*:

* `OracleComp.evalDist_run_setOf_le_of_fresh_bound`.

*The charge bound*:

* `OracleComp.le_add_cost_of_mem_support_runAdd_run`,
  `OracleComp.mem_support_runAdd_run_withAddCost_iff`,
  `OracleComp.exists_mem_support_runAdd_of_mem_support_run`,
  `OracleComp.enncard_le_add_cost_of_mem_support_runAdd_run_withAddCost`.
-/

public section

open OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

/-! ## The potential engine -/

section Potential

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- A potential that never decreases along a step never decreases along a whole run. -/
theorem le_of_mem_support_run_simulateQ_of_step (so : QueryImpl spec (StateT σ ProbComp))
    (Φ : σ → ℝ≥0∞) (hmono : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s), Φ s ≤ Φ z.2)
    (oa : OracleComp spec α) (s : σ) {z : α × σ} (hz : z ∈ support ((simulateQ so oa).run s)) :
    Φ s ≤ Φ z.2 :=
  simulateQ_run_preservesInv so (Φ s ≤ Φ ·) (fun t s' hs' z hz => hs'.trans (hmono t s' z hz))
    oa s le_rfl z hz

/-- **The potential-charged first-fire bound.**  `P` is a predicate on the state and `Φ` a
potential that never decreases along a step.  If every step out of a state where `P` fails is
either deterministic and lands again where `P` fails, or a sample `samp` with state update `upd`
whose firing mass `𝒟[samp] {u | P (upd u)}` is at most a weight `w` that the step adds to `Φ`,
then from a state where `P` fails the mass of the paths whose final state fires `P` with
`Φ ≤ K` is at most `K - Φ s`.

The measurable-space instance on `α × σ` is pinned to `⊤` inside the statement because the
induction that proves it changes `α`; a consumer must fix `⊤` too. -/
theorem evalDist_apply_setOf_and_le_of_potential (so : QueryImpl spec (StateT σ ProbComp))
    (P : σ → Prop) (Φ : σ → ℝ≥0∞)
    (hmono : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s), Φ s ≤ Φ z.2)
    (hstep : ∀ (t : spec.Domain) (s : σ), ¬ P s →
      (∃ a s', (so t).run s = pure (a, s') ∧ ¬ P s') ∨
      (∃ (samp : ProbComp (spec.Range t)) (upd : spec.Range t → σ) (w : ℝ≥0∞),
        (so t).run s = (fun u => (u, upd u)) <$> samp ∧
        (letI : MeasurableSpace (spec.Range t) := ⊤; 𝒟[samp] {u | P (upd u)} ≤ w) ∧
        ∀ u, w + Φ s ≤ Φ (upd u)))
    (oa : OracleComp spec α) (K : ℝ≥0∞) (hK' : K ≠ ⊤) :
    ∀ s : σ, ¬ P s →
      (letI : MeasurableSpace (α × σ) := ⊤;
        𝒟[(simulateQ so oa).run s] {z | P z.2 ∧ Φ z.2 ≤ K} ≤ K - Φ s) := by
  let _ : MeasurableSpace (α × σ) := ⊤
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s hs
    rw [simulateQ_pure, StateT.run_pure, evalDist_pure,
      Measure.dirac_apply' _ MeasurableSet.of_discrete]
    simp [Set.indicator, hs]
  | query_bind t k ih =>
    intro s hs
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases hstep t s hs with ⟨a, s', hrun, hs'⟩ | ⟨samp, upd, w, hrun, hw, hΦ⟩
    · rw [hrun, pure_bind]
      exact (ih a s' hs').trans (tsub_le_tsub_left (hmono t s (a, s')
        (by rw [hrun, support_pure]; exact Set.mem_singleton _)) K)
    · rw [hrun]
      let _ : MeasurableSpace (spec.Range t) := ⊤
      let _ : MeasurableSpace (spec.Range t × σ) := ⊤
      have hpath : ∀ z ∈ support (((fun u => (u, upd u)) <$> samp) >>= fun p =>
          (simulateQ so (k p.1)).run p.2), w + Φ s ≤ Φ z.2 := by
        intro z hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨p, hp, hz⟩ := hz
        rw [support_map] at hp
        obtain ⟨u, -, rfl⟩ := hp
        exact (hΦ u).trans (le_of_mem_support_run_simulateQ_of_step so Φ hmono (k u) (upd u) hz)
      by_cases hK : w + Φ s ≤ K
      · have hbadBound : 𝒟[(fun u => (u, upd u)) <$> samp]
            {p : spec.Range t × σ | P p.2 ∨ ∀ u, p ≠ (u, upd u)} ≤ w := by
          rw [evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete
            MeasurableSet.of_discrete]
          refine le_trans (le_of_eq (congrArg _ ?_)) hw
          ext u
          exact ⟨fun h => h.elim id fun h => absurd rfl (h u), Or.inl⟩
        refine (evalDist_bind_apply_le_add_of_bad _ _ Measurable.of_discrete
          MeasurableSet.of_discrete MeasurableSet.of_discrete hbadBound (ε₂ := K - (w + Φ s))
          ?_).trans (le_of_eq ?_)
        · rintro ⟨u, s'⟩ hgood
          have hP : ¬ P s' := fun h => hgood (Or.inl h)
          obtain ⟨u', hu'⟩ : ∃ u', (u, s') = (u', upd u') := by
            by_contra h
            exact hgood (Or.inr fun u' hu' => h ⟨u', hu'⟩)
          obtain ⟨h1, h2⟩ := Prod.mk.inj hu'
          subst h1 h2
          exact (ih u (upd u) hP).trans (tsub_le_tsub_left (hΦ u) K)
        · rw [tsub_add_eq_tsub_tsub_swap, add_tsub_cancel_of_le (ENNReal.le_sub_of_add_le_right
            (ne_top_of_le_ne_top hK' (le_add_self.trans hK)) hK)]
      · rw [evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete]
        · exact zero_le
        · exact fun z hz hmem => hK ((hpath z hz).trans hmem.2)

end Potential

/-! ## Step shapes of the shared lazy oracle -/

section Steps

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

omit [DecidableEq ι] [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- A private-sampling step leaves the cache untouched. -/
theorem snd_eq_of_mem_support_run_unifFwdImpl (i : unifSpec.Domain) (c : spec.QueryCache)
    {z : unifSpec.Range i × spec.QueryCache}
    (hz : z ∈ support ((unifFwdImpl spec i).run c)) : z.2 = c := by
  rw [unifFwdImpl, QueryImpl.liftTarget_apply, StateT.run_liftM, bind_pure_comp,
    support_map] at hz
  obtain ⟨_, -, rfl⟩ := hz
  rfl

/-- A private-sampling step of the shared lazy oracle is a sample that leaves the cache
untouched. -/
theorem exists_run_unifFwdImpl_add_randomOracle_inl (i : unifSpec.Domain)
    (c : spec.QueryCache) :
    ∃ samp : ProbComp (unifSpec.Range i),
      ((unifFwdImpl spec + spec.randomOracle) (Sum.inl i)).run c =
        (fun u => (u, c)) <$> samp :=
  ⟨liftM (OracleSpec.query i), by simp [unifFwdImpl]⟩

/-- A public-hash step at an already cached query is deterministic and leaves the cache
untouched. -/
theorem run_unifFwdImpl_add_randomOracle_inr_some {t : spec.Domain} {c : spec.QueryCache}
    {u : spec.Range t} (h : c t = some u) :
    ((unifFwdImpl spec + spec.randomOracle) (Sum.inr t)).run c = pure (u, c) := by
  simp [h]

/-- A public-hash step at a query that was not already cached samples uniformly and caches the
answer. -/
theorem run_unifFwdImpl_add_randomOracle_inr_none {t : spec.Domain} {c : spec.QueryCache}
    (h : c t = none) :
    ((unifFwdImpl spec + spec.randomOracle) (Sum.inr t)).run c =
      (fun u => (u, c.cacheQuery t u)) <$> ($ᵗ spec.Range t) := by
  simp [h]

/-! ## The fresh-answer bound -/

/-- **The fresh-answer bound for a shared lazy random oracle.**  `P` is a predicate on the
public-hash cache that fails of the empty cache, and `ε` bounds, uniformly in the query and in
the not-yet-firing cache, the mass of the fresh answers that make `P` fire.  Then along a whole
run of `unifFwdImpl spec + spec.randomOracle` from the empty cache, `P` holds of the final cache
with mass at most `q * ε` on the paths whose final cache has at most `q` entries.

The measurable-space instance on `α × spec.QueryCache` is pinned to `⊤` inside the statement, so
a consumer must fix `⊤` too. -/
theorem evalDist_run_setOf_le_of_fresh_bound (P : spec.QueryCache → Prop) (hP : ¬ P ∅)
    (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : spec.Domain) (c : spec.QueryCache), ¬ P c → c t = none →
      (letI : MeasurableSpace (spec.Range t) := ⊤;
        𝒟[($ᵗ spec.Range t : ProbComp (spec.Range t))] {u | P (c.cacheQuery t u)} ≤ ε))
    {α : Type} (oa : OracleComp (unifSpec + spec) α) (q : ℕ) :
    (letI : MeasurableSpace (α × spec.QueryCache) := ⊤;
      𝒟[(simulateQ (unifFwdImpl spec + spec.randomOracle) oa).run ∅]
        {z | P z.2 ∧ QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} ≤ (q : ℝ≥0∞) * ε) := by
  let _ : MeasurableSpace (α × spec.QueryCache) := ⊤
  have hmono : ∀ (t : (unifSpec + spec).Domain) (c : spec.QueryCache),
      ∀ z ∈ support (((unifFwdImpl spec + spec.randomOracle) t).run c),
        QueryCache.enncard c * ε ≤ QueryCache.enncard z.2 * ε := by
    intro t c z hz
    have hle : c ≤ z.2 := le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl
      (liftM (OracleSpec.query t) : OracleComp (unifSpec + spec) ((unifSpec + spec).Range t))
      (by simpa using hz)
    gcongr
    exact QueryCache.enncard_mono hle
  have hstep : ∀ (t : (unifSpec + spec).Domain) (c : spec.QueryCache), ¬ P c →
      (∃ a c', (((unifFwdImpl spec + spec.randomOracle) t).run c) = pure (a, c') ∧ ¬ P c') ∨
      (∃ (samp : ProbComp ((unifSpec + spec).Range t))
        (upd : (unifSpec + spec).Range t → spec.QueryCache) (w : ℝ≥0∞),
        (((unifFwdImpl spec + spec.randomOracle) t).run c) = (fun u => (u, upd u)) <$> samp ∧
        (letI : MeasurableSpace ((unifSpec + spec).Range t) := ⊤;
          𝒟[samp] {u | P (upd u)} ≤ w) ∧
        ∀ u, w + QueryCache.enncard c * ε ≤ QueryCache.enncard (upd u) * ε) := by
    rintro (i | t) c hc
    · obtain ⟨samp, hsamp⟩ := exists_run_unifFwdImpl_add_randomOracle_inl (spec := spec) i c
      exact Or.inr ⟨samp, fun _ => c, 0, hsamp, by simp [hc], fun _ => by simp⟩
    · rcases h : c t with _ | u
      · exact Or.inr ⟨$ᵗ spec.Range t, fun u => c.cacheQuery t u, ε,
          run_unifFwdImpl_add_randomOracle_inr_none h, hfresh t c hc h,
          fun u => by rw [QueryCache.enncard_cacheQuery c t u h, add_mul, one_mul, add_comm]⟩
      · exact Or.inl ⟨u, c, run_unifFwdImpl_add_randomOracle_inr_some h, hc⟩
  have key := evalDist_apply_setOf_and_le_of_potential
    (unifFwdImpl spec + spec.randomOracle) P (fun c => QueryCache.enncard c * ε) hmono hstep oa
    ((q : ℝ≥0∞) * ε) (ENNReal.mul_ne_top (by simp) hε) ∅ hP
  rw [QueryCache.enncard_empty, zero_mul, tsub_zero] at key
  refine le_trans (measure_mono fun z hz => ?_) key
  exact ⟨hz.1, by have := hz.2; gcongr⟩

end Steps

/-! ## The charge bound -/

section Charge

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- A potential that grows by at most the charge of each step grows by at most the total charge
of the run. -/
theorem le_add_cost_of_mem_support_runAdd_run
    (impl : QueryImpl spec (AddWriterT ℕ (StateT σ ProbComp))) (Φ : σ → ℝ≥0∞)
    (hstep : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((impl t).runAdd.run s),
      Φ z.2 ≤ Φ s + z.1.2)
    (oa : OracleComp spec α) :
    ∀ (s : σ), ∀ z ∈ support ((simulateQ impl oa).runAdd.run s), Φ z.2 ≤ Φ s + z.1.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s z hz; simp_all
  | query_bind t k ih =>
    intro s z hz
    rw [simulateQ_bind, simulateQ_spec_query, AddWriterT.runAdd_bind, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨⟨⟨u, w⟩, s'⟩, hu, hz⟩ := hz
    rw [StateT.run_map, support_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have h : Φ z'.2 ≤ Φ s + ((w : ℝ≥0∞) + (z'.1.2 : ℝ≥0∞)) := by
      refine (ih u s' z' hz').trans ?_
      rw [← add_assoc]
      exact add_le_add (hstep t s _ hu) le_rfl
    simpa [Prod.map, Nat.cast_add, add_assoc] using h

/-- The support of one cost-instrumented step: the charge is the step's cost and the underlying
step is unchanged. -/
theorem mem_support_runAdd_run_withAddCost_iff (impl : QueryImpl spec (StateT σ ProbComp))
    (cost : spec.Domain → ℕ) (t : spec.Domain) (s : σ) (z : (spec.Range t × ℕ) × σ) :
    z ∈ support (((impl.withAddCost cost) t).runAdd.run s) ↔
      z.1.2 = cost t ∧ (z.1.1, z.2) ∈ support ((impl t).run s) := by
  rw [QueryImpl.withAddCost_apply]
  simp only [AddWriterT.runAdd_bind, AddWriterT.runAdd_addTell, pure_bind,
    AddWriterT.runAdd_liftM, StateT.run_map, support_map, Set.mem_image, Prod.map, id_eq]
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨by simp, by simpa using hx⟩
  · rintro ⟨hw, hmem⟩
    exact ⟨((z.1.1, 0), z.2), ⟨(z.1.1, z.2), hmem, rfl⟩, by simp only [add_zero, ← hw]⟩

/-- Every path of an uninstrumented run is a path of the cost-instrumented run at some charge. -/
theorem exists_mem_support_runAdd_of_mem_support_run (impl : QueryImpl spec (StateT σ ProbComp))
    (cost : spec.Domain → ℕ) (oa : OracleComp spec α) (s : σ) {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run s)) :
    ∃ n, ((z.1, n), z.2) ∈ support ((simulateQ (impl.withAddCost cost) oa).runAdd.run s) := by
  rw [← QueryImpl.fst_map_runAdd_withAddCost impl cost oa, StateT.run_map, support_map] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  exact ⟨w.1.2, by rw [← congrArg Prod.fst hwz, ← congrArg Prod.snd hwz]; exact hw⟩

end Charge

section CacheCharge

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)] {α : Type}

/-- **The cache never holds more entries than the charge.**  For any cost function charging at
least `1` to every public-hash query, the final cache of a cost-instrumented run of the shared
lazy oracle has at most `enncard` of the initial cache plus the run's total charge many
entries. -/
theorem enncard_le_add_cost_of_mem_support_runAdd_run_withAddCost
    (cost : (unifSpec + spec).Domain → ℕ) (hcost : ∀ t : spec.Domain, 1 ≤ cost (Sum.inr t))
    (oa : OracleComp (unifSpec + spec) α) (c : spec.QueryCache) :
    ∀ z ∈ support ((simulateQ ((unifFwdImpl spec + spec.randomOracle).withAddCost cost)
      oa).runAdd.run c),
      QueryCache.enncard z.2 ≤ QueryCache.enncard c + (z.1.2 : ℝ≥0∞) := by
  refine le_add_cost_of_mem_support_runAdd_run _ QueryCache.enncard ?_ oa c
  rintro (i | t) s ⟨⟨u, w⟩, s'⟩ hz
  · obtain ⟨rfl, hmem⟩ := (mem_support_runAdd_run_withAddCost_iff _ _ _ s _).mp hz
    rw [QueryImpl.add_apply_inl] at hmem
    rw [snd_eq_of_mem_support_run_unifFwdImpl i s hmem]
    simp
  · obtain ⟨rfl, hmem⟩ := (mem_support_runAdd_run_withAddCost_iff _ _ _ s _).mp hz
    rcases h : s t with _ | v
    · rw [run_unifFwdImpl_add_randomOracle_inr_none h, support_map] at hmem
      obtain ⟨u', -, hu'⟩ := hmem
      obtain ⟨-, rfl⟩ := Prod.mk.inj hu'
      rw [QueryCache.enncard_cacheQuery s t u' h]
      gcongr
      exact_mod_cast hcost t
    · rw [run_unifFwdImpl_add_randomOracle_inr_some h, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨-, rfl⟩ := Prod.mk.inj hmem
      simp

end CacheCharge

end OracleComp
