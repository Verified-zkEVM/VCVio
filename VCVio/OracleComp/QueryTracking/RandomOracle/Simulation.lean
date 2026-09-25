/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
import VCVio.OracleComp.EvalDist.Measure

/-!
# The Random Oracle Model

This file provides the random oracle model for computations `OracleComp (unifSpec + hashSpec)`.
The handler `OracleSpec.romImpl hashSpec` forwards uniform-sampling queries to `ProbComp` and
answers `hashSpec` queries with the lazily sampled random oracle `hashSpec.randomOracle`, whose
cache is the state of `StateT hashSpec.QueryCache ProbComp`. The runtime
`ProbCompRuntime.rom hashSpec cache` interprets experiments through `romImpl` from the initial
cache `cache`, empty by default; a nonempty cache programs the random oracle at its entries.

The `roSim` lemmas are stated for `unifFwdImpl hashSpec + ro` with a general hash handler `ro`.
They apply to `romImpl`, which unfolds reducibly to `unifFwdImpl hashSpec + hashSpec.randomOracle`,
and equally to programmed or logged hash handlers. They show that lifted `ProbComp` computations
and computations without hash queries leave the cache unchanged, and that a hash query is
dispatched to `ro`.

`OracleComp.unifFwdAnswerImpl` answers hash queries from a fixed deterministic table instead. A
run of `romImpl` from a cache reaches an output iff some answer table agreeing with that cache
does, so a probability-one claim about `romImpl` reduces to the same claim for every such table.

## Main definitions

* `unifFwdImpl`: the identity forwarding implementation for `unifSpec`, lifted to `StateT`
* `OracleSpec.romImpl`: the random oracle model handler `unifFwdImpl hashSpec + randomOracle`,
  equal to `unifSpec.passthrough + hashSpec.randomOracle`
* `ProbCompRuntime.rom`: the random-oracle-model runtime, interpreting through `romImpl` from a
  given initial cache
* `OracleComp.unifFwdAnswerImpl`: forwards uniform queries while using a fixed deterministic
  answer table for the other summand

## Main statements

* `OracleComp.probEvent_eq_one_simulateQ_romImpl_run_iff`: reduces a probability-one claim for
  `romImpl` to all fixed answer tables agreeing with the initial cache
-/

@[expose] public section

open MeasureTheory OracleComp OracleSpec

variable {ι : Type} {hashSpec : OracleSpec ι}

/-- The identity forwarding implementation for `unifSpec` queries, lifted to
`StateT hashSpec.QueryCache ProbComp`. Each uniform query passes through to the underlying
`ProbComp` without touching the cache state. -/
def unifFwdImpl (hashSpec : OracleSpec ι) :
    QueryImpl unifSpec (StateT hashSpec.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT hashSpec.QueryCache ProbComp)

namespace unifFwdImpl

/-- The explicit lift-based forwarding handler agrees with the canonical `HasQuery` handler. -/
lemma eq_toQueryImpl :
    unifFwdImpl hashSpec =
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT hashSpec.QueryCache ProbComp) := by
  unfold unifFwdImpl
  congr 1

/-- Simulating a plain `ProbComp` through `unifFwdImpl` and running it on cache `s` leaves
the cache untouched, pairing each sampled output with the unchanged `s`. -/
lemma simulateQ_run {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec) oa).run s = (fun x => (x, s)) <$> oa := by
  rw [eq_toQueryImpl]
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [← ih]

end unifFwdImpl

namespace roSim

variable (ro : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))

/-- Simulating a `liftComp`-embedded `ProbComp` through `unifFwdImpl + ro` discards the hash
oracle, reducing to simulation through `unifFwdImpl` alone. -/
lemma simulateQ_liftComp {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (OracleComp.liftComp oa (unifSpec + hashSpec)) =
    simulateQ (unifFwdImpl hashSpec) oa :=
  QueryImpl.simulateQ_add_liftComp_left
    (m' := StateT hashSpec.QueryCache ProbComp) (unifFwdImpl hashSpec) ro oa

/-- Running the `unifFwdImpl + ro` simulation of a lifted `ProbComp` on cache `s` leaves the
cache untouched, pairing each sampled output with `s`. -/
lemma run_liftM {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s =
      (fun x => (x, s)) <$> oa := by
  rw [show simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) =
      simulateQ (unifFwdImpl hashSpec) oa from simulateQ_liftComp ro oa]
  exact unifFwdImpl.simulateQ_run oa s

/-- The support of the `unifFwdImpl + ro` simulation of a lifted `ProbComp` run on cache `s`
is the image of `support oa` under pairing each output with `s`. -/
lemma run_liftM_support {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    support ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s) =
      (fun x => (x, s)) '' support oa := by
  rw [run_liftM, support_map]

/-- Running the `unifFwdImpl + ro` simulation of a lifted `ProbComp` bound to a continuation,
projected to its value via `run'`, samples `oa` and then runs each continuation on cache `s`. -/
lemma run'_liftM_bind {α β : Type} (oa : ProbComp α)
    (rest : α → StateT hashSpec.QueryCache ProbComp β) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run' s =
      oa >>= fun x => (rest x).run' s := by
  change Prod.fst <$>
    ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run s) =
    oa >>= fun x => Prod.fst <$> (rest x).run s
  rw [StateT.run_bind, run_liftM]
  simp [map_bind]

/-- A computation with zero budget on a predicate that charges every `hashSpec` query queries
only the uniform summand. -/
private lemma allQueriesSatisfy_not_of_isQueryBoundP_zero {α : Type} {p : ℕ ⊕ ι → Prop}
    [DecidablePred p] {oa : OracleComp (unifSpec + hashSpec) α} (h : oa.IsQueryBoundP p 0) :
    oa.AllQueriesSatisfy (fun t => ¬ p t) :=
  (isQueryBoundP_zero_iff oa _).1 ((isQueryBoundP_congr_pred fun _ => not_not.symm).1 h)

/-- Every query outside a predicate that charges every `hashSpec` query is a uniform query, which
`unifFwdImpl + ro` answers without touching the cache. -/
private lemma run_eq_map_run'_of_not {p : ℕ ⊕ ι → Prop} (hp : ∀ t, p (.inr t))
    (t : ℕ ⊕ ι) (ht : ¬ p t) (s : hashSpec.QueryCache) :
    ((unifFwdImpl hashSpec + ro) t).run s = (·, s) <$> ((unifFwdImpl hashSpec + ro) t).run' s := by
  rcases t with n | t
  · simp [unifFwdImpl, StateT.run'_eq]
  · exact absurd (hp t) ht

/-- Simulating through `unifFwdImpl + ro` a computation that makes no `hashSpec` query leaves
the cache untouched, whatever `ro` does on hash queries. The query bound is stated for any
predicate `p` that charges every `hashSpec` query, such as `(· matches .inr _)`. This is the
counterpart of `run_liftM` for a computation given with a query bound rather than as a lifted
`ProbComp`. -/
lemma run_eq_map_run'_of_isQueryBoundP_zero {α : Type} {p : ℕ ⊕ ι → Prop} [DecidablePred p]
    (hp : ∀ t, p (.inr t)) {oa : OracleComp (unifSpec + hashSpec) α}
    (h : oa.IsQueryBoundP p 0) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) oa).run s =
      (·, s) <$> (simulateQ (unifFwdImpl hashSpec + ro) oa).run' s :=
  (allQueriesSatisfy_not_of_isQueryBoundP_zero h).simulateQ_run_eq_map_run'
    (run_eq_map_run'_of_not ro hp) s

/-- A prefix with no `hashSpec` query hands its initial cache to the continuation. -/
lemma run'_bind_of_isQueryBoundP_zero {α β : Type} {p : ℕ ⊕ ι → Prop} [DecidablePred p]
    (hp : ∀ t, p (.inr t)) {oa : OracleComp (unifSpec + hashSpec) α}
    (h : oa.IsQueryBoundP p 0) (ob : α → OracleComp (unifSpec + hashSpec) β)
    (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (oa >>= ob)).run' s =
      (simulateQ (unifFwdImpl hashSpec + ro) oa).run' s >>= fun x =>
        (simulateQ (unifFwdImpl hashSpec + ro) (ob x)).run' s :=
  (allQueriesSatisfy_not_of_isQueryBoundP_zero h).simulateQ_run'_bind
    (run_eq_map_run'_of_not ro hp) ob s

/-- A uniform-sampling query of `unifFwdImpl + ro` samples and leaves the cache unchanged. -/
lemma run_apply_inl (n : ℕ) (s : hashSpec.QueryCache) :
    ((unifFwdImpl hashSpec + ro) (Sum.inl n)).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simpa using unifFwdImpl.simulateQ_run (hashSpec := hashSpec)
    (unifSpec.query n : ProbComp (Fin (n + 1))) s

/-- Simulating a `hashSpec` query through `unifFwdImpl + ro` dispatches it to the hash-oracle
handler `ro`, since uniform forwarding leaves hash queries to `ro`. -/
@[simp]
lemma simulateQ_liftM_spec_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro) (hashSpec.query q) = ro q := by
  change simulateQ (unifFwdImpl hashSpec + ro)
    (liftM (liftM (hashSpec.query q) :
      OracleQuery (unifSpec + hashSpec) _)) = _
  exact QueryImpl.simulateQ_add_liftM_query_right (unifFwdImpl hashSpec) ro q

/-- Simulating a `HasQuery.query` hash query through `unifFwdImpl + ro` dispatches it to the
hash-oracle handler `ro`, matching `simulateQ_liftM_spec_query` through the monad-lift form. -/
lemma simulateQ_HasQuery_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (HasQuery.query (spec := hashSpec)
        (m := OracleComp (unifSpec + hashSpec)) q) =
      ro q := by
  simp

end roSim

/-! ## The random oracle model -/

namespace OracleSpec

variable (hashSpec) [DecidableEq ι] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]

/-- The random oracle model for `unifSpec + hashSpec`: uniform-sampling queries reach the ambient
`ProbComp` unchanged, and `hashSpec` queries are answered by the lazily sampled random oracle
`hashSpec.randomOracle`, whose cache is the state. Simulating `oa` with `hashSpec.romImpl` from the
empty cache is the execution of `oa` in the random oracle model.

It is `unifSpec.passthrough + hashSpec.randomOracle` (`romImpl_eq_passthrough_add`). It unfolds
reducibly to `unifFwdImpl hashSpec + hashSpec.randomOracle`, so the `roSim` lemmas apply to it. -/
abbrev romImpl : QueryImpl (unifSpec + hashSpec) (StateT hashSpec.QueryCache ProbComp) :=
  unifFwdImpl hashSpec + hashSpec.randomOracle

variable {hashSpec}

lemma romImpl_eq_passthrough_add :
    hashSpec.romImpl = unifSpec.passthrough + hashSpec.randomOracle :=
  rfl

lemma romImpl_apply_inr (t : hashSpec.Domain) :
    hashSpec.romImpl (.inr t) = hashSpec.randomOracle t :=
  rfl

/-- Simulating a lifted `ProbComp` in the random oracle model samples it and leaves the cache
unchanged. -/
lemma simulateQ_romImpl_liftM_run {α : Type} (oa : ProbComp α) (cache : hashSpec.QueryCache) :
    (simulateQ hashSpec.romImpl (liftM oa)).run cache = (·, cache) <$> oa :=
  roSim.run_liftM _ oa cache

end OracleSpec

namespace ProbCompRuntime

/-- The runtime of the random oracle model for `unifSpec + hashSpec`: experiments are simulated
with `hashSpec.romImpl` starting from the random-oracle cache `cache`, empty unless given, and
plain `ProbComp` sampling lifts into the uniform summand. A nonempty `cache` programs the random
oracle at the cached points. -/
noncomputable def rom (hashSpec : OracleSpec ι) [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    (cache : hashSpec.QueryCache := ∅) : ProbCompRuntime (OracleComp (unifSpec + hashSpec)) :=
  withStateOracle hashSpec.randomOracle cache

/-- The random-oracle-model runtime observes the simulation under `romImpl` from its cache. -/
lemma rom_evalDist [DecidableEq ι] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    (cache : hashSpec.QueryCache) {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + hashSpec) α) :
    (rom hashSpec cache).evalDist oa = 𝒟[(simulateQ hashSpec.romImpl oa).run' cache] :=
  rfl

/-- The random-oracle-model runtime commutes with a lifted `ProbComp` prefix: evaluating
`liftM oa >>= rest` samples `oa` and then integrates the runtime measures of `rest x`. -/
lemma rom_evalDist_bind_liftM [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] (cache : hashSpec.QueryCache)
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (oa : ProbComp α) (rest : α → OracleComp (unifSpec + hashSpec) β) :
    (rom hashSpec cache).evalDist (liftM oa >>= rest) =
      Measure.bind 𝒟[oa] fun x => (rom hashSpec cache).evalDist (rest x) := by
  simp_rw [rom_evalDist]
  rw [simulateQ_bind, roSim.run'_liftM_bind, evalDist_bind_of_discrete]

end ProbCompRuntime

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Interpret uniform queries probabilistically while answering every `spec` query with the
deterministic table `f`. This is the fixed-table counterpart of the random oracle model handler
`spec.romImpl`. -/
def unifFwdAnswerImpl (f : QueryImpl spec Id) :
    QueryImpl (unifSpec + spec) ProbComp :=
  unifSpec.passthrough + f.liftTarget ProbComp

/-- The random-oracle simulation of a plain `OracleComp` never fails on any starting cache. -/
theorem neverFail_simulateQ_randomOracle_run
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    NeverFail ((simulateQ randomOracle oa).run cache) := by
  infer_instance

/-- Running the lazy random oracle on an uncached query `t` and binding the result samples the
fresh answer uniformly, so the support of the bound computation is the union over all answers of
the support obtained after caching that answer. -/
private lemma support_randomOracle_run_bind_of_uncached [DecidableEq ι]
    [(t : spec.Domain) → SampleableType (spec.Range t)] {β : Type} (t : spec.Domain)
    {cache : spec.QueryCache} (hcache : cache t = none)
    (g : spec.Range t × spec.QueryCache → ProbComp β) :
    support ((randomOracle (spec := spec) t).run cache >>= g) =
      ⋃ u, support (g (u, cache.cacheQuery t u)) := by
  rw [QueryImpl.withCaching_run_none _ hcache, support_bind, support_map,
    show support (uniformSampleImpl t) = Set.univ from support_uniformSample _]
  simp

/-- Support characterization for a computation with both fresh uniform queries and a lazy
random oracle.

An output `a` is reachable from `cache` under the random oracle model handler `spec.romImpl` iff
it is reachable while keeping the uniform queries probabilistic and replacing the hash oracle by
some total deterministic answer table that agrees with `cache`. The final lazy-oracle cache is
existentially quantified away. -/
theorem exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp (unifSpec + spec) α) (cache : spec.QueryCache) (a : α) :
    (∃ f : QueryImpl spec Id, cache.AgreesWithFn f ∧
      a ∈ support (simulateQ (unifFwdAnswerImpl f) oa))
    ↔
    (∃ cache' : spec.QueryCache,
      (a, cache') ∈ support
        ((simulateQ spec.romImpl oa).run cache)) := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a with
  | pure x =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff,
      StateT.run_pure, Prod.mk.injEq]
    refine ⟨fun ⟨_, _, h⟩ => ⟨cache, h, rfl⟩, fun ⟨_, ha, _⟩ => ?_⟩
    obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := spec) cache
    exact ⟨f, hf, ha⟩
  | query_bind t k ih =>
    cases t with
    | inl t =>
      simp only [simulateQ_bind, simulateQ_spec_query, unifFwdAnswerImpl,
        QueryImpl.add_apply_inl, unifFwdImpl,
        QueryImpl.liftTarget_apply, StateT.run_bind, StateT.run_liftM,
        support_bind, Set.mem_iUnion]
      constructor
      · rintro ⟨f, hf, u, hu, ha⟩
        obtain ⟨cache', hcache'⟩ := (ih u cache a).mp
          ⟨f, hf, by simpa [unifFwdAnswerImpl] using ha⟩
        exact ⟨cache', (u, cache), ⟨u, hu, by simp⟩, hcache'⟩
      · rintro ⟨cache', ⟨u, cache₀⟩, ⟨u', hu', hpair⟩, ha⟩
        have hpair' : (u, cache₀) = (u', cache) := by simpa using hpair
        have hu : u = u' := congrArg Prod.fst hpair'
        have hc : cache₀ = cache := congrArg Prod.snd hpair'
        subst u'
        subst cache₀
        obtain ⟨f, hf, hs⟩ := (ih u cache a).mpr ⟨cache', ha⟩
        exact ⟨f, hf, u, hu', by simpa [unifFwdAnswerImpl] using hs⟩
    | inr t =>
      have h_eval : ∀ f : QueryImpl spec Id,
          simulateQ (unifFwdAnswerImpl f)
              (liftM ((unifSpec + spec).query (Sum.inr t)) >>= k) =
            simulateQ (unifFwdAnswerImpl f) (k (f t)) := by
        intro f
        rw [simulateQ_bind, simulateQ_spec_query]
        change (pure (f t) : ProbComp _) >>= (fun u =>
          simulateQ (unifFwdAnswerImpl f) (k u)) = _
        rw [pure_bind]
      simp_rw [h_eval]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OracleSpec.romImpl_apply_inr]
      rcases hcache : cache t with _ | u
      · simp only [support_randomOracle_run_bind_of_uncached t hcache, Set.mem_iUnion]
        constructor
        · rintro ⟨f, hf, ha⟩
          obtain ⟨cache', hcache'⟩ := (ih (f t) (cache.cacheQuery t (f t)) a).mp
            ⟨f, (QueryCache.agreesWithFn_cacheQuery_iff cache t (f t) f hcache).mpr
              ⟨hf, rfl⟩, ha⟩
          exact ⟨cache', f t, hcache'⟩
        · rintro ⟨cache', u, hcache'⟩
          obtain ⟨f, hagree, ha⟩ := (ih u (cache.cacheQuery t u) a).mpr
            ⟨cache', hcache'⟩
          obtain ⟨hf, hfu⟩ :=
            (QueryCache.agreesWithFn_cacheQuery_iff cache t u f hcache).mp hagree
          exact ⟨f, hf, hfu ▸ ha⟩
      · rw [QueryImpl.withCaching_run_some _ hcache, pure_bind]
        constructor
        · rintro ⟨f, hf, ha⟩
          exact (ih u cache a).mp ⟨f, hf, hf hcache ▸ ha⟩
        · intro hsupp
          obtain ⟨f, hf, ha⟩ := (ih u cache a).mpr hsupp
          exact ⟨f, hf, hf hcache ▸ ha⟩

/-- Probability-one form of the combined uniform-query/random-oracle support characterization.

The combined lazy-oracle simulation satisfies `p` almost surely from `preexisting_cache` iff,
for every deterministic hash-answer table extending that cache, the computation that keeps fresh
uniform queries probabilistic and uses that fixed table satisfies `p` almost surely. No separate
`NeverFail` premise is needed: both interpretations are `ProbComp` computations and hence total. -/
theorem probEvent_eq_one_simulateQ_romImpl_run_iff
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp (unifSpec + spec) α) (preexisting_cache : spec.QueryCache) (p : α → Prop) :
    Pr[fun v => p v.1 | (simulateQ spec.romImpl oa).run preexisting_cache] = 1
    ↔
    ∀ f : QueryImpl spec Id, preexisting_cache.AgreesWithFn f →
      Pr[p | simulateQ (unifFwdAnswerImpl f) oa] = 1 := by
  classical
  rw [probEvent_eq_one_iff]
  constructor
  · rintro ⟨_, hsupp⟩ f hf
    rw [probEvent_eq_one_iff]
    refine ⟨probFailure_eq_zero' (by infer_instance), ?_⟩
    intro a ha
    obtain ⟨cache', hcache'⟩ :=
      (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
        oa preexisting_cache a).mp ⟨f, hf, ha⟩
    exact hsupp (a, cache') hcache'
  · intro h
    refine ⟨probFailure_eq_zero' (by infer_instance), ?_⟩
    rintro ⟨a, cache'⟩ ha
    obtain ⟨f, hf, has⟩ :=
      (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
        oa preexisting_cache a).mpr ⟨cache', ha⟩
    exact ((probEvent_eq_one_iff.mp (h f hf)).2 a has)

/-- Measure-native probability-one form of the combined uniform-query/random-oracle
characterization. The visible state is discarded before the output event is measured. -/
theorem evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (oa : OracleComp (unifSpec + spec) α) (preexisting_cache : spec.QueryCache) (p : α → Prop) :
    𝒟[(simulateQ spec.romImpl oa).run' preexisting_cache] {x | p x} = 1
    ↔
    ∀ f : QueryImpl spec Id, preexisting_cache.AgreesWithFn f →
      𝒟[simulateQ (unifFwdAnswerImpl f) oa] {x | p x} = 1 := by
  rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support]
  constructor
  · intro h f hf
    rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support]
    intro a ha
    obtain ⟨cache', hcache'⟩ :=
      (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
        oa preexisting_cache a).mp ⟨f, hf, ha⟩
    apply h a
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst hcache'
  · intro h a ha
    rw [StateT.run'_eq, support_map, Set.mem_image] at ha
    obtain ⟨⟨a', cache'⟩, ha', rfl⟩ := ha
    obtain ⟨f, hf, haf⟩ :=
      (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
        oa preexisting_cache a').mpr ⟨cache', ha'⟩
    exact (OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support
      (simulateQ (unifFwdAnswerImpl f) oa) p).mp (h f hf) a' haf

/-- Support characterization for lazy random-oracle simulation.

A value `a` can appear as the output of the random-oracle simulation from `cache` iff some total
answer function agreeing with `cache` evaluates the computation to `a`. The final cache produced
by the simulation is existentially quantified away. -/
theorem exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (cache : spec.QueryCache) (a : α) :
    (∃ f : QueryImpl spec Id, cache.AgreesWithFn f ∧ evalWithAnswerFn f oa = a)
    ↔
    (∃ cache' : spec.QueryCache,
      (a, cache') ∈ support ((simulateQ randomOracle oa).run cache)) := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq]
    refine ⟨fun ⟨_, _, h⟩ => ⟨cache, h.symm, rfl⟩, fun ⟨_, ha, _⟩ => ?_⟩
    obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := spec) cache
    exact ⟨f, hf, ha.symm⟩
  | query_bind t k ih =>
    have h_eval : ∀ f : QueryImpl spec Id, evalWithAnswerFn f (liftM (spec.query t) >>= k)
        = evalWithAnswerFn f (k (f t)) := fun f => by
      rw [evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (spec.query t)) = f t from simulateQ_spec_query f t]
    simp_rw [h_eval]
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases hcache : cache t with _ | u
    · simp only [support_randomOracle_run_bind_of_uncached t hcache, Set.mem_iUnion]
      refine ⟨fun ⟨f, hf, ha⟩ => ?_, fun ⟨cache', u, hcache'⟩ => ?_⟩
      · obtain ⟨cache', hcache'⟩ := (ih (f t) (cache.cacheQuery t (f t)) a).mp
          ⟨f, (QueryCache.agreesWithFn_cacheQuery_iff cache t (f t) f hcache).mpr ⟨hf, rfl⟩, ha⟩
        exact ⟨cache', f t, hcache'⟩
      · obtain ⟨f, hagree, ha⟩ := (ih u (cache.cacheQuery t u) a).mpr ⟨cache', hcache'⟩
        obtain ⟨hf, hfu⟩ := (QueryCache.agreesWithFn_cacheQuery_iff cache t u f hcache).mp hagree
        exact ⟨f, hf, hfu ▸ ha⟩
    · rw [QueryImpl.withCaching_run_some _ hcache, pure_bind]
      refine ⟨fun ⟨f, hf, ha⟩ => (ih u cache a).mp ⟨f, hf, hf hcache ▸ ha⟩, fun hsupp => ?_⟩
      obtain ⟨f, hf, ha⟩ := (ih u cache a).mpr hsupp
      exact ⟨f, hf, hf hcache ▸ ha⟩

/-- Probability-one form of the random-oracle support characterization.

A predicate on the result value holds with probability one under lazy random-oracle simulation
from `preexisting_cache` iff it holds for every total answer function agreeing with that cache. -/
theorem probEvent_eq_one_simulateQ_randomOracle_run_iff
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (preexisting_cache : spec.QueryCache) (p : α → Prop) :
    Pr[fun v => p v.1 | (simulateQ randomOracle oa).run preexisting_cache] = 1
    ↔
    ∀ f : QueryImpl spec Id, preexisting_cache.AgreesWithFn f → p (evalWithAnswerFn f oa) := by
  classical
  rw [probEvent_eq_one_iff]
  refine ⟨fun ⟨_, hsupp⟩ f hf => ?_, fun h => ⟨?_, ?_⟩⟩
  · obtain ⟨cache', hcache'⟩ :=
      (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support oa preexisting_cache
        (evalWithAnswerFn f oa)).mp ⟨f, hf, rfl⟩
    exact hsupp _ hcache'
  · exact probFailure_eq_zero' (neverFail_simulateQ_randomOracle_run oa preexisting_cache)
  · rintro ⟨a, cache'⟩ hac
    obtain ⟨f, hf, ha⟩ :=
      (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support oa preexisting_cache a).mpr
        ⟨cache', hac⟩
    exact ha ▸ h f hf

end OracleComp

/-- Simulating the random oracle leaves a mapped uniform `Fin` sample unchanged: the query is
intercepted, but from the empty cache it misses and resamples uniformly, and the updated cache is
then discarded by `run'`, so the distribution over results is identical to the original sample. -/
lemma simulateQ_randomOracle_map_uniformFin {α : Type} (n : ℕ) (f : Fin (n + 1) → α) :
    ((simulateQ (unifSpec.randomOracle :
      QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (f <$> uniformSample (Fin (n + 1)) : ProbComp α) :
        StateT unifSpec.QueryCache ProbComp α).run' ∅) =
      (f <$> uniformSample (Fin (n + 1))) := by
  rw [simulateQ_map, StateT.run'_map']
  congr 1
