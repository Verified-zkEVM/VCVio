/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Cache Growth and Programming for the Forwarded Random Oracle

Facts about the random oracle model handler `hashSpec.romImpl`, which forwards uniform sampling
and answers `hashSpec` with a lazy random oracle:

* `roSim.le_of_mem_support_run`: a run only extends its cache.
* `roSim.isCached_of_mem_support_run_withLogging`: along a logged run, the cache gains an answer
  at `t` exactly when the transcript queries `t`.
* `roSim.prEvent_run_uncached_le_run_cacheQuery`: programming an answer at an uncached input is
  invisible to a run until the run queries that input.

Together they justify replacing a random-oracle answer at a hidden input by an independent
sample, up to the event that the input is queried.
-/

public section

open OracleComp OracleSpec

namespace roSim

variable {ι : Type} [DecidableEq ι] {hashSpec : OracleSpec.{0, 0} ι}
  [∀ t, SampleableType (hashSpec.Range t)]

/-- A run of the forwarded lazy random oracle only extends its cache. -/
theorem le_of_mem_support_run {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    (s : hashSpec.QueryCache) :
    ∀ z ∈ support ((simulateQ hashSpec.romImpl oa).run s),
      s ≤ z.2 := by
  refine OracleComp.simulateQ_run_preservesInv _ (s ≤ ·) ?_ oa s le_rfl
  refine QueryImpl.PreservesInv.add ?_ (QueryImpl.PreservesInv.withCaching_le _ s)
  intro n s' hs z hz
  rw [show (unifFwdImpl hashSpec n).run s' =
      (hashSpec.romImpl (Sum.inl n)).run s' from rfl,
    run_apply_inl, support_map] at hz
  obtain ⟨u, _, rfl⟩ := hz
  exact hs

/-- One query of the forwarded lazy random oracle gains a cached answer at `t` exactly when it
queries `t`. -/
theorem isCached_of_mem_support_run_apply {q : ℕ ⊕ ι} {s s' : hashSpec.QueryCache}
    {u : (unifSpec + hashSpec).Range q}
    (h : (u, s') ∈ support ((hashSpec.romImpl q).run s)) (t : ι) :
    s'.isCached t = (s.isCached t || decide (q = Sum.inr t)) := by
  cases q with
  | inl n =>
    rw [run_apply_inl, support_map] at h
    obtain ⟨_, _, h⟩ := h
    rw [Prod.mk.injEq] at h
    rw [← h.2]
    simp
  | inr x =>
    rw [OracleSpec.romImpl_apply_inr, randomOracle.run_eq] at h
    cases hsx : s x with
    | some v =>
      rw [hsx, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rw [h.2]
      by_cases hxt : x = t
      · subst hxt
        simp [QueryCache.isCached, hsx]
      · simp [hxt]
    | none =>
      rw [hsx, mem_support_bind_iff] at h
      obtain ⟨v, _, h⟩ := h
      rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rw [h.2]
      by_cases hxt : x = t
      · subst hxt
        simp
      · simp [hxt, QueryCache.isCached_cacheQuery_of_ne _ _ (Ne.symm hxt)]

/-- Along a logged run of the forwarded lazy random oracle, the cache gains an answer at `t`
exactly when the transcript queries `t`. -/
theorem isCached_of_mem_support_run_withLogging {α : Type}
    (oa : OracleComp (unifSpec + hashSpec) α) (t : ι) :
    ∀ s : hashSpec.QueryCache,
      ∀ z ∈ support (((simulateQ hashSpec.romImpl.withLogging oa).run).run s),
        z.2.isCached t = (s.isCached t || z.1.2.wasQueried (Sum.inr t)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz
    simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind q k ih =>
    intro s z hz
    rw [QueryImpl.run_run_simulateQ_withLogging_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨z', hz', hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨hlog, hstep⟩ :=
      QueryImpl.mem_support_run_simulateQ_withLogging_query_stateT _ q s hp
    rw [ih p.1.1 p.2 z' hz', isCached_of_mem_support_run_apply hstep t,
      QueryLog.wasQueried_append, hlog, Bool.or_assoc]
    congr 2
    by_cases hq : q = Sum.inr t
    · subst hq
      simp
    · simp [hq, QueryLog.wasQueried_cons_of_ne hq]

/-- Programming an answer `u` at an uncached input `t` is invisible to a run of the forwarded
lazy random oracle until the run queries `t`: an event of the unprogrammed run that leaves `t`
uncached is at most as likely as the same event in the programmed run. -/
theorem prEvent_run_uncached_le_run_cacheQuery {α : Type}
    (oa : OracleComp (unifSpec + hashSpec) α) (t : ι) (u : hashSpec.Range t) (E : α → Prop) :
    ∀ s : hashSpec.QueryCache, s t = none →
      Pr{let z ← (simulateQ hashSpec.romImpl oa).run s}[E z.1 ∧ z.2 t = none] ≤
        Pr{let z ← (simulateQ hashSpec.romImpl oa).run (s.cacheQuery t u)}[E z.1] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    by_cases hE : E a <;> simp [hE, hs]
  | query_bind q k ih =>
    intro s hs
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map]
    cases q with
    | inl n =>
      simp only [run_apply_inl, bind_map_left]
      exact OracleComp.evalDist_bind_apply_mono_of_support _ _ _
        (measurableSet_singleton True) fun v _ => ih v s hs
    | inr x =>
      simp only [QueryImpl.add_apply_inr, randomOracle.run_eq]
      by_cases hxt : x = t
      · subst hxt
        refine le_of_eq_of_le ?_ bot_le
        rw [hs]
        simp only [bind_assoc, pure_bind]
        refine evalDist.apply_eq_zero_of_disjoint_support _ (measurableSet_singleton True) ?_
        intro p hp
        rw [mem_support_bind_iff] at hp
        obtain ⟨v, _, hp⟩ := hp
        rw [mem_support_bind_iff] at hp
        obtain ⟨z, hz, hp⟩ := hp
        rw [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        have hcached := le_of_mem_support_run (k v) (s.cacheQuery x v) z hz
          (QueryCache.cacheQuery_self s x v)
        simp [hcached]
      · rw [QueryCache.cacheQuery_of_ne _ _ hxt]
        cases hsx : s x with
        | some v =>
          simp only [pure_bind]
          exact ih v s hs
        | none =>
          simp only [bind_assoc, pure_bind]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _
            (measurableSet_singleton True) fun v _ => ?_
          rw [QueryCache.cacheQuery_comm s (Ne.symm hxt) u v]
          exact ih v (s.cacheQuery x v)
            (by rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxt)]; exact hs)

end roSim
