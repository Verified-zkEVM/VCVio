/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.CachingLoggingOracle
public import VCVio.ProgramLogic.Library.T2.Caching

/-!
# Specifications for the caching-and-logging handlers

Specifications for `QueryImpl.withCachingLogging` and `cachingLoggingOracle`, which keep a cache
and a query log in one `StateT (QueryCache spec × QueryLog spec)` layer, under the necessary
reading of `OracleComp` (`open scoped OracleComp.Necessary`).

* *One query.* `cachingLoggingOracle_wp` (`spec high`) is the monotone frame of the cache with
  the log extended by the query and its answer; `cachingLoggingOracle_wp_cacheQuery` is exact;
  `withCachingLogging_wp_frame` covers any `OracleComp`-based fallback handler.
* *Whole runs.* Both handlers are `QueryImpl.MonotoneState` for the product order "the cache
  grows and the log is extended", so T1's frame steps over an opaque run.
* *Invariants.* The two coherence invariants of the Fiat-Shamir and forking proofs hold along
  every run: every logged answer is the cached answer (`simulateQ_withCachingLogging_log_cached`),
  and every cached answer is logged (`simulateQ_withCachingLogging_cache_logged`). Both hold of
  the empty state, so of every run started from it.
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary

universe u u' v'

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι} {ι' : Type u'}
  {spec' : OracleSpec.{u', v'} ι'}

/-- A reachable caching-and-logging step is a hit, which logs the stored answer, or a miss,
which caches and logs a possible answer of the underlying handler. -/
@[simulateQ_nf]
theorem mem_support_withCachingLogging_run_iff (so : QueryImpl spec (OracleComp spec'))
    {t : spec.Domain} {s s' : spec.QueryCache × QueryLog spec} {v : spec.Range t} :
    (v, s') ∈ support ((so.withCachingLogging t).run s) ↔
      (s.1 t = some v ∧ s' = (s.1, s.2 ++ [⟨t, v⟩])) ∨
        (s.1 t = none ∧ v ∈ support (so t) ∧ s' = (s.1.cacheQuery t v, s.2 ++ [⟨t, v⟩])) := by
  rw [withCachingLogging_apply, StateT.run_mk]
  cases h : s.1 t with
  | some u =>
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
      reduceCtorEq, false_and, or_false]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | none => simp [eq_comm]

/-- A reachable caching-and-logging step grows the cache, stores the answer, and logs it. -/
theorem withCachingLogging_run_le (so : QueryImpl spec (OracleComp spec')) {t : spec.Domain}
    {s : spec.QueryCache × QueryLog spec} {z : spec.Range t × spec.QueryCache × QueryLog spec}
    (hz : z ∈ support ((so.withCachingLogging t).run s)) :
    s.1 ≤ z.2.1 ∧ z.2.1 t = some z.1 ∧ z.2.2 = s.2 ++ [⟨t, z.1⟩] := by
  obtain ⟨v, c', l'⟩ := z
  rcases (mem_support_withCachingLogging_run_iff so).1 hz with ⟨hc, h⟩ | ⟨hc, -, h⟩ <;>
    simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact ⟨le_rfl, hc, rfl⟩
  · exact ⟨QueryCache.le_cacheQuery _ hc, QueryCache.cacheQuery_self _ _ _, rfl⟩

/-- A caching-and-logging step over `OracleComp` in monotone-frame form: the cache grows and
stores the answer, which on a miss is a possible answer of the underlying handler, and the log
gains the query with its answer. -/
@[spec]
theorem withCachingLogging_wp_frame (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain)
    (post : spec.Range t → spec.QueryCache × QueryLog spec → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v c', s.1 ≤ c' → c' t = some v → (s.1 t = none → v ∈ support (so t)) →
        post v (c', s.2 ++ [⟨t, v⟩]) ⦄
      (so.withCachingLogging t) ⦃ post; epost ⦄ :=
  (OracleComp.ProgramLogic.triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases (mem_support_withCachingLogging_run_iff so).1 hz with ⟨hc, rfl⟩ | ⟨hc, hv, rfl⟩
    · exact h v s.1 le_rfl hc fun h' => by simp [hc] at h'
    · exact h v _ (QueryCache.le_cacheQuery _ hc) (QueryCache.cacheQuery_self _ _ _) fun _ => hv

/-- A caching-and-logging handler only grows its cache and extends its log. -/
instance monotoneState_withCachingLogging (so : QueryImpl spec (OracleComp spec')) :
    so.withCachingLogging.MonotoneState fun s s' => s.1 ≤ s'.1 ∧ s.2 <+: s'.2 where
  refl _ := ⟨le_rfl, List.prefix_refl _⟩
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  step _ _ _ hz := by
    obtain ⟨hle, -, hlog⟩ := withCachingLogging_run_le so hz
    exact ⟨hle, hlog ▸ List.prefix_append _ _⟩

/-- Along every run, every logged answer is the cached answer, if it was so initially. -/
theorem simulateQ_withCachingLogging_log_cached {α : Type u}
    (so : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α)
    {s : spec.QueryCache × QueryLog spec} (hs : ∀ e ∈ s.2, s.1 e.1 = some e.2) :
    ∀ z ∈ support ((simulateQ so.withCachingLogging oa).run s), ∀ e ∈ z.2.2, z.2.1 e.1 = some e.2 :=
  fun _ hz => OracleComp.inv_of_mem_support_simulateQ_run
    (Inv := fun s : spec.QueryCache × QueryLog spec => ∀ e ∈ s.2, s.1 e.1 = some e.2)
    (fun _ _ hs' _ hz' e he => by
      obtain ⟨hle, hc, hlog⟩ := withCachingLogging_run_le so hz'
      rw [hlog, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hle (hs' e he)
      · exact hc) hs hz

/-- Along every run, every cached answer is logged, if it was so initially. -/
theorem simulateQ_withCachingLogging_cache_logged {α : Type u}
    (so : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α)
    {s : spec.QueryCache × QueryLog spec} (hs : ∀ t u, s.1 t = some u → ⟨t, u⟩ ∈ s.2) :
    ∀ z ∈ support ((simulateQ so.withCachingLogging oa).run s),
      ∀ t u, z.2.1 t = some u → ⟨t, u⟩ ∈ z.2.2 :=
  fun _ hz => OracleComp.inv_of_mem_support_simulateQ_run
    (Inv := fun s : spec.QueryCache × QueryLog spec => ∀ t u, s.1 t = some u → ⟨t, u⟩ ∈ s.2)
    (fun t' s' hs' z hz' t u hu => by
      obtain ⟨v, c', l'⟩ := z
      rcases (mem_support_withCachingLogging_run_iff so).1 hz' with ⟨-, h⟩ | ⟨-, -, h⟩ <;>
        simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp only at hu ⊢
      · exact List.mem_append_left _ (hs' t u hu)
      · rcases eq_or_ne t t' with rfl | hne
        · rw [QueryCache.cacheQuery_self] at hu
          cases hu
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [QueryCache.cacheQuery_of_ne _ _ hne] at hu
          exact List.mem_append_left _ (hs' t u hu)) hs hz

end QueryImpl

namespace cachingLoggingOracle

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- A reachable `cachingLoggingOracle` step is a hit logging the stored answer, or a miss caching
and logging an arbitrary answer. -/
@[simulateQ_nf]
theorem mem_support_run_iff {t : spec.Domain} {s s' : spec.QueryCache × QueryLog spec}
    {v : spec.Range t} :
    (v, s') ∈ support ((cachingLoggingOracle t).run s) ↔
      (s.1 t = some v ∧ s' = (s.1, s.2 ++ [⟨t, v⟩])) ∨
        (s.1 t = none ∧ s' = (s.1.cacheQuery t v, s.2 ++ [⟨t, v⟩])) := by
  rw [cachingLoggingOracle, QueryImpl.mem_support_withCachingLogging_run_iff]
  simp

/-- `cachingLoggingOracle` only grows its cache and extends its log. -/
instance monotoneState :
    (spec.cachingLoggingOracle).MonotoneState fun s s' => s.1 ≤ s'.1 ∧ s.2 <+: s'.2 :=
  QueryImpl.monotoneState_withCachingLogging _

/-- Along every `cachingLoggingOracle` run from the empty state, every logged answer is cached
and every cached answer is logged. -/
theorem log_cached_and_cache_logged_of_mem_support {α : Type u} {oa : OracleComp spec α}
    {z : α × spec.QueryCache × QueryLog spec}
    (hz : z ∈ support ((simulateQ spec.cachingLoggingOracle oa).run (∅, []))) :
    (∀ e ∈ z.2.2, z.2.1 e.1 = some e.2) ∧ ∀ t u, z.2.1 t = some u → ⟨t, u⟩ ∈ z.2.2 :=
  ⟨QueryImpl.simulateQ_withCachingLogging_log_cached _ oa (by simp) z hz,
    QueryImpl.simulateQ_withCachingLogging_cache_logged _ oa (by simp [QueryCache.empty_apply])
      z hz⟩

end cachingLoggingOracle

namespace OracleComp.ProgramLogic

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- One `cachingLoggingOracle` query in monotone-frame form: the cache grows and stores the
answer, and the log gains the query with its answer. The default rule of `vcgen`. -/
@[spec high]
theorem cachingLoggingOracle_wp (t : spec.Domain)
    (post : spec.Range t → spec.QueryCache × QueryLog spec → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v c', s.1 ≤ c' → c' t = some v → post v (c', s.2 ++ [⟨t, v⟩]) ⦄
      (spec.cachingLoggingOracle t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases cachingLoggingOracle.mem_support_run_iff.1 hz with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · exact h v s.1 le_rfl hc
    · exact h v _ (QueryCache.le_cacheQuery _ hc) (QueryCache.cacheQuery_self _ _ _)

/-- One `cachingLoggingOracle` query, exactly: the final cache is the initial one with the answer
cached, the stored one on a hit, and the log gains the query with its answer. -/
theorem cachingLoggingOracle_wp_cacheQuery (t : spec.Domain)
    (post : spec.Range t → spec.QueryCache × QueryLog spec → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v, (s.1 t = none ∨ s.1 t = some v) →
        post v (s.1.cacheQuery t v, s.2 ++ [⟨t, v⟩]) ⦄
      (spec.cachingLoggingOracle t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases cachingLoggingOracle.mem_support_run_iff.1 hz with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h v (Or.inr hc)
    · exact h v (Or.inl hc)

end OracleComp.ProgramLogic
