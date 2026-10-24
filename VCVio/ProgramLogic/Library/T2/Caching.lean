/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.ProgramLogic.Library.T1.RunNF

/-!
# Specifications for caching handlers

Program-logic specifications for `QueryImpl.withCaching` and `cachingOracle`, under the
necessary reading of `OracleComp` (`open scoped OracleComp.Necessary`) for the `OracleComp`-based
statements.

* *Cache updates.* `QueryCache.cacheQuery` facts that caching proofs re-derive: re-caching a
  stored answer is the identity (`cacheQuery_eq_self_of_eq_some`), overwriting is idempotent
  (`cacheQuery_cacheQuery_self`), and when a cache only grows (`le_cacheQuery_iff`,
  `cacheQuery_le_of_le`).
* *One query.* `cachingOracle_wp` is the monotone-frame weakest precondition
  `fun c => ∀ v c', c ≤ c' → c' t = some v → post v c'`, registered at `spec high`;
  `cachingOracle_wp_cacheQuery` is the exact one, `fun c => ∀ v, (c t = none ∨ c t = some v) →
  post v (c.cacheQuery t v)`: a hit re-caches the stored answer, which leaves the cache unchanged.
  Both have one branch per query, so `vcgen` does not split on hits and misses. Pass the exact
  rule explicitly (`vcgen [cachingOracle_wp_cacheQuery]`) to override the frame.
* *Any base.* `withCaching_wp_frame` is the frame of `so.withCaching` for any `OracleComp`-based
  `so`. `withCaching_wp` (`spec low`) reads `so.withCaching` through the weakest precondition of
  the underlying handler for any `WPMonad` base and assertion language; its precondition is a
  `match` on the cache, at which `vcgen` stops, so `split` it and call `vcgen` again.
* *Repeated queries.* A second caching query at the same input is a hit, for any base monad
  (`withCaching_bind_withCaching_self`, `simulateQ_withCaching_query_bind_query_self`).
* *Whole runs.* Every `OracleComp`-based caching handler, including `cachingOracle` and
  `randomOracle`, is `QueryImpl.MonotoneState` for the cache order (`monotoneState_withCaching`),
  so T1's frame `Spec.simulateQ_monotoneState` lets `vcgen` step over an opaque simulated program,
  and sums with other cache-monotone handlers inherit it. `simulateQ_withCaching_cache_le` is the
  support form.
* *Support.* `QueryImpl.mem_support_withCaching_run_iff` and `cachingOracle.mem_support_run_iff`
  split a reachable step into its hit and miss cases. They and the hit/miss run equations are
  members of T1's `simulateQ_nf` simp set.
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary

universe u v w w' u' v'

namespace OracleSpec.QueryCache

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, v} ι}

/-- Caching the answer already stored at `t` leaves the cache unchanged. -/
theorem cacheQuery_eq_self_of_eq_some {c : spec.QueryCache} {t : spec.Domain} {u : spec.Range t}
    (h : c t = some u) : c.cacheQuery t u = c := by
  refine QueryCache.ext fun t' => ?_
  rcases eq_or_ne t' t with rfl | ht
  · rw [cacheQuery_self, h]
  · exact cacheQuery_of_ne c u ht

/-- Caching twice at the same input keeps only the second answer. -/
@[simp, grind =]
theorem cacheQuery_cacheQuery_self (c : spec.QueryCache) (t : spec.Domain) (u u' : spec.Range t) :
    (c.cacheQuery t u).cacheQuery t u' = c.cacheQuery t u' := by
  refine QueryCache.ext fun t' => ?_
  rcases eq_or_ne t' t with rfl | ht
  · rw [cacheQuery_self, cacheQuery_self]
  · rw [cacheQuery_of_ne _ _ ht, cacheQuery_of_ne _ _ ht, cacheQuery_of_ne _ _ ht]

/-- Caching `u` at `t` extends the cache exactly when `t` is uncached or already holds `u`. -/
theorem le_cacheQuery_iff {c : spec.QueryCache} {t : spec.Domain} {u : spec.Range t} :
    c ≤ c.cacheQuery t u ↔ c t = none ∨ c t = some u := by
  refine ⟨fun h => ?_, ?_⟩
  · cases ht : c t with
    | none => exact Or.inl rfl
    | some u' => exact Or.inr ((h ht).symm.trans (cacheQuery_self c t u))
  · rintro (ht | ht)
    · exact le_cacheQuery c ht
    · rw [cacheQuery_eq_self_of_eq_some ht]

/-- A cache below `c'` stays below `c'` after caching an answer that `c'` already stores. -/
theorem cacheQuery_le_of_le {c c' : spec.QueryCache} {t : spec.Domain} {u : spec.Range t}
    (h : c ≤ c') (ht : c' t = some u) : c.cacheQuery t u ≤ c' := by
  intro t' u' h'
  rcases eq_or_ne t' t with rfl | hne
  · rw [cacheQuery_self] at h'
    exact h' ▸ ht
  · exact h (cacheQuery_of_ne c u hne ▸ h')

end OracleSpec.QueryCache

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

section anyBase

variable {m : Type u → Type v} [Monad m]

/-- On a cache hit, the answer of a caching step is the stored one. -/
@[simulateQ_nf]
theorem withCaching_run'_of_eq_some [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {c : spec.QueryCache} {u : spec.Range t} (h : c t = some u) :
    (so.withCaching t).run' c = pure u := by
  rw [StateT.run'_eq, withCaching_run_some so h, map_pure]

/-- On a cache miss, the answer of a caching step is the underlying handler's. -/
@[simulateQ_nf]
theorem withCaching_run'_of_eq_none [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {c : spec.QueryCache} (h : c t = none) :
    (so.withCaching t).run' c = so t := by
  rw [StateT.run'_eq, withCaching_run_none so h, Functor.map_map]
  exact id_map (so t)

/-- A repeated caching query at the same input is a hit: it returns the first answer. -/
theorem withCaching_bind_withCaching_self [LawfulMonad m] {β : Type u} (so : QueryImpl spec m)
    (t : spec.Domain) (f : spec.Range t → spec.Range t → StateT spec.QueryCache m β) :
    (so.withCaching t >>= fun a => so.withCaching t >>= f a) =
      so.withCaching t >>= fun a => f a a := by
  refine StateT.ext fun c => ?_
  cases h : c t with
  | some u => simp only [StateT.run_bind, withCaching_run_some so h, pure_bind]
  | none =>
    simp only [StateT.run_bind, withCaching_run_none so h, bind_map_left]
    exact bind_congr fun u => by
      rw [withCaching_run_some so (QueryCache.cacheQuery_self c t u), pure_bind]

/-- A simulated program that queries an input twice in a row sees the same answer twice under a
caching handler. -/
theorem simulateQ_withCaching_query_bind_query_self [LawfulMonad m] {β : Type u}
    (so : QueryImpl spec m) (t : spec.Domain)
    (f : spec.Range t → spec.Range t → OracleComp spec β) :
    simulateQ so.withCaching ((spec.query t : OracleComp spec _) >>= fun a =>
        (spec.query t : OracleComp spec _) >>= f a) =
      simulateQ so.withCaching ((spec.query t : OracleComp spec _) >>= fun a => f a a) := by
  simp only [simulateQ_bind, simulateQ_spec_query]
  exact withCaching_bind_withCaching_self so t fun a b => simulateQ so.withCaching (f a b)

variable {Pred : Type w} {EPred : Type w'} [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
  [Std.WP.WPMonad m Pred EPred]

/-- A caching step under any reading: a hit returns the stored answer, a miss runs the
underlying handler and caches its answer. -/
@[spec low]
theorem withCaching_wp (so : QueryImpl spec m) (t : spec.Domain)
    (post : spec.Range t → spec.QueryCache → Pred) (epost : EPred) :
    ⦃ fun c => match c t with
        | some u => post u c
        | none => wp (so t) (fun u => post u (c.cacheQuery t u)) epost ⦄
      (so.withCaching t) ⦃ post; epost ⦄ := by
  refine ⟨fun c => ?_⟩
  cases h : c t with
  | some u =>
    rw [StateT.wp_apply_eq, withCaching_run_some so h]
    exact WPMonad.pure_le_wp_pure (m := m) (u, c) (fun x => post x.1 x.2) epost
  | none =>
    rw [StateT.wp_apply_eq, withCaching_run_none so h]
    exact WPMonad.map_le_wp_map (m := m) (fun u => (u, c.cacheQuery t u)) (so t)
      (fun x => post x.1 x.2) epost

end anyBase

section oracleCompBase

variable {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}

/-- A reachable caching step is a hit returning the stored answer, or a miss returning a possible
answer of the underlying handler and caching it. -/
@[simulateQ_nf]
theorem mem_support_withCaching_run_iff (so : QueryImpl spec (OracleComp spec'))
    {t : spec.Domain} {c c' : spec.QueryCache} {v : spec.Range t} :
    (v, c') ∈ support ((so.withCaching t).run c) ↔
      (c t = some v ∧ c' = c) ∨ (c t = none ∧ v ∈ support (so t) ∧ c' = c.cacheQuery t v) := by
  cases h : c t with
  | some u =>
    rw [withCaching_run_some so h, support_pure]
    simp [eq_comm]
  | none =>
    rw [withCaching_run_none so h, support_map]
    simp [eq_comm]

/-- A caching step over `OracleComp` in monotone-frame form: the final cache extends the initial
one and stores the answer, which on a miss is a possible answer of the underlying handler. -/
@[spec]
theorem withCaching_wp_frame (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain)
    (post : spec.Range t → spec.QueryCache → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v c', c ≤ c' → c' t = some v → (c t = none → v ∈ support (so t)) →
        post v c' ⦄
      (so.withCaching t) ⦃ post; epost ⦄ := by
  refine (OracleComp.ProgramLogic.triple_stateT_iff_forall_mem_support _ _ _ _).2
    fun c h v c' hz => h v c' (withCaching_cache_le so t c _ hz)
      (withCaching_run_caches so t c _ hz) fun hc => ?_
  rcases mem_support_withCaching_run_iff so |>.1 hz with ⟨hc', -⟩ | ⟨-, hv, -⟩
  · exact absurd (hc.symm.trans hc') (by simp)
  · exact hv

/-- Every caching handler over `OracleComp` only grows its cache, so whole runs are framed by the
cache order. -/
instance monotoneState_withCaching (so : QueryImpl spec (OracleComp spec')) :
    so.withCaching.MonotoneState (· ≤ ·) :=
  .of_le fun t s z hz => withCaching_cache_le so t s z hz

/-- A run of any caching handler over `OracleComp` only grows its cache, whatever the program. -/
theorem simulateQ_withCaching_cache_le {α : Type u} (so : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) (c : spec.QueryCache) :
    ∀ z ∈ support ((simulateQ so.withCaching oa).run c), c ≤ z.2 :=
  fun _ hz => MonotoneState.rel_of_mem_support hz

end oracleCompBase

attribute [simulateQ_nf] withCaching_run_some withCaching_run_none

end QueryImpl

namespace cachingOracle

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- A reachable `cachingOracle` step is a hit returning the stored answer or a miss caching an
arbitrary answer. -/
@[simulateQ_nf high]
theorem mem_support_run_iff {t : spec.Domain} {c c' : spec.QueryCache} {v : spec.Range t} :
    (v, c') ∈ support ((cachingOracle t).run c) ↔
      (c t = some v ∧ c' = c) ∨ (c t = none ∧ c' = c.cacheQuery t v) := by
  rw [QueryImpl.mem_support_withCaching_run_iff]
  simp

/-- A reachable `cachingOracle` step ends in the cache `c.cacheQuery t v`, with `v` the stored
answer when `t` was cached. -/
theorem eq_cacheQuery_of_mem_support_run {t : spec.Domain} {c c' : spec.QueryCache}
    {v : spec.Range t} (h : (v, c') ∈ support ((cachingOracle t).run c)) :
    c' = c.cacheQuery t v ∧ (c t = none ∨ c t = some v) := by
  rcases mem_support_run_iff.1 h with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · exact ⟨(QueryCache.cacheQuery_eq_self_of_eq_some hc).symm, Or.inr hc⟩
  · exact ⟨rfl, Or.inl hc⟩

end cachingOracle

namespace OracleComp.ProgramLogic

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- One `cachingOracle` query in monotone-frame form: the final cache extends the initial one and
stores the answer. The default rule of `vcgen` for `cachingOracle`. -/
@[spec high]
theorem cachingOracle_wp (t : spec.Domain) (post : spec.Range t → spec.QueryCache → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v c', c ≤ c' → c' t = some v → post v c' ⦄
      (spec.cachingOracle t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h v c' hz =>
    h v c' (QueryImpl.withCaching_cache_le _ t c _ hz) (QueryImpl.withCaching_run_caches _ t c _ hz)

/-- One `cachingOracle` query, exactly: the answer is the stored one on a hit, and the final cache
is the initial one with the answer cached. -/
theorem cachingOracle_wp_cacheQuery (t : spec.Domain)
    (post : spec.Range t → spec.QueryCache → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v, (c t = none ∨ c t = some v) → post v (c.cacheQuery t v) ⦄
      (spec.cachingOracle t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h v c' hz => by
    obtain ⟨rfl, hv⟩ := cachingOracle.eq_cacheQuery_of_mem_support_run hz
    exact h v hv

end OracleComp.ProgramLogic
