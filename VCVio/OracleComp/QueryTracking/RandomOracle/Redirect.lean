/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Reading a cache through a query redirect

A *redirect* of an oracle signature `spec` into `spec'` is an implementation
`ρ : QueryImpl spec (OracleComp spec')` that answers each query by a program over `spec'`;
`simulateQ ρ` rewrites a program by replacing each of its queries with that program. When
`spec' = spec` and an implementation answers every `ρ t` as it answers `t` itself, it cannot tell a
program from its redirected form (`QueryImpl.simulateQ_simulateQ_eq_of_apply`): this is the
situation of two typed queries that share one encoding in a single underlying oracle, when the
redirect sends one to the other.

`QueryCache.viewBy c ρ` is a cache `c` of `spec'` read through `ρ`: its entry at `t` is the
partial replay of `ρ t` on `c` (`QueryCache.toPartialImpl`). Reading a program on the view is
reading the redirected program on `c` (`QueryCache.simulateQ_viewBy_toPartialImpl`), and the view
is monotone in the cache (`QueryCache.viewBy_mono`). For a redirect of `spec` into itself, the
view agrees with `c` wherever `ρ` passes the query on (`QueryCache.viewBy_apply_of_eq_query`), so
it extends the restriction `QueryCache.filter p c` of `c` to any set `p` of such points
(`QueryCache.filter_le_viewBy`).

## Replays on a restriction

A replay whose every query satisfies `p` reads `filter p c` as `c`
(`QueryCache.simulateQ_toPartialImpl_filter_eq_of_allQueriesSatisfy`). A replay settled on `c`
that settles on the restriction to `p` of a larger cache settles, with that value, on
`filter p c` (`QueryCache.simulateQ_toPartialImpl_filter_of_le`). A `spec₁`-only program
run in the random oracle model over `spec₁ + spec₂`, whose replay settles on the restriction to
`p` of the `spec₁` part of its final cache, adds to that part only points of `p`
(`OracleComp.forall_of_simulateQ_toPartialImpl_filter_fst_of_mem_support_run_romImpl`).
-/

public section

open OracleComp OracleSpec

universe u v

namespace OracleSpec.QueryCache

section Filter

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- The restriction of `c` to the points satisfying `p`: the entries of `c` there, and no entry
elsewhere. -/
@[expose] def filter (p : spec.Domain → Prop) [DecidablePred p] (c : spec.QueryCache) :
    spec.QueryCache :=
  ofFn fun t => if p t then c t else none

/-- The entry of `filter p c` at `t` is that of `c` when `p t` holds and unset otherwise. -/
@[simp] lemma filter_apply (p : spec.Domain → Prop) [DecidablePred p] (c : spec.QueryCache)
    (t : spec.Domain) : filter p c t = if p t then c t else none := rfl

/-- The restriction of a cache lies below the cache. -/
theorem filter_le (p : spec.Domain → Prop) [DecidablePred p] (c : spec.QueryCache) :
    filter p c ≤ c := fun t u ht => by
  rw [filter_apply] at ht
  split_ifs at ht
  exact ht

/-- A cache below `c` whose entries all lie at points satisfying `p` is below the restriction of
`c` to `p`. -/
theorem le_filter {c₀ c : spec.QueryCache} (h : c₀ ≤ c) {p : spec.Domain → Prop}
    [DecidablePred p] (hp : ∀ t, (c₀ t).isSome → p t) : c₀ ≤ filter p c := fun t u ht => by
  simpa [hp t (by simp [ht])] using h ht

end Filter

section FilterReplay

variable {ι : Type} {spec : OracleSpec ι} {α : Type} {p : spec.Domain → Prop} [DecidablePred p]

/-- A replay whose every query satisfies `p` reads the restriction of a cache to `p` as the cache
itself. -/
theorem simulateQ_toPartialImpl_filter_eq_of_allQueriesSatisfy (c : spec.QueryCache)
    {oa : OracleComp spec α} (h : oa.AllQueriesSatisfy p) :
    simulateQ (filter p c).toPartialImpl oa = simulateQ c.toPartialImpl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, toPartialImpl_apply, filter_apply, h.1,
      ↓reduceIte]
    exact congrArg _ (funext fun u => ih u (h.2 u))

/-- A replay settled on `c` and settled on the restriction to `p` of a larger cache is settled,
with the latter value, on the restriction of `c` to `p`. -/
theorem simulateQ_toPartialImpl_filter_of_le {c c' : spec.QueryCache} (h : c ≤ c')
    {oa : OracleComp spec α} {a b : α} (ha : simulateQ c.toPartialImpl oa = some a)
    (hb : simulateQ (filter p c').toPartialImpl oa = some b) :
    simulateQ (filter p c).toPartialImpl oa = some b := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact hb
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at ha hb ⊢
    obtain ⟨u, hu, ha⟩ := Option.bind_eq_some_iff.mp ha
    obtain ⟨u', hu', hb⟩ := Option.bind_eq_some_iff.mp hb
    rw [toPartialImpl_apply, filter_apply] at hu'
    split_ifs at hu' with hp
    obtain rfl : u' = u := Option.some.inj (hu'.symm.trans (h hu))
    rw [toPartialImpl_apply] at hu
    simp only [toPartialImpl_apply, filter_apply, hp, ↓reduceIte, hu]
    exact ih u' ha hb

end FilterReplay

section ViewBy

variable {ι ι' : Type u} {spec : OracleSpec.{u, u} ι} {spec' : OracleSpec.{u, u} ι'}
  {α : Type u}

/-- The cache `c` of `spec'` read through the redirect `ρ`: its entry at `t` is the partial
replay of `ρ t` on `c`, unset when that replay reads an unset entry. -/
@[expose] def viewBy (c : spec'.QueryCache) (ρ : QueryImpl spec (OracleComp spec')) :
    spec.QueryCache :=
  ofFn (c.toPartialImpl ∘ₛ ρ)

/-- The entry of the view at `t` is the partial replay of `ρ t` on the cache. -/
@[simp] lemma viewBy_apply (c : spec'.QueryCache) (ρ : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) : c.viewBy ρ t = simulateQ c.toPartialImpl (ρ t) := rfl

/-- Reading a program on the view of `c` through `ρ` is reading the program rewritten by `ρ` on
`c`. -/
theorem simulateQ_viewBy_toPartialImpl (c : spec'.QueryCache)
    (ρ : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α) :
    simulateQ (c.viewBy ρ).toPartialImpl oa = simulateQ c.toPartialImpl (simulateQ ρ oa) :=
  QueryImpl.simulateQ_compose _ _ oa

/-- The view through a fixed redirect is monotone in the cache. -/
theorem viewBy_mono {c c' : spec'.QueryCache} (h : c ≤ c')
    (ρ : QueryImpl spec (OracleComp spec')) : c.viewBy ρ ≤ c'.viewBy ρ :=
  fun t _ ht => simulateQ_toPartialImpl_mono h (ρ t) ht

/-- At a point that `ρ` passes on unchanged, the view of `c` through `ρ` is the entry of `c`. -/
theorem viewBy_apply_of_eq_query {ρ : QueryImpl spec (OracleComp spec)} {t : spec.Domain}
    (ht : ρ t = query t) (c : spec.QueryCache) : c.viewBy ρ t = c t := by
  rw [viewBy_apply, ht]
  simp

/-- The view of `c` through `ρ` extends the restriction of `c` to points that `ρ` passes on
unchanged. -/
theorem filter_le_viewBy (c : spec.QueryCache) {ρ : QueryImpl spec (OracleComp spec)}
    {p : spec.Domain → Prop} [DecidablePred p] (hρ : ∀ t, p t → ρ t = query t) :
    filter p c ≤ c.viewBy ρ := fun t u ht => by
  rw [filter_apply] at ht
  split_ifs at ht with hp
  rwa [viewBy_apply_of_eq_query (hρ t hp)]

end ViewBy

end OracleSpec.QueryCache

namespace OracleComp

variable {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂] {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} [∀ t, SampleableType ((spec₁ + spec₂).Range t)] {α : Type}

/-- **A run whose replay settles on a restriction adds only points of it.** A `spec₁`-only program
issued through its query capability and run in the random oracle model over `spec₁ + spec₂`, whose
replay settles on the restriction to `p` of the `spec₁` part of its final cache, adds to the
`spec₁` part of the cache only points satisfying `p`. -/
theorem forall_of_simulateQ_toPartialImpl_filter_fst_of_mem_support_run_romImpl
    (oa : OracleComp spec₁ α) {p : ι₁ → Prop} [DecidablePred p]
    {cache : (spec₁ + spec₂).QueryCache} {z : α × (spec₁ + spec₂).QueryCache}
    (hz : z ∈ support ((simulateQ (spec₁ + spec₂).romImpl (simulateQ (HasQuery.toQueryImpl
      (spec := spec₁) (m := OracleComp (unifSpec + (spec₁ + spec₂)))) oa)).run cache))
    {b : α} (hb : simulateQ (QueryCache.filter p z.2.fst).toPartialImpl oa = some b) :
    ∀ t, cache (.inl t) = none → (z.2 (.inl t)).isSome → p t := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x =>
    rw [simulateQ_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    intro t h h'
    simp [h] at h'
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨⟨u, c₁⟩, h₁, h₂⟩ := hz
    rw [show (HasQuery.toQueryImpl (spec := spec₁)
        (m := OracleComp (unifSpec + (spec₁ + spec₂))) t) =
        liftM ((unifSpec + (spec₁ + spec₂)).query (.inr (.inl t))) from rfl,
      simulateQ_spec_query] at h₁
    have hc₁ : c₁ (.inl t) = some u :=
      QueryImpl.withCaching_run_caches (uniformSampleImpl (spec := spec₁ + spec₂)) (.inl t)
        cache (u, c₁) h₁
    have hle := le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ h₂
    rw [simulateQ_bind, simulateQ_spec_query] at hb
    obtain ⟨u', hu', hb⟩ := Option.bind_eq_some_iff.mp hb
    rw [QueryCache.toPartialImpl_apply, QueryCache.filter_apply] at hu'
    split_ifs at hu' with hp
    rw [QueryCache.fst_apply, hle hc₁] at hu'
    obtain rfl : u' = u := (Option.some.inj hu').symm
    intro t' ht' hz'
    by_cases ht : t' = t
    · exact ht ▸ hp
    · refine ih _ h₂ hb t' ?_ hz'
      have hiff := QueryImpl.withCaching_run_isSome_apply_iff
        (uniformSampleImpl (spec := spec₁ + spec₂)) h₁ (.inl t')
      cases hc : c₁ (.inl t') with
      | none => rfl
      | some v =>
        have := hiff.1 (by simp [hc])
        simp [ht', ht] at this

end OracleComp
