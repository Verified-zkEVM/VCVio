/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Reading a lazy random-oracle run off its cache

The cache a `QueryImpl.withCaching` run leaves behind (for `OracleSpec.randomOracle`, the lazily
sampled table) is a partial answer function.  `QueryCache.toPartialImpl` reads it as a
`QueryImpl spec Option`: simulating a computation through it returns `some a` exactly when every
query the computation makes is settled in the cache, and then `a` is the answer those entries
force.  This is the interface between a probabilistic run and a deterministic re-reading of it:
the final cache of a cached run extends the initial one
(`QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching`) and replays the run's own output
(`QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching`), a successful
reading survives cache extension (`QueryCache.simulateQ_toPartialImpl_mono`), and it fixes the
value of every total answer function agreeing with the cache
(`QueryCache.evalWithAnswerFn_eq_of_agreesWithFn`).  The cache of a run that also answers
uniform queries through `unifFwdImpl` only grows
(`OracleComp.le_snd_of_mem_support_run_unifFwdImpl_add_withCaching`).
-/

public section

open OracleComp OracleSpec

universe u v

namespace OracleSpec.QueryCache

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u}

/-- A cache read as a partial oracle: a cached query is answered from the cache and an uncached
one fails. -/
@[expose] def toPartialImpl (cache : spec.QueryCache) : QueryImpl spec Option := cache.toFn

@[simp] lemma toPartialImpl_apply (cache : spec.QueryCache) (t : spec.Domain) :
    cache.toPartialImpl t = cache t := rfl

/-- A partial reading that succeeds still succeeds, with the same value, from any larger
cache. -/
theorem simulateQ_toPartialImpl_mono {c c' : spec.QueryCache} (h : c ≤ c')
    (oa : OracleComp spec α) {a : α} (ha : simulateQ c.toPartialImpl oa = some a) :
    simulateQ c'.toPartialImpl oa = some a := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ha
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at ha ⊢
    obtain ⟨u, hu, ha⟩ := Option.bind_eq_some_iff.mp ha
    rw [toPartialImpl_apply, h hu]
    exact ih u ha

/-- A successful partial reading determines the value of every total answer function agreeing
with the cache. -/
theorem evalWithAnswerFn_eq_of_agreesWithFn {cache : spec.QueryCache} {f : QueryImpl spec Id}
    (hf : cache.AgreesWithFn f) (oa : OracleComp spec α) {a : α}
    (ha : simulateQ cache.toPartialImpl oa = some a) : evalWithAnswerFn f oa = a := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact Option.some.inj ha
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at ha
    obtain ⟨u, hu, ha⟩ := Option.bind_eq_some_iff.mp ha
    unfold evalWithAnswerFn at ih ⊢
    rw [simulateQ_bind, simulateQ_spec_query, hf hu]
    exact ih u ha

end OracleSpec.QueryCache

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι} {m : Type u → Type v} [Monad m]
  [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] {α : Type u}

/-- A cached step settles its query at the value it returns. -/
lemma snd_apply_of_mem_support_run_withCaching (so : QueryImpl spec m) {t : spec.Domain}
    {cache : spec.QueryCache} {z : spec.Range t × spec.QueryCache}
    (hz : z ∈ support ((so.withCaching t).run cache)) : z.2 t = some z.1 := by
  cases ht : cache t with
  | some u =>
    rw [withCaching_run_some so ht, support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ ht
  | none =>
    rw [withCaching_run_none so ht, support_map] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact QueryCache.cacheQuery_self cache t v

/-- The final cache of a cached run extends the initial one. -/
theorem le_snd_of_mem_support_run_simulateQ_withCaching (so : QueryImpl spec m)
    (oa : OracleComp spec α) {cache : spec.QueryCache} {z : α × spec.QueryCache}
    (hz : z ∈ support ((simulateQ so.withCaching oa).run cache)) : cache ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ le_rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, c₁⟩, h₁, h₂⟩ := hz
    exact (withCaching_cache_le so t cache _ h₁).trans (ih u h₂)

/-- The final cache of a cached run, read as a partial oracle, replays the run's output. -/
theorem simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching (so : QueryImpl spec m)
    (oa : OracleComp spec α) {cache : spec.QueryCache} {z : α × spec.QueryCache}
    (hz : z ∈ support ((simulateQ so.withCaching oa).run cache)) :
    simulateQ z.2.toPartialImpl oa = some z.1 := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, c₁⟩, h₁, h₂⟩ := hz
    rw [simulateQ_bind, simulateQ_spec_query, QueryCache.toPartialImpl_apply,
      le_snd_of_mem_support_run_simulateQ_withCaching so (k u) h₂
        (snd_apply_of_mem_support_run_withCaching so h₁)]
    exact ih u h₂

end QueryImpl

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}

/-- Running a computation that draws private randomness through `unifFwdImpl` and answers `spec`
through a cached oracle only extends the cache. -/
theorem le_snd_of_mem_support_run_unifFwdImpl_add_withCaching (so : QueryImpl spec ProbComp)
    (oa : OracleComp (unifSpec + spec) α) {cache : spec.QueryCache}
    {z : α × spec.QueryCache}
    (hz : z ∈ support ((simulateQ (unifFwdImpl spec + so.withCaching) oa).run cache)) :
    cache ≤ z.2 :=
  simulateQ_run_preservesInv _ (cache ≤ ·)
    (QueryImpl.PreservesInv.add
      (fun t s hs z hz => by
        rw [unifFwdImpl, QueryImpl.liftTarget_apply, StateT.run_liftM, bind_pure_comp,
          support_map] at hz
        obtain ⟨_, _, rfl⟩ := hz
        exact hs)
      (fun t s hs z hz => hs.trans (QueryImpl.withCaching_cache_le so t s z hz)))
    oa cache le_rfl z hz

end OracleComp
