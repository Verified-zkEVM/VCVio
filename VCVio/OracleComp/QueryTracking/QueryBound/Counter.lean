/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Query bounds as pathwise counters

`IsQueryBoundP oa p q` is a syntactic statement about the computation `oa`: along every
response path it makes at most `q` queries satisfying `p`. This file reads it as a statement
about runs. Extend any stateful handler with a natural-number counter
(`QueryImpl.extendState`) that grows by at most one on a `p`-query and not at all otherwise;
then on every output in the support of the extended run, the counter has grown by at most `q`
(`IsQueryBoundP.cnt_le_of_mem_support_run_extendState`). The handler itself is arbitrary: it
may answer queries from a cache, a tape or any other state, and may make its own queries. The
counter is the cost `Prod.snd` of `IsQueryBoundP.cost_le_of_mem_support_run_simulateQ`, which
bounds any natural-number cost of the state that grows by at most one on a `p`-query and not at
all on any other query; `IsQueryBoundP.resource_le_add_of_mem_support_run_simulateQ` is the same
bound for an `ℕ∞`-valued resource.

A handler that *caches only its query's point* (`QueryImpl.CachesOnlyQueryPoint`) adds to a
cache read off its state, on each step, at most the point of that step's query. If `p` holds at
every query whose point lies in a set `D`, the cache of every run gains at most as many points of
`D` as the run makes `p`-queries
(`QueryImpl.CachesOnlyQueryPoint.encard_inter_le_add_of_mem_support_simulateQ`).
-/

public section

open OracleSpec

namespace OracleComp

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α : Type}

/-- Run a `p`-bounded-by-`q` computation under a stateful handler extended by a counter that
grows by at most one on each `p`-query and does not grow on any other query. On every output of
the run, the counter exceeds its initial value by at most `q`. -/
theorem IsQueryBoundP.cnt_le_of_mem_support_run_extendState {σ : Type}
    (so : QueryImpl spec (StateT σ (OracleComp spec'))) {p : ι → Prop} [DecidablePred p]
    {aux : (t : spec.Domain) → σ → spec.Range t → σ → ℕ → ℕ}
    (haux : ∀ t s u s' c, aux t s u s' c ≤ c + if p t then 1 else 0)
    {oa : OracleComp spec α} {q : ℕ} (h : IsQueryBoundP oa p q) {s : σ} {c : ℕ}
    {z : α × σ × ℕ} (hz : z ∈ support ((simulateQ (so.extendState aux) oa).run (s, c))) :
    z.2.2 ≤ c + q := by
  have hstep (t : spec.Domain) (st : σ × ℕ) (w : spec.Range t × σ × ℕ)
      (hw : w ∈ support ((so.extendState aux t).run st)) :
      w.2.2 ≤ st.2 + if p t then 1 else 0 := by
    rw [QueryImpl.extendState_apply, mem_support_bind_iff] at hw
    obtain ⟨v, -, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    exact hw ▸ haux t st.1 v.1 v.2 st.2
  exact h.cost_le_of_mem_support_run_simulateQ Prod.snd
    (fun t hp st w hw ↦ by simpa only [hp, ↓reduceIte] using hstep t st w hw)
    (fun t hp st w hw ↦ by simpa only [hp, ↓reduceIte, add_zero] using hstep t st w hw) (s, c) z hz

/-- Run a `p`-bounded-by-`n` computation under a stateful handler, and let `f` be an
`ℕ∞`-valued resource of the state that grows by at most one on each `p`-query and does not grow
on any other query. On every output of the run, the resource exceeds its initial value by at
most `n`. -/
theorem IsQueryBoundP.resource_le_add_of_mem_support_run_simulateQ {σ : Type}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {p : ι → Prop} [DecidablePred p]
    (f : σ → ℕ∞)
    (hstep : ∀ t s, ∀ w ∈ support ((impl t).run s), f w.2 ≤ f s + if p t then 1 else 0)
    {oa : OracleComp spec α} {n : ℕ} (h : IsQueryBoundP oa p n) {s : σ} {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run s)) :
    f z.2 ≤ f s + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_self_add
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    refine (ih w.1 (h.2 w.1) hz).trans ?_
    by_cases hpt : p t
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (h.1.resolve_left (not_not_intro hpt)).ne'
      have hw' := hstep t s w hw
      simp only [hpt, ↓reduceIte, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hw' ⊢
      calc f w.2 + m ≤ f s + 1 + m := add_le_add hw' le_rfl
        _ = f s + (m + 1) := by rw [add_assoc, add_comm 1]
    · have hw' := hstep t s w hw
      simp only [hpt, ↓reduceIte, add_zero] at hw' ⊢
      exact add_le_add hw' le_rfl

end OracleComp

namespace QueryImpl

open OracleComp

variable {ι ι' κ : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ : Type}

/-- A stateful handler *caches only its query's point*: the cache `cached s ⊆ κ` read off its
state grows, on each step, by at most the point `pt t` of the step's query, and by nothing on a
query with no point. -/
@[expose] def CachesOnlyQueryPoint (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (cached : σ → Set κ) (pt : spec.Domain → Option κ) : Prop :=
  ∀ t s, ∀ w ∈ support ((impl t).run s), cached w.2 ⊆ cached s ∪ {k | pt t = some k}

namespace CachesOnlyQueryPoint

variable {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {cached : σ → Set κ}
  {pt : spec.Domain → Option κ}

/-- A step of a handler caching only its query's point caches at most one new point of a set
`D`, and none unless its query is one of a predicate `p` holding at every query whose point
lies in `D`. -/
theorem encard_inter_le_add_of_mem_support (himpl : impl.CachesOnlyQueryPoint cached pt)
    {D : Set κ} {p : spec.Domain → Prop} [DecidablePred p]
    (hp : ∀ t k, pt t = some k → k ∈ D → p t) {t : spec.Domain} {s : σ}
    {w : spec.Range t × σ} (hw : w ∈ support ((impl t).run s)) :
    (D ∩ cached w.2).encard ≤ (D ∩ cached s).encard + if p t then 1 else 0 := by
  have hsub : D ∩ cached w.2 ⊆ D ∩ cached s ∪ D ∩ {k | pt t = some k} := fun k ⟨hD, hk⟩ ↦
    (himpl t s w hw hk).imp (⟨hD, ·⟩) (⟨hD, ·⟩)
  refine (Set.encard_le_encard hsub).trans ((Set.encard_union_le _ _).trans ?_)
  by_cases hpt : p t
  · have hone : (D ∩ {k | pt t = some k}).encard ≤ 1 :=
      Set.encard_le_one_iff.2 fun a b ha hb ↦ Option.some_injective _ (ha.2.symm.trans hb.2)
    simpa only [hpt, ↓reduceIte] using add_le_add le_rfl hone
  · have hemp : D ∩ {k | pt t = some k} = ∅ :=
      Set.eq_empty_of_forall_notMem fun k hk ↦ hpt (hp t k hk.2 hk.1)
    simp only [hpt, ↓reduceIte, hemp, Set.encard_empty, add_zero, le_refl]

/-- **Cached points are charged queries.** Run a `p`-bounded-by-`q` computation under a handler
caching only its query's point, where `p` holds at every query whose point lies in a set `D`. On
every output of the run, the cache holds at most `q` more points of `D` than it did initially. -/
theorem encard_inter_le_add_of_mem_support_simulateQ
    (himpl : impl.CachesOnlyQueryPoint cached pt) {D : Set κ} {p : spec.Domain → Prop}
    [DecidablePred p] (hp : ∀ t k, pt t = some k → k ∈ D → p t) {α : Type}
    {oa : OracleComp spec α} {q : ℕ} (h : IsQueryBoundP oa p q) {s : σ} {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run s)) :
    (D ∩ cached z.2).encard ≤ (D ∩ cached s).encard + q :=
  h.resource_le_add_of_mem_support_run_simulateQ (fun s ↦ (D ∩ cached s).encard)
    (fun _ _ _ hw ↦ himpl.encard_inter_le_add_of_mem_support hp hw) hz

end CachesOnlyQueryPoint

end QueryImpl
