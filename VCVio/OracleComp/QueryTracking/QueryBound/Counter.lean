/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Query bounds as pathwise counters

`IsQueryBoundP oa p q` is a syntactic statement about the computation `oa`: along every
response path it makes at most `q` queries satisfying `p`. This file reads it as a statement
about runs. Extend any stateful handler with a natural-number counter
(`QueryImpl.extendState`) that grows by at most one on a `p`-query and not at all otherwise;
then on every output in the support of the extended run, the counter has grown by at most `q`
(`IsQueryBoundP.cnt_le_of_mem_support_run_extendState`). The handler itself is arbitrary: it
may answer queries from a cache, a tape or any other state, and may make its own queries.
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
  induction oa using OracleComp.inductionOn generalizing q s c z with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_query_bind, StateT.run_bind] at hz
    simp only [OracleQuery.input_query, monadLift_self, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    rw [QueryImpl.extendState_apply, support_bind] at hw
    simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨v, -, rfl⟩ := hw
    have hrest := ih v.1 (h.2 v.1) hz
    have hstep := haux t s v.1 v.2 c
    split_ifs at hrest hstep with hpt
    · have := h.1.resolve_left (not_not.mpr hpt)
      omega
    · omega

end OracleComp
