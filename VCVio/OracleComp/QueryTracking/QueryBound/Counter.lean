/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

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
bounds any natural-number cost of the state that grows by at most one on each `p`-query.
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

end OracleComp
