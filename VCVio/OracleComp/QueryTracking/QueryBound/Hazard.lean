/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-!
# Bad events with a per-query hazard

A stateful handler whose bad event can only arise at charged queries, with a hazard that depends
on a counter of the state, makes the bad event unlikely in every computation with few charged
queries: the hazards of the charged steps add up. This is the adaptive form of the birthday bound,
where the draws that may collide are interleaved with arbitrary other queries and the number of
earlier draws is read from the state.

## Main statements

* `OracleComp.prEvent_simulateQ_run_le_sum_of_isQueryBoundP`: if a free step keeps the counter and
  never makes the state bad, and a charged step raises the counter by at most one and makes the
  state bad with probability at most `w` of the counter, for a monotone `w`, then a run with at most
  `q` charged queries from a good state ends bad with probability at most
  `∑ i < q, w (c + i)`, where `c` is the initial counter.
-/

public section

open OracleSpec ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **The hazard bound.** Let `impl` be a stateful handler with an invariant `inv`, a counter
`cnt` and a bad event `bad`. From a good state satisfying the invariant, suppose a step at an
uncharged query keeps the counter and leads to good states only, and a step at a charged query
raises the counter by at most one and leads to a bad state with probability at most `w` of the
counter, where `w` is monotone. Then a run of a computation with at most `q` charged queries from
such a state `s` ends in a bad state with probability at most `∑ i < q, w (cnt s + i)`. -/
theorem prEvent_simulateQ_run_le_sum_of_isQueryBoundP
    (impl : QueryImpl spec (StateT σ ProbComp)) (charged : ι → Prop) [DecidablePred charged]
    (cnt : σ → ℕ) (inv bad : σ → Prop) (w : ℕ → ℝ≥0∞) (hw : Monotone w)
    (hinv : QueryImpl.PreservesInv impl inv)
    (h_free : ∀ t s, ¬ charged t → inv s → ¬ bad s →
      ∀ z ∈ support ((impl t).run s), cnt z.2 = cnt s ∧ ¬ bad z.2)
    (h_cnt : ∀ t s, charged t → inv s → ¬ bad s →
      ∀ z ∈ support ((impl t).run s), cnt z.2 ≤ cnt s + 1)
    (h_charged : ∀ t s, charged t → inv s → ¬ bad s →
      Pr{let z ← (impl t).run s}[bad z.2] ≤ w (cnt s))
    {α : Type} (oa : OracleComp spec α) {q : ℕ} (hq : oa.IsQueryBoundP charged q) (s : σ)
    (hs : inv s) (hb : ¬ bad s) :
    Pr{let z ← (simulateQ impl oa).run s}[bad z.2] ≤ ∑ i ∈ Finset.range q, w (cnt s + i) := by
  induction oa using OracleComp.inductionOn generalizing q s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
      rw [mem_support_pure_iff] at hz
      exact hz ▸ hb]
    exact zero_le
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    obtain ⟨hvalid, hcont⟩ := hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases ht : charged t
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 :=
        Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.1 (hvalid.resolve_left (· ht)))
      simp only [ht, ↓reduceIte, Nat.add_sub_cancel] at hcont
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z => bad z.2) _
        (ε := ∑ i ∈ Finset.range q', w (cnt s + 1 + i)) fun z hz hbz => ?_).trans ?_
      · refine (ih z.1 (hcont z.1) z.2 (hinv t s hs z hz) hbz).trans
          (Finset.sum_le_sum fun i _ => hw ?_)
        have := h_cnt t s ht hs hb z hz
        omega
      · rw [Finset.sum_range_succ', add_zero, add_comm]
        refine add_le_add (le_of_eq ?_) (h_charged t s ht hs hb)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_assoc, add_comm 1 i]
    · simp only [ht, ↓reduceIte] at hcont
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
      obtain ⟨hcnt, hbz⟩ := h_free t s ht hs hb z hz
      rw [← hcnt]
      exact ih z.1 (hcont z.1) z.2 (hinv t s hs z hz) hbz

end OracleComp
