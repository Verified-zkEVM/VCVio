/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-! # Weighted query bounds through handlers

Weighted budgets use `IsQueryBound` with validity `w t ≤ b` and residual budget `b - w t`.
This structural formulation counts prefixes even when a later query has no possible answer.
`WorstCaseCostBound` bounds completed paths only, so it cannot in general supply a structural
budget. Structural weighted budgets do imply that semantic cost bound, and per-kind query
bounds supply both formulations without assumptions on answer types.
-/

public section

open OracleSpec

namespace OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- A stateful handler transfers a structural weighted budget to a target query budget. -/
theorem IsQueryBound.simulateQ_run_weighted
    {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} {σ : Type u}
    {w : ι → ℕ} {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α} {W : ℕ}
    (h : IsQueryBound oa W (fun t b => w t ≤ b) (fun t b => b - w t))
    (hstep : ∀ t s, IsQueryBoundP ((impl t).run s) q (w t)) (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q W := by
  induction oa using OracleComp.inductionOn generalizing W s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simpa only [Nat.add_sub_of_le h.1] using
      isQueryBoundP_bind (hstep t s) (fun z _ => ih z.1 (h.2 z.1) z.2)

/-- A stateless handler transfers a structural weighted budget to a target query budget. -/
theorem IsQueryBound.simulateQ_weighted
    {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    {w : ι → ℕ} {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')} {oa : OracleComp spec α} {W : ℕ}
    (h : IsQueryBound oa W (fun t b => w t ≤ b) (fun t b => b - w t))
    (hstep : ∀ t, IsQueryBoundP (impl t) q (w t)) :
    IsQueryBoundP (simulateQ impl oa) q W := by
  induction oa using OracleComp.inductionOn generalizing W with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query]
    simpa only [Nat.add_sub_of_le h.1] using
      isQueryBoundP_bind (hstep t) (fun a _ => ih a (h.2 a))

/-- Predicate-targeted counting is structural weighting by the predicate's indicator. -/
theorem isQueryBoundP_iff_weighted {p : ι → Prop} [DecidablePred p]
    (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa p n ↔
      IsQueryBound oa n (fun t b => (if p t then 1 else 0) ≤ b)
        (fun t b => b - (if p t then 1 else 0)) := by
  rw [isQueryBoundP_def]
  apply isQueryBound_congr
  · intro t b
    by_cases ht : p t <;> simp [ht, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  · intro t b
    split_ifs <;> simp

/-- Per-kind query budgets give the sum of the costs times their respective budgets. -/
theorem isQueryBound_weighted_of_per_kind {K : Type v} [Fintype K] [DecidableEq K]
    (κ : ι → K) (c n : K → ℕ) {oa : OracleComp spec α}
    (h : ∀ k, IsQueryBoundP oa (fun t => κ t = k) (n k)) :
    IsQueryBound oa (∑ k, c k * n k)
      (fun t b => c (κ t) ≤ b) (fun t b => b - c (κ t)) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBound_pure _ _ _ _
  | query_bind t f ih =>
    have ht := (isQueryBoundP_query_bind_iff _ _ _ _).mp (h (κ t))
    have hn : 0 < n (κ t) := ht.1.resolve_left (not_not_intro rfl)
    let n' := Function.update n (κ t) (n (κ t) - 1)
    have hsum : c (κ t) + ∑ k, c k * n' k = ∑ k, c k * n k := by
      have he : (fun k => c k * n' k) =
          Function.update (fun k => c k * n k) (κ t) (c (κ t) * (n (κ t) - 1)) := by
        funext k
        by_cases hk : k = κ t <;> simp [n', hk]
      rw [he, Finset.sum_update_of_mem (Finset.mem_univ (κ t)),
        Finset.sdiff_singleton_eq_erase,
        ← Finset.add_sum_erase _ (fun k => c k * n k) (Finset.mem_univ (κ t))]
      have heq : c (κ t) + c (κ t) * (n (κ t) - 1) = c (κ t) * n (κ t) := by
        calc
          _ = c (κ t) * (1 + (n (κ t) - 1)) := by simp [mul_add]
          _ = _ := by rw [Nat.add_sub_of_le hn]
      omega
    rw [isQueryBound_query_bind_iff]
    refine ⟨by omega, fun a => ?_⟩
    have hc : ∀ k, IsQueryBoundP (f a) (fun t => κ t = k) (n' k) := by
      intro k
      have hk := ((isQueryBoundP_query_bind_iff _ _ _ _).mp (h k)).2 a
      by_cases he : κ t = k
      · subst k
        simpa [n'] using hk
      · simpa [n', Function.update_of_ne (Ne.symm he), he] using hk
    have he : (∑ k, c k * n k) - c (κ t) = ∑ k, c k * n' k := by omega
    rw [he]
    exact ih a n' hc

/-- A structural weighted budget bounds all completed instrumented paths. -/
theorem IsQueryBound.toWorstCaseCostBound_weighted
    {ι : Type} {spec : OracleSpec ι} {α : Type}
    {oa : OracleComp spec α} {w : ι → ℕ} {W : ℕ}
    (h : IsQueryBound oa W (fun t b => w t ≤ b) (fun t b => b - w t)) :
    WorstCaseCostBound oa ⟨w⟩ W := by
  induction oa using OracleComp.inductionOn generalizing W with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at h
    rw [worstCaseCostBound_query_bind_iff]
    intro a z hz
    have hc := (worstCaseCostBound_iff_support_bound _ _ _).mp (ih a (h.2 a)) z hz
    change w t + Multiplicative.toAdd z.2 ≤ W
    omega

/-- Per-kind bounds imply the corresponding weighted worst-case cost bound. -/
theorem worstCaseCostBound_of_per_kind
    {ι : Type} {spec : OracleSpec ι} {α : Type} {K : Type v}
    [Fintype K] [DecidableEq K] (κ : ι → K) (c n : K → ℕ)
    {oa : OracleComp spec α}
    (h : ∀ k, IsQueryBoundP oa (fun t => κ t = k) (n k)) :
    WorstCaseCostBound oa ⟨fun t => c (κ t)⟩ (∑ k, c k * n k) :=
  (isQueryBound_weighted_of_per_kind κ c n h).toWorstCaseCostBound_weighted

end OracleComp
