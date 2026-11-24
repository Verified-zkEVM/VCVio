/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! # Weighted query bounds through handlers

Weighted budgets use `IsQueryBound` with validity `w t ≤ b` and residual budget `b - w t`.
This structural formulation counts prefixes even when a later query has no possible answer.
`WorstCaseCostBound` bounds completed paths only, so it cannot in general supply a structural
budget. Structural weighted budgets do imply that semantic cost bound, and per-kind query
bounds supply both formulations without assumptions on answer types.

A weighted budget is PolyFun's prefix charge bound `PFunctor.FreeM.IsChargeBound oa w W`
(`PFunctor.FreeM.isChargeBound_iff_isRollBound_nat`). The handler transfers are
`IsChargeBound.run_liftM` and `IsChargeBound.liftM`, per-kind budgets are the pushforward of one
vector charge along a weighted sum (`isChargeBound_pi_iff`, `IsChargeBound.map`), and the
completed-path bound is `PFunctor.FreeM.Path.charge_le_of_isChargeBound`.
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
  rw [isQueryBoundP_iff_isChargeBound, simulateQ]
  exact PFunctor.FreeM.IsChargeBound.run_liftM impl
    (fun t s => (isQueryBoundP_iff_isChargeBound _ _ _).1 (hstep t s))
    ((PFunctor.FreeM.isChargeBound_iff_isRollBound_nat oa w W).2 h) s

/-- A stateless handler transfers a structural weighted budget to a target query budget. -/
theorem IsQueryBound.simulateQ_weighted
    {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    {w : ι → ℕ} {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')} {oa : OracleComp spec α} {W : ℕ}
    (h : IsQueryBound oa W (fun t b => w t ≤ b) (fun t b => b - w t))
    (hstep : ∀ t, IsQueryBoundP (impl t) q (w t)) :
    IsQueryBoundP (simulateQ impl oa) q W := by
  rw [isQueryBoundP_iff_isChargeBound, simulateQ]
  exact PFunctor.FreeM.IsChargeBound.liftM impl
    (fun t => (isQueryBoundP_iff_isChargeBound _ _ _).1 (hstep t))
    ((PFunctor.FreeM.isChargeBound_iff_isRollBound_nat oa w W).2 h)

/-- Predicate-targeted counting is structural weighting by the predicate's indicator. -/
theorem isQueryBoundP_iff_weighted {p : ι → Prop} [DecidablePred p]
    (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa p n ↔
      IsQueryBound oa n (fun t b => (if p t then 1 else 0) ≤ b)
        (fun t b => b - (if p t then 1 else 0)) :=
  (isQueryBoundP_iff_isChargeBound p oa n).trans
    (PFunctor.FreeM.isChargeBound_iff_isRollBound_nat oa _ n)

/-- The weighted sum `v ↦ ∑ k, c k * v k`, as a monotone additive map. -/
private def weightedSum {K : Type v} [Fintype K] (c : K → ℕ) : (K → ℕ) →+o ℕ where
  toFun v := ∑ k, c k * v k
  map_zero' := by simp
  map_add' v v' := by simp [mul_add, Finset.sum_add_distrib]
  monotone' _ _ hv := Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (hv k)

private theorem weightedSum_apply {K : Type v} [Fintype K] (c v : K → ℕ) :
    weightedSum c v = ∑ k, c k * v k := rfl

/-- Per-kind query budgets give the sum of the costs times their respective budgets. -/
theorem isQueryBound_weighted_of_per_kind {K : Type v} [Fintype K] [DecidableEq K]
    (κ : ι → K) (c n : K → ℕ) {oa : OracleComp spec α}
    (h : ∀ k, IsQueryBoundP oa (fun t => κ t = k) (n k)) :
    IsQueryBound oa (∑ k, c k * n k)
      (fun t b => c (κ t) ≤ b) (fun t b => b - c (κ t)) := by
  have hv : PFunctor.FreeM.IsChargeBound oa (fun t k => if κ t = k then 1 else 0) n :=
    PFunctor.FreeM.isChargeBound_pi_iff.2 fun k => (isQueryBoundP_iff_isChargeBound _ _ _).1 (h k)
  rw [isQueryBound_iff_isRollBound, ← PFunctor.FreeM.isChargeBound_iff_isRollBound_nat]
  simpa [weightedSum_apply, Function.comp_def, mul_ite, Finset.sum_ite_eq] using
    hv.map (weightedSum c)

/-- A structural weighted budget bounds all completed instrumented paths. -/
theorem IsQueryBound.toWorstCaseCostBound_weighted
    {ι : Type} {spec : OracleSpec ι} {α : Type}
    {oa : OracleComp spec α} {w : ι → ℕ} {W : ℕ}
    (h : IsQueryBound oa W (fun t b => w t ≤ b) (fun t b => b - w t)) :
    WorstCaseCostBound oa ⟨w⟩ W := by
  rw [worstCaseCostBound_iff_forall_charge_le]
  intro p
  simpa using PFunctor.FreeM.Path.charge_le_of_isChargeBound
    ((PFunctor.FreeM.isChargeBound_iff_isRollBound_nat oa w W).2 h) p

/-- Per-kind bounds imply the corresponding weighted worst-case cost bound. -/
theorem worstCaseCostBound_of_per_kind
    {ι : Type} {spec : OracleSpec ι} {α : Type} {K : Type v}
    [Fintype K] [DecidableEq K] (κ : ι → K) (c n : K → ℕ)
    {oa : OracleComp spec α}
    (h : ∀ k, IsQueryBoundP oa (fun t => κ t = k) (n k)) :
    WorstCaseCostBound oa ⟨fun t => c (κ t)⟩ (∑ k, c k * n k) :=
  (isQueryBound_weighted_of_per_kind κ c n h).toWorstCaseCostBound_weighted

end OracleComp
