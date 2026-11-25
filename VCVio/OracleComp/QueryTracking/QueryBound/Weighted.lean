/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! # Weighted budgets through handlers

A weighted budget is PolyFun's prefix charge bound `PFunctor.FreeM.IsChargeBound oa w W`: along
every path, each prefix of `oa` spends at most `W`, where a query at `t` costs `w t`. It charges a
query even when that query has no possible answer, so it is stronger than the completed-path bound
`WorstCaseCostBound`, which it implies (`worstCaseCostBound_of_isChargeBound`); the converse needs
every reachable query to have an answer (`PFunctor.FreeM.isChargeBound_of_forall_charge_le`).
Predicate-targeted budgets are its indicator case (`isQueryBoundP_iff_isChargeBound`), and
budgets on several predicates, which may overlap, combine into one weighted budget
(`isChargeBound_of_predicates`, with disjoint kinds as `isChargeBound_of_per_kind`).

Through a handler whose every step stays within the charge of its query, the simulation stays
within the same budget: `isChargeBound_run_simulateQ` for stateful handlers and
`isChargeBound_simulateQ` for stateless ones. These are PolyFun's `IsChargeBound.run_liftM` and
`IsChargeBound.liftM`, stated for `simulateQ`.
-/

public section

open OracleSpec

namespace OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

section Transfer

variable {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} {ω : Type w}
  [AddMonoid ω] [Preorder ω] [AddLeftMono ω] [AddRightMono ω]

/-- A stateful handler whose every step stays within the charge of its query, from every state,
transfers a weighted budget from the source program to the simulation. -/
theorem isChargeBound_run_simulateQ {σ : Type u}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {c : ι → ω} {d : ι' → ω}
    (hstep : ∀ t s, PFunctor.FreeM.IsChargeBound ((impl t).run s) d (c t))
    {oa : OracleComp spec α} {W : ω} (h : PFunctor.FreeM.IsChargeBound oa c W) (s : σ) :
    PFunctor.FreeM.IsChargeBound ((simulateQ impl oa).run s) d W := by
  rw [simulateQ]
  exact PFunctor.FreeM.IsChargeBound.run_liftM impl.toHandler hstep h s

/-- A stateless handler whose every step stays within the charge of its query transfers a
weighted budget from the source program to the simulation. -/
theorem isChargeBound_simulateQ
    {impl : QueryImpl spec (OracleComp spec')} {c : ι → ω} {d : ι' → ω}
    (hstep : ∀ t, PFunctor.FreeM.IsChargeBound (impl t) d (c t))
    {oa : OracleComp spec α} {W : ω} (h : PFunctor.FreeM.IsChargeBound oa c W) :
    PFunctor.FreeM.IsChargeBound (simulateQ impl oa) d W := by
  rw [simulateQ]
  exact PFunctor.FreeM.IsChargeBound.liftM impl hstep h

end Transfer

/-- The weighted sum `v ↦ ∑ k, c k * v k`, as a monotone additive map. -/
private def weightedSum {K : Type v} [Fintype K] (c : K → ℕ) : (K → ℕ) →+o ℕ where
  toFun v := ∑ k, c k * v k
  map_zero' := by simp
  map_add' v v' := by simp [mul_add, Finset.sum_add_distrib]
  monotone' _ _ hv := Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (hv k)

private theorem weightedSum_apply {K : Type v} [Fintype K] (c v : K → ℕ) :
    weightedSum c v = ∑ k, c k * v k := rfl

/-- Budgets `n k` on query predicates `p k`, which may overlap, give the weighted budget
`∑ k, c k * n k` for the charge summing the weights `c k` of the predicates a query satisfies.
Queries satisfying no predicate are free. -/
theorem isChargeBound_of_predicates {K : Type v} [Fintype K]
    (p : K → ι → Prop) [∀ k, DecidablePred (p k)] (c n : K → ℕ) {oa : OracleComp spec α}
    (h : ∀ k, IsQueryBoundP oa (p k) (n k)) :
    PFunctor.FreeM.IsChargeBound oa (fun t => ∑ k, if p k t then c k else 0)
      (∑ k, c k * n k) := by
  have hv : PFunctor.FreeM.IsChargeBound oa (fun t k => if p k t then 1 else 0) n :=
    PFunctor.FreeM.isChargeBound_pi_iff.2 fun k => (isQueryBoundP_iff_isChargeBound _ _ _).1 (h k)
  simpa [weightedSum_apply, Function.comp_def, mul_ite] using hv.map (weightedSum c)

/-- Per-kind query budgets give the weighted budget that charges `c k` for a query of kind `k`:
the sum of the costs times their respective budgets. -/
theorem isChargeBound_of_per_kind {K : Type v} [Fintype K] [DecidableEq K]
    (κ : ι → K) (c n : K → ℕ) {oa : OracleComp spec α}
    (h : ∀ k, IsQueryBoundP oa (fun t => κ t = k) (n k)) :
    PFunctor.FreeM.IsChargeBound oa (fun t => c (κ t)) (∑ k, c k * n k) := by
  simpa [Finset.sum_ite_eq] using isChargeBound_of_predicates (fun k t => κ t = k) c n h

/-- A weighted budget bounds the charge of every completed instrumented path. -/
theorem worstCaseCostBound_of_isChargeBound {ι : Type} {spec : OracleSpec ι} {α ω : Type}
    [AddCommMonoid ω] [Preorder ω] {oa : OracleComp spec α} {w : ι → ω} {W : ω}
    (h : PFunctor.FreeM.IsChargeBound oa w W) : WorstCaseCostBound oa ⟨w⟩ W := by
  rw [worstCaseCostBound_iff_forall_charge_le]
  intro p
  simpa using PFunctor.FreeM.Path.charge_le_of_isChargeBound h p

/-- Per-kind bounds imply the corresponding weighted worst-case cost bound. -/
theorem worstCaseCostBound_of_per_kind
    {ι : Type} {spec : OracleSpec ι} {α : Type} {K : Type v}
    [Fintype K] [DecidableEq K] (κ : ι → K) (c n : K → ℕ)
    {oa : OracleComp spec α}
    (h : ∀ k, IsQueryBoundP oa (fun t => κ t = k) (n k)) :
    WorstCaseCostBound oa ⟨fun t => c (κ t)⟩ (∑ k, c k * n k) :=
  worstCaseCostBound_of_isChargeBound (isChargeBound_of_per_kind κ c n h)

end OracleComp
