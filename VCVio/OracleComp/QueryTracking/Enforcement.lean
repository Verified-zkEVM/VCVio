/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import PolyFun.PFunctor.Handler.Charge

/-!
# Enforcement Oracle

Oracle wrapper that enforces a query budget by silently dropping queries beyond
the budget. This implements EasyCrypt's `Enforce`/`Bounder` pattern.

## Main Definitions

- `enforceOracle`: Oracle that tracks remaining budget via `StateT` and returns
  `default` for queries exceeding the budget.

## Main Results

- `enforceOracle.run_simulateQ_sub_eq`: Enforcement is PolyFun's budget gate with fallback,
  `PFunctor.Handler.withBudgetOr`, for that charge and the same `default` fallback. Enforcement
  keeps the remaining budget `qb - spent` as state where `withBudgetOr` keeps the amount spent.
- `enforceOracle.fst_map_run_simulateQ`: Enforcement is transparent for computations
  within their query bound (`PFunctor.Handler.run_liftM_withBudgetOr_of_isChargeBound`).
-/

@[expose] public section

open OracleSpec OracleComp

universe u

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u}

/-- Enforcement oracle: wraps the original oracle with a per-index budget tracked via `StateT`.
When the remaining budget for the queried oracle is positive, the query is forwarded and
the budget decremented. When the budget is exhausted, `default` is returned silently. -/
def OracleSpec.enforceOracle [DecidableEq ι] [∀ t, Inhabited (spec.Range t)] :
    QueryImpl spec (StateT (ι → ℕ) (OracleComp spec)) :=
  fun t => StateT.mk fun budget =>
    if 0 < budget t then
      (·, Function.update budget t (budget t - 1)) <$> liftM (query t)
    else
      pure (default, budget)

namespace enforceOracle

variable [DecidableEq ι] [∀ t, Inhabited (spec.Range t)]

@[simp]
lemma run_apply (t : ι) (budget : ι → ℕ) :
    (spec.enforceOracle t).run budget =
      if 0 < budget t then
        (·, Function.update budget t (budget t - 1)) <$> liftM (query t)
      else
        pure (default, budget) := rfl

/-- **Remaining and spent budgets.** Enforcement from the remaining budget `qb - spent` is
PolyFun's budget gate with fallback from the amount `spent`, charging `Pi.single t 1` for a query
at `t` against the budget `qb` and answering `default` past it, with the final state read back as
the remaining budget. The correspondence needs `spent ≤ qb`: the gate compares every index, while
enforcement checks only the queried one. -/
theorem run_simulateQ_sub_eq [DecidableLE (ι → ℕ)] (oa : OracleComp spec α)
    {qb spent : ι → ℕ} (hspent : spent ≤ qb) :
    (simulateQ spec.enforceOracle oa).run (qb - spent) =
      Prod.map id (qb - ·) <$> (simulateQ (PFunctor.Handler.withBudgetOr (P := spec.toPFunctor)
        (QueryImpl.ofLift spec (OracleComp spec)) (fun t => Pi.single t 1) qb
        (fun _ => default)) oa).run spent := by
  induction oa using OracleComp.inductionOn generalizing spent with
  | pure x => simp
  | query_bind t mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, run_apply]
    by_cases h : spent + Pi.single t 1 ≤ qb
    · have hpos : 0 < (qb - spent) t := by
        have := h t
        simp at this ⊢
        omega
      have hupd : Function.update (qb - spent) t ((qb - spent) t - 1) =
          qb - (spent + Pi.single t 1) := by
        funext j
        by_cases hj : j = t
        · subst hj; simp; omega
        · simp [hj]
      simp only [ite_eq_left hpos, ite_eq_left h, PFunctor.Handler.withBudgetOr, StateT.run, hupd,
        bind_map_left, map_bind]
      exact bind_congr fun u => ih u h
    · have hpos : ¬ 0 < (qb - spent) t := by
        refine fun hlt => h fun j => ?_
        by_cases hj : j = t
        · subst hj; simp at hlt ⊢; omega
        · simpa [Pi.single_apply, hj] using hspent j
      simp only [ite_eq_right hpos, ite_eq_right h, PFunctor.Handler.withBudgetOr, StateT.run,
        pure_bind]
      exact ih default hspent

/-- When the computation is within its query bound, enforcement is transparent:
the output distribution is identical to running without enforcement. -/
theorem fst_map_run_simulateQ {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    Prod.fst <$> (simulateQ enforceOracle oa).run qb = oa := by
  classical
  have hrun := run_simulateQ_sub_eq oa (qb := qb) (spent := 0) zero_le
  rw [tsub_zero] at hrun
  rw [hrun, Functor.map_map,
    show (fun z : α × (ι → ℕ) => (Prod.map id (qb - ·) z).1) = Prod.fst from rfl, simulateQ,
    PFunctor.Handler.run_liftM_withBudgetOr_of_isChargeBound _ _ _
      ((isPerIndexQueryBound_iff_isChargeBound oa qb).1 h),
    PFunctor.Handler.fst_map_run_liftM_withCharge]
  exact simulateQ_ofLift_eq_self oa

section Probability

variable {ι : Type} {spec : OracleSpec ι} {α : Type} [DecidableEq ι]
  [AnswerMeasure spec]

/-- A structural query bound makes its budget check redundant in the counting event. -/
theorem prEvent_counting_budget_eq {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr{let z ← countingOracle.simulate oa 0}[p z.1 ∧ z.2 ≤ qb] =
      Pr{let x ← oa}[p x] := by
  rw [prEvent_congr_of_support (countingOracle.simulate oa 0)
    (fun z => p z.1 ∧ z.2 ≤ qb) (fun z => p z.1)
    (fun z hz => and_iff_left (h.counting_bounded hz))]
  have hproj : Prod.fst <$> countingOracle.simulate oa 0 = oa := by
    simp [countingOracle.simulate]
  exact (prEvent_map (m := OracleComp spec) (countingOracle.simulate oa 0)
    Prod.fst p).symm.trans
      (congrArg (fun comp : OracleComp spec α => Pr{let x ← comp}[p x]) hproj)

variable [∀ t, Inhabited (spec.Range t)]

/-- Under a structural query bound, the counting event agrees with the enforcement event. -/
theorem prEvent_counting_budget_eq_enforce {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr{let z ← countingOracle.simulate oa 0}[p z.1 ∧ z.2 ≤ qb] =
      Pr{let x ← Prod.fst <$> (simulateQ enforceOracle oa).run qb}[p x] := by
  rw [fst_map_run_simulateQ h]
  exact prEvent_counting_budget_eq h p

/-- Structural boundedness implies the counting-to-enforcement event inequality. -/
theorem prEvent_counting_budget_le_enforce {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr{let z ← countingOracle.simulate oa 0}[p z.1 ∧ z.2 ≤ qb] ≤
      Pr{let x ← Prod.fst <$> (simulateQ enforceOracle oa).run qb}[p x] := by
  rw [prEvent_counting_budget_eq_enforce h p]

end Probability

end enforceOracle
