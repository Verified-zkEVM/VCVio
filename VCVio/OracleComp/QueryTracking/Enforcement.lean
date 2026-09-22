/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Enforcement Oracle

Oracle wrapper that enforces a query budget by silently dropping queries beyond
the budget. This implements EasyCrypt's `Enforce`/`Bounder` pattern.

## Main Definitions

- `enforceOracle`: Oracle that tracks remaining budget via `StateT` and returns
  `default` for queries exceeding the budget.

## Main Results

- `enforceOracle.fst_map_run_simulateQ`: Enforcement is transparent for computations
  within their query bound.
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

/-- When the computation is within its query bound, enforcement is transparent:
the output distribution is identical to running without enforcement. -/
theorem fst_map_run_simulateQ {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    Prod.fst <$> (simulateQ enforceOracle oa).run qb = oa := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => simp
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    obtain ⟨hpos, hcont⟩ := h
    rw [run_simulateQ_query_bind (so := spec.enforceOracle) t mx qb,
      run_apply, ite_eq_left hpos]
    simp only [monad_norm, Function.comp]
    exact bind_congr fun u => by
      simpa only [map_eq_bind_pure_comp] using ih u (hcont u)

section Probability

variable {ι : Type} {spec : OracleSpec ι} {α : Type}
  [DecidableEq ι] [∀ t, Inhabited (spec.Range t)]
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [IsMeasureSpec spec]

omit [∀ t, Inhabited (spec.Range t)] in
/-- A structural query bound makes its budget check redundant in the counting event. -/
theorem prEvent_counting_budget_eq {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr{let z ← countingOracle.simulate oa 0}[p z.1 ∧ z.2 ≤ qb] =
      Pr{let x ← oa}[p x] := by
  rw [OracleComp.prEvent_congr_of_support (countingOracle.simulate oa 0)
    (fun z => p z.1 ∧ z.2 ≤ qb) (fun z => p z.1)
    (fun z hz => and_iff_left (h.counting_bounded hz))]
  have hproj : Prod.fst <$> countingOracle.simulate oa 0 = oa := by
    simp [countingOracle.simulate]
  exact (prEvent_map (m := OracleComp spec) (countingOracle.simulate oa 0)
    Prod.fst p).symm.trans
      (congrArg (fun comp : OracleComp spec α => Pr{let x ← comp}[p x]) hproj)

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
