/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ClassicalRandomized
public import Mathlib.Data.ZMod.Basic

/-!
# Sequential randomized classical embedding regressions

A private coin selects an address, repeated calls test consistency, and an oracle answer
selects the final address. Exact fixed-table answers, lazy random-oracle laws, and query budgets
are checked over a nonbinary response group.
-/

public section

open Quantum OracleSpec OracleComp MeasureTheory Matrix
open scoped ENNReal

namespace VCVioTest.QuantumClassicalRandomized

/-- A private coin chooses the first address; its answer chooses the final address. -/
@[expose]
def adaptive : OracleComp (unifSpec + (Bool →ₒ ZMod 3))
    (Fin 2 × ZMod 3 × ZMod 3 × ZMod 3) := do
  let b : Fin 2 ← liftM ((unifSpec + (Bool →ₒ ZMod 3)).query (.inl 1))
  let x : Bool := b == 0
  let y : ZMod 3 ← liftM ((unifSpec + (Bool →ₒ ZMod 3)).query (.inr x))
  let z : ZMod 3 ← liftM ((unifSpec + (Bool →ₒ ZMod 3)).query (.inr x))
  let w : ZMod 3 ← liftM ((unifSpec + (Bool →ₒ ZMod 3)).query (.inr (if y = 0 then !x else x)))
  pure (b, y, z, w)

/-- The deterministic answer tuple at a fixed private coin and function. -/
@[expose]
def answers (H : Bool → ZMod 3) (b : Fin 2) : Fin 2 × ZMod 3 × ZMod 3 × ZMod 3 :=
  let x : Bool := b == 0
  (b, H x, H x, H (if H x = 0 then !x else x))

/-- Fixed-table simulation retains precisely the initial private coin. -/
theorem simulateQ_adaptive (H : Bool → ZMod 3) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) adaptive =
      (do let b ← (liftM (unifSpec.query 1) : ProbComp (Fin 2)); pure (answers H b)) := by
  rfl

/-- Distinct table values exercise both branches of the answer-dependent final address. -/
@[expose]
def table (b : Bool) : ZMod 3 := if b then 2 else 0

/-- The first private-coin branch reads `true` three times. -/
example : answers table 0 = (0, 2, 2, 2) := by decide

/-- The second branch reads `false` twice, then changes its address to `true`. -/
example : answers table 1 = (1, 0, 0, 2) := by decide

/-- The actual quantum run has the expected two concrete tuples, with its private coin intact. -/
example :
    (additiveOracleRuntime table).evalDist₂ .instruments adaptive.toQuantumRandomized
      (SubState.basis ()) =
      𝒟[(liftM (unifSpec.query 1) : ProbComp (Fin 2)) >>= fun b ↦
          pure (if b = 0 then (0, 2, 2, 2) else (1, 0, 0, 2) :
            Fin 2 × ZMod 3 × ZMod 3 × ZMod 3)] := by
  rw [evalDist_additiveOracleRuntime_toQuantumRandomized, simulateQ_adaptive]
  congr 1
  congr 1
  funext b
  fin_cases b <;> rfl

/-- Repeated responses coincide for every function, not only for the concrete test table. -/
example (H : Bool → ZMod 3) (b : Fin 2) :
    (answers H b).2.1 = (answers H b).2.2.1 := rfl

/-- A classical basis call really returns the nonbinary table answer. -/
example (d : (additiveOracleRuntime table).D) :
    ((additiveOracleRuntime table).run₂ .instruments (classicalQuery true)).branch 2
      (Matrix.single ((), d) ((), d) 1) = Matrix.single ((), d) ((), d) 1 := by
  rw [run_classicalQuery]
  exact LinearMap.congr_fun (SubInstrument.branch_pure_self (2 : ZMod 3)) _

/-- The private randomized adaptive program has the complete shared-cache lazy oracle law. -/
example :
    qromEvalDist₂ .instruments adaptive.toQuantumRandomized (SubState.basis ()) =
      𝒟[(simulateQ (Bool →ₒ ZMod 3).romImpl adaptive).run' ∅] :=
  qromEvalDist₂_toQuantumRandomized_eq_randomOracle adaptive

/-- Exactly three function calls are needed syntactically; the private coin is free. -/
theorem adaptive_classical_budget (n : ℕ) :
    adaptive.IsQueryBoundP (fun t ↦ t.isRight = true) n ↔ 3 ≤ n := by
  simp [adaptive, isQueryBoundP_query_bind_iff]
  omega

/-- The function-query budget transfers to the actual quantum program. -/
example : adaptive.toQuantumRandomized.IsQueryBound (fun _ ↦ 3) :=
  ((adaptive_classical_budget 3).mpr le_rfl).isQueryBound_toQuantumRandomized

/-- Two function calls do not cover the adaptive program. -/
example : ¬ adaptive.IsQueryBoundP (fun t ↦ t.isRight = true) 2 := by
  rw [adaptive_classical_budget]
  omega

/-- An actual quantum basis query cannot fit a zero oracle budget. -/
example : ¬ (classicalQuery (Y := ZMod 3) true).IsQueryBound (fun _ ↦ 0) := by
  intro h
  rw [classicalQuery, QComp.isQueryBound_act_bind_iff] at h
  have h₀ := h ()
  rw [QuantumComp₂.query_bind, QuantumComp₂.queryBind] at h₀
  have hz := (QuantumComp.IsQueryBound.of_queryBind h₀).1
  omega

/-- A computation using only private randomness. -/
@[expose]
def coinsOnly : OracleComp (unifSpec + (Bool →ₒ ZMod 3)) (Fin 3) :=
  liftM ((unifSpec + (Bool →ₒ ZMod 3)).query (.inl 2))

/-- A three-way private coin contributes no quantum oracle queries. -/
example : coinsOnly.toQuantumRandomized.IsQueryBound (fun _ ↦ 0) := by
  have h : coinsOnly.IsQueryBoundP (fun t ↦ t.isRight = true) 0 := by simp [coinsOnly]
  exact h.isQueryBound_toQuantumRandomized

/-- The quantum private-coin law is its original uniform classical law. -/
example (H : Bool → ZMod 3) :
    (additiveOracleRuntime H).evalDist₂ .instruments coinsOnly.toQuantumRandomized
      (SubState.basis ()) = 𝒟[(liftM (unifSpec.query 2) : ProbComp (Fin 3))] := by
  rw [evalDist_additiveOracleRuntime_toQuantumRandomized]
  rfl

end VCVioTest.QuantumClassicalRandomized
