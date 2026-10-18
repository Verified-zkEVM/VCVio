/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Cost
public import PolyFun.PFunctor.Handler.Machine.Admission
public import Mathlib.Algebra.Order.Ring.Rat

/-!
# Executable admission budgets for persistent threshold queries

A client shares a dyadic prefix and an exact nonnegative rational allowance.
Admission reserves the cap's geometric tail before running the query. Refusal
performs no random-bit effect. Timeout retains both the debit and the refined
prefix, and aborts the client through `ExceptT` over `StateT`.

The charge bounds the local cutoff probability. Comparison with an ideal
service additionally requires a common admission policy and a reconstruction
contract; the executable admission check alone does not assert that contract.
-/

public section

open OracleComp PFunctor MeasureTheory
open scoped ENNReal

namespace UniformThreshold.Budget

/-- A persistent random prefix paired with its remaining precision allowance. -/
abbrev Session := Prefix × ℚ≥0

/-- A session distinguishes refusal before sampling from timeout after an admitted call. -/
inductive Failure where
  | budgetExhausted
  | timeout
  deriving DecidableEq, Repr

/-- The exact rational geometric tail reserved for a bit cap. -/
@[expose] def charge (fuel : ℕ) : ℚ≥0 := (1 / 2) ^ fuel

/-- Admit a cap only when its entire allowance is available, debiting before execution. -/
@[expose] def admission (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session) :
    Except Failure (ℕ × Session) :=
  let fuel := cap q state
  if charge fuel ≤ state.2 then .ok (fuel, (state.1, state.2 - charge fuel))
  else .error .budgetExhausted

/-- The admission reserve and the remaining allowance exactly partition the prior budget. -/
theorem debit_add_charge (fuel : ℕ) (allowance : ℚ≥0) (h : charge fuel ≤ allowance) :
    (allowance - charge fuel) + charge fuel = allowance := tsub_add_cancel_of_le h

/-- Admission uses the supplied cap and debits exactly its stated allowance. -/
theorem admission_ok (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : charge (cap q state) ≤ state.2) :
    admission cap q state = .ok (cap q state, (state.1, state.2 - charge (cap q state))) := by
  simp only [admission, h, ↓reduceIte]

/-- Insufficient allowance is an explicit refusal. -/
theorem admission_error (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : state.2 < charge (cap q state)) : admission cap q state = .error .budgetExhausted := by
  simp only [admission, not_le.mpr h, ↓reduceIte]

/-- The executable rational reserve is the same geometric tail as the measure bound. -/
theorem coe_charge (fuel : ℕ) : (charge fuel : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  rw [← ENNReal.coe_nnratCast]
  norm_num [charge, ENNReal.coe_pow]

/-- A cap's failure probability is bounded by its reserved rational allowance. -/
theorem cutoff_le_charge (q : ℚ) (p : Prefix) (fuel : ℕ) :
    boundedLaw q p fuel {none} ≤ (charge fuel : ℝ≥0∞) := by
  rw [coe_charge]
  exact cutoff_le q p fuel

/-- The shared admission adapter retains the last sampled prefix when a call times out. -/
@[expose] def handler (cap : ℚ → Session → ℕ) :
    Handler (ExceptT Failure (StateT Session (FreeM coinSpec.toPFunctor))) spec.toPFunctor :=
  machineHandler.admitted (admission cap) (fun _ _ residual => (.timeout, residual))

/-- Run an adaptive finite client with permanent abort and retained session state. -/
@[expose] def run {α : Type} (cap : ℚ → Session → ℕ)
    (program : FreeM spec.toPFunctor α) (state : Session) :
    FreeM coinSpec.toPFunctor (Except Failure α × Session) :=
  ((program.liftM (handler cap)).run).run state

/-- A finished client preserves the prefix and unused allowance. -/
@[simp] theorem run_pure {α : Type} (cap : ℚ → Session → ℕ) (value : α) (state : Session) :
    run cap (pure value) state = pure (.ok value, state) := by rfl

/-- Budget refusal stops the client before the current or any later bit query. -/
theorem run_refused {α : Type} (cap : ℚ → Session → ℕ) (q : ℚ)
    (next : Bool → FreeM spec.toPFunctor α) (state : Session)
    (h : state.2 < charge (cap q state)) :
    run cap (.liftBind q next) state = pure (.error .budgetExhausted, state) :=
  machineHandler.liftM_admitted_refused (admission cap) _ q next state .budgetExhausted
    (admission_error cap q state h)

/-- An executable conservative cap reserving less than half of a positive allowance.
It uses only the denominator's integer bit length and adds no service counter. -/
@[expose] def halfAllowanceCap (_ : ℚ) (state : Session) : ℕ := state.2.den.log2 + 2

/-- Positive allowance pays the cap and leaves more than half for later calls. -/
theorem charge_halfAllowanceCap_lt (q : ℚ) (state : Session) (h : 0 < state.2) :
    charge (halfAllowanceCap q state) < state.2 / 2 := by
  have hd : (state.2.den : ℚ≥0) < (2 : ℚ≥0) ^ (state.2.den.log2 + 1) := by
    exact_mod_cast Nat.lt_log2_self (n := state.2.den)
  have hdpos : (0 : ℚ≥0) < state.2.den := by exact_mod_cast state.2.den_pos
  have hn : (1 : ℚ≥0) ≤ state.2.num := by
    exact_mod_cast Nat.succ_le_of_lt (NNRat.num_pos.mpr h)
  have hbound : 1 / (2 : ℚ≥0) ^ (state.2.den.log2 + 1) < state.2 := by
    calc
      _ < 1 / (state.2.den : ℚ≥0) := one_div_lt_one_div_of_lt hdpos hd
      _ ≤ (state.2.num : ℚ≥0) / state.2.den :=
        div_le_div_of_nonneg_right hn (le_of_lt hdpos)
      _ = state.2 := NNRat.num_div_den state.2
  have hhalf := div_lt_div_of_pos_right hbound (by norm_num : (0 : ℚ≥0) < 2)
  convert hhalf using 1
  simp [charge, halfAllowanceCap, pow_succ, div_eq_mul_inv, mul_comm]

/-- The conservative cap admits every call with positive remaining allowance. -/
theorem admission_halfAllowanceCap (q : ℚ) (state : Session) (h : 0 < state.2) :
    admission halfAllowanceCap q state =
      .ok (halfAllowanceCap q state, (state.1, state.2 - charge (halfAllowanceCap q state))) := by
  apply admission_ok
  exact (charge_halfAllowanceCap_lt q state h).le.trans (div_le_self zero_le (by norm_num))

end UniformThreshold.Budget
