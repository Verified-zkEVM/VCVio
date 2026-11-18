/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ParallelFinding
public import Mathlib.Data.ZMod.Basic

/-!
# Parallel search for a uniformly hidden marked input

The oracle is the additive bit oracle for one uniformly hidden input, rather than a uniformly
random Boolean function. The program, its local interpretation, initial substate and output
guess are independent of the hidden input. Adaptive measurements, mixed and subnormalized
states, repeated inputs and zero-width rounds are allowed. Success is unconditional: loss
and postselection do not renormalize the probability.

The proof compares with the zero oracle and sums query-union masses over all hidden inputs
before applying the square-root hybrid argument. The guessing term remains even with no calls.

## References

* C. Zalka, Grover's quantum searching algorithm is optimal, arXiv:quant-ph/9711070v2, §4.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Quantum
universe u v w
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The additive bit oracle marking exactly the input `y`. -/
@[expose]
def markedFunction (y : X) : X → ZMod 2 := fun z ↦ if z = y then 1 else 0

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
/-- Success at recovering a uniformly hidden marked input using one fixed adversary.
The final observer compares the guess with the same input that defined the oracle. -/
@[expose]
noncomputable def markedSearchAdvantage (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X (ZMod 2)) W A)
    (ρ : SubState A) (guess : (Σ a, W a) → X) : ℝ≥0∞ :=
  sampledEvalDistMap (fun y ↦ parallelOracleRuntime (markedFunction y)) I x ρ
    (fun y p ↦ guess p = y) {True}

/-- The search success probability is the uniform average of the fixed-mark success weights. -/
theorem markedSearchAdvantage_eq_sum (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X (ZMod 2)) W A)
    (ρ : SubState A) (guess : (Σ a, W a) → X) :
    markedSearchAdvantage I x ρ guess = (Fintype.card X : ℝ≥0∞)⁻¹ *
      ∑ y, (parallelOracleRuntime (markedFunction y)).evalDistMap I x ρ
        (fun p ↦ guess p = y) {True} := by
  rw [markedSearchAdvantage, sampledEvalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton _),
    Finset.mul_sum]

/-- Unconditional marked-search success is at most one, including subnormalized runs. -/
theorem markedSearchAdvantage_le_one [Nonempty X] (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X (ZMod 2)) W A)
    (ρ : SubState A) (guess : (Σ a, W a) → X) :
    markedSearchAdvantage I x ρ guess ≤ 1 := by
  classical
  rw [markedSearchAdvantage_eq_sum]
  calc
    _ ≤ (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ _y : X, (1 : ℝ≥0∞) := by
      gcongr with y
      exact measure_le_one _ _
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)

/-- Parallel marked search under a total round budget `q` and total point budget `Q`.
The points add the widths along each adaptive branch; no maximum width is required.
The initial state, local operations and guessing rule are independent of the mark, and
success remains unconditional when input or execution mass is lost. -/
theorem markedSearchAdvantage_le_of_isPointBound [Nonempty X] (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X (ZMod 2)) W A} {q Q : ℕ}
    (hq : x.IsTotalQueryBound q) (hQ : x.IsPointBound Q)
    (ρ : SubState A) (guess : (Σ a, W a) → X) :
    markedSearchAdvantage I x ρ guess ≤ min 1
      (ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) / Fintype.card X) := by
  apply le_min (markedSearchAdvantage_le_one I x ρ guess)
  rw [markedSearchAdvantage_eq_sum]
  have hsum : ∑ y, (parallelOracleRuntime (markedFunction y)).evalDistMap I x ρ
      (fun p ↦ guess p = y) {True} ≤
        ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) := by
    have h := sum_mul_evalDistMap_mem_parallel_le_of_isPointBound I
      (0 : X → ZMod 2) markedFunction (fun _ : X ↦ (1 : ℝ)) (fun _ ↦ by norm_num)
      (fun y ↦ {y}) (fun y z hz ↦ by
        simp only [Set.mem_singleton_iff] at hz
        simp [markedFunction, hz])
      1 (by norm_num) (fun z ↦ by simp [Set.indicator]) hq hQ ρ guess
    simpa only [ENNReal.ofReal_one, one_mul, Set.mem_singleton_iff] using h
  calc
    _ ≤ (Fintype.card X : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) :=
      mul_le_mul le_rfl hsum bot_le bot_le
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- Parallel search for a uniformly hidden marked input after at most `q` rounds of width
at most `k`. The initial state, local operations and guessing rule are independent of the mark.
The term `1` retains the no-query guessing probability. -/
theorem markedSearchAdvantage_le [Nonempty X] (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X (ZMod 2)) W A} {q k : ℕ}
    (hq : x.IsTotalQueryBound q) (hk : x.IsWidthBound k)
    (ρ : SubState A) (guess : (Σ a, W a) → X) :
    markedSearchAdvantage I x ρ guess ≤ min 1
      (ENNReal.ofReal ((1 + 2 * (q : ℝ) * Real.sqrt k) ^ 2) / Fintype.card X) := by
  have h := markedSearchAdvantage_le_of_isPointBound I hq (hq.isPointBound hk) ρ guess
  have hsqrt : Real.sqrt ((q : ℝ) * ((k * q : ℕ) : ℝ)) = (q : ℝ) * Real.sqrt k := by
    rw [Nat.cast_mul, show (q : ℝ) * ((k : ℝ) * q) = (q : ℝ) ^ 2 * k by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  simpa only [hsqrt, mul_assoc] using h

end Quantum
