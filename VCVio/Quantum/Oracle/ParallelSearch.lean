/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import VCVio.Quantum.Comp.ChargeWeight
public import VCVio.Quantum.Oracle.ParallelHybrid
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

open MeasureTheory Matrix
open scoped ENNReal Kronecker

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

private theorem sum_evalDistMap_guess_le (R : QuantumRuntime (qromBatchSpec X (ZMod 2)))
    (I : L.Interp) (x : QuantumComp L (qromBatchSpec X (ZMod 2)) W A)
    (ρ : SubState A) (guess : (Σ a, W a) → X) :
    ∑ y : X, R.evalDistMap I x ρ (fun p ↦ guess p = y) {True} ≤ 1 := by
  classical
  simp only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton _)]
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  simp only [← Finset.mul_sum]
  have hsum (p : Σ a, W a) :
      ∑ y : X, Set.indicator {True} (1 : Prop → ℝ≥0∞) (guess p = y) = 1 := by
    rw [Finset.sum_eq_single (guess p)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  simp only [hsum, mul_one]
  simp only [QuantumRuntime.matrix_jointPost]
  exact ((R.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le
    (ρ.prod R.init).posSemidef).trans (ENNReal.ofReal_le_one.mpr (ρ.prod R.init).trace_re_le_one)

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
      exact (Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ y)).trans
        (sum_evalDistMap_guess_le _ I x ρ guess)
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)

private theorem markedSearch_sum_le_of_isPointBound (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X (ZMod 2)) W A} {q Q : ℕ}
    (hq : x.IsTotalQueryBound q) (hQ : x.IsPointBound Q)
    (ρ : SubState A) (guess : (Σ a, W a) → X) :
    ∑ y, (parallelOracleRuntime (markedFunction y)).evalDistMap I x ρ
      (fun p ↦ guess p = y) {True} ≤
      (1 + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ)) ^ (2 : ℕ) := by
  classical
  let R := parallelOracleRuntime (0 : X → ZMod 2)
  let τ : SubState (A × R.D) := ρ.prod (SubState.basis ())
  let p (y : X) := (parallelOracleRuntime (markedFunction y)).evalDistMap I x ρ
    (fun p ↦ guess p = y) {True}
  let a (y : X) := R.evalDistMap I x ρ (fun p ↦ guess p = y) {True}
  let m (j : ℕ) (y : X) := 4 * R.queryWeight I (parallelInputWeight (D := R.D) {y}) x τ.matrix j
  have ha : ∑' y, a y ≤ 1 := by
    simpa only [tsum_fintype] using sum_evalDistMap_guess_le R I x ρ guess
  have hcut : ∀ j, q ≤ j → ∀ y, m j y = 0 := by
    intro j hj y
    dsimp only [m]
    rw [R.queryWeight_eq_zero_of_isTotalQueryBound I hq hj τ.matrix, mul_zero]
  have hm : ∑' j, ∑' y, m j y ≤ 4 * Q := by
    change (∑' j, ∑' y, 4 * R.queryWeight I
      (parallelInputWeight (D := R.D) {y}) x τ.matrix j) ≤ _
    simp only [ENNReal.tsum_mul_left, QuantumRuntime.tsum_queryWeight]
    change 4 * R.totalWeight I
      (fun i σ ↦ ∑' y : X, parallelInputWeight (D := R.D) {y} i σ) x τ.matrix ≤ _
    refine mul_le_mul le_rfl ?_ bot_le bot_le
    refine (R.totalWeight_le_of_isPointBound I ?_ hQ τ.posSemidef).trans ?_
    · intro ik σ hσ
      simpa only [tsum_fintype] using
        sum_parallelInputWeight_singleton_le (Y := ZMod 2) (D := R.D) ik hσ
    · exact mul_le_of_le_one_right (by positivity)
        (ENNReal.ofReal_le_one.mpr τ.trace_re_le_one)
  have hh (y : X) : p y ^ (2⁻¹ : ℝ) ≤ a y ^ (2⁻¹ : ℝ) +
      ∑' j, m j y ^ (2⁻¹ : ℝ) :=
    rpow_inv_two_evalDistMap_parallel_le_support I (markedFunction y) 0 {y}
      (fun z hz ↦ by
        simp only [Set.mem_singleton_iff] at hz
        simp [markedFunction, hz])
      x ρ (fun p ↦ guess p = y) (MeasurableSet.singleton True)
  have hroot := rpow_inv_two_tsum_le_of_le_add_tsum_of_cutoff p a m q hcut hh
  have hamp : (∑' y, p y) ^ (2⁻¹ : ℝ) ≤
      1 + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ) :=
    hroot.trans (add_le_add
      (by simpa using ENNReal.rpow_le_rpow ha (by norm_num : (0 : ℝ) ≤ 2⁻¹))
      (ENNReal.rpow_le_rpow (mul_le_mul le_rfl hm bot_le bot_le) (by norm_num)))
  have hsquare := ENNReal.rpow_le_rpow hamp (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = ((∑' y, p y) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) := by
      rw [rpow_inv_two_rpow_two, tsum_fintype]
    _ ≤ (1 + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) := hsquare
    _ = _ := ENNReal.rpow_two _

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
  have hconst : (1 : ℝ≥0∞) + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal (1 + 2 * Real.sqrt ((q : ℝ) * Q)) := by
    rw [show (q : ℝ≥0∞) * (4 * Q) = 4 * ((q : ℝ≥0∞) * Q) by ring,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have hfour : (4 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 2 := by
      rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 : ℕ) by norm_num,
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hfour, ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_rpow_inv_two,
      ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp
  calc
    _ ≤ (Fintype.card X : ℝ≥0∞)⁻¹ *
        (1 + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ)) ^ (2 : ℕ) :=
      mul_le_mul le_rfl (markedSearch_sum_le_of_isPointBound I hq hQ ρ guess) bot_le bot_le
    _ = _ := by
      rw [hconst, ← ENNReal.ofReal_pow (by positivity), div_eq_mul_inv, mul_comm]

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
