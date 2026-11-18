/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.ChargeWeight
public import VCVio.Quantum.Oracle.ParallelHybrid

/-!
# Finding a sampled disagreement set

A fixed reference oracle is independent of a sampled family of hidden input sets. A pointwise
weighted incidence bound controls both guessing in the reference execution and its total query
weight on those sets. The parallel hybrid argument then bounds finding a hidden set after adaptive
rounds with a pathwise total-point budget. Observers retain the same sampled set as the oracle.

## References

* C. Zalka, *Grover's quantum searching algorithm is optimal*, arXiv:quant-ph/9711070v2, §4.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal Kronecker

namespace Quantum

universe u v w

variable {X Y : Type} {Ω : Type*} [Fintype Ω]

private theorem sum_mul_indicator_mem_le (weights : Ω → ℝ) (hw : ∀ ω, 0 ≤ weights ω)
    (S : Ω → Set X) (δ : ℝ)
    (hS : ∀ z, ∑ ω, (S ω).indicator (fun _ ↦ weights ω) z ≤ δ) (z : X) :
    ∑ ω, ENNReal.ofReal (weights ω) *
      Set.indicator {True} (1 : Prop → ℝ≥0∞) (z ∈ S ω) ≤ ENNReal.ofReal δ := by
  classical
  have hn (ω : Ω) : 0 ≤ (S ω).indicator (fun _ ↦ weights ω) z := by
    by_cases hz : z ∈ S ω <;> simp [hz, hw]
  calc
    _ = ENNReal.ofReal (∑ ω, (S ω).indicator (fun _ ↦ weights ω) z) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ hn ω)]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hz : z ∈ S ω <;> simp [hz]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hS z)

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- A reference execution independent of the hidden set can guess membership only at the
weighted incidence rate. Its missing mass is not renormalized. -/
theorem sum_mul_evalDistMap_mem_le (R : QuantumRuntime (qromBatchSpec X Y))
    (I : L.Interp) (weights : Ω → ℝ) (hw : ∀ ω, 0 ≤ weights ω)
    (S : Ω → Set X) (δ : ℝ)
    (hS : ∀ z, ∑ ω, (S ω).indicator (fun _ ↦ weights ω) z ≤ δ)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (guess : (Σ B, W B) → X) :
    ∑ ω, ENNReal.ofReal (weights ω) *
      R.evalDistMap I x ρ (fun leaf ↦ guess leaf ∈ S ω) {True} ≤ ENNReal.ofReal δ := by
  classical
  simp only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True),
    ← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  calc
    _ ≤ ∑' leaf, ENNReal.ofReal (R.jointPost I x ρ leaf).matrix.trace.re * ENNReal.ofReal δ := by
      apply ENNReal.tsum_le_tsum
      intro leaf
      calc
        _ = ENNReal.ofReal (R.jointPost I x ρ leaf).matrix.trace.re *
            ∑ ω, ENNReal.ofReal (weights ω) *
              Set.indicator {True} (1 : Prop → ℝ≥0∞) (guess leaf ∈ S ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          ring
        _ ≤ _ := mul_le_mul le_rfl
          (sum_mul_indicator_mem_le weights hw S δ hS (guess leaf)) bot_le bot_le
    _ = (∑' leaf, ENNReal.ofReal (R.jointPost I x ρ leaf).matrix.trace.re) * ENNReal.ofReal δ :=
      ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_of_le_one_left (by positivity) (by
      simpa only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ MeasurableSet.univ,
        Set.indicator_univ, Pi.one_apply, mul_one] using
        measure_univ_le (R.evalDistMap I x ρ (fun _ ↦ ())))

/-- Averaging sampled input sets in one fixed execution preserves a total-point budget.
The reference runtime, program and input state are independent of the sampled set. -/
theorem tsum_sum_mul_queryWeight_parallelInputWeight_le_of_isPointBound
    (R : QuantumRuntime (qromBatchSpec X Y)) (I : L.Interp)
    (weights : Ω → ℝ) (hw : ∀ ω, 0 ≤ weights ω) (S : Ω → Set X)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ ω, (S ω).indicator (fun _ ↦ weights ω) z ≤ δ)
    {x : QuantumComp L (qromBatchSpec X Y) W A} {Q : ℕ} (hQ : x.IsPointBound Q)
    (ρ : SubState (A × R.D)) :
    ∑' j, ∑ ω, ENNReal.ofReal (weights ω) *
      R.queryWeight I (parallelInputWeight (D := R.D) (S ω)) x ρ.matrix j ≤
        ENNReal.ofReal δ * Q := by
  let avgWeight : ∀ i : (qromBatchSpec X Y).Port,
      Matrix ((qromBatchSpec X Y).In i × R.D) ((qromBatchSpec X Y).In i × R.D) ℂ → ℝ≥0∞ :=
    fun i σ ↦ ∑ ω, ENNReal.ofReal (weights ω) *
    parallelInputWeight (D := R.D) (S ω) i σ
  have he (j : ℕ) :
      (∑ ω, ENNReal.ofReal (weights ω) * R.queryWeight I
        (parallelInputWeight (D := R.D) (S ω)) x ρ.matrix j) =
        R.queryWeight I avgWeight x ρ.matrix j := by
    simp only [← QuantumRuntime.queryWeight_const_mul]
    simpa only [tsum_fintype] using R.tsum_queryWeight I
      (fun ω i σ ↦ ENNReal.ofReal (weights ω) * parallelInputWeight (D := R.D) (S ω) i σ)
      x ρ.matrix j
  calc
    _ = R.totalWeight I avgWeight x ρ.matrix := by simp only [QuantumRuntime.totalWeight, he]
    _ ≤ ∑' j, R.queryWeight I
        (fun i σ ↦ ENNReal.ofReal δ * (i.2 * ENNReal.ofReal σ.trace.re)) x ρ.matrix j := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply R.queryWeight_mono I _ x ρ.posSemidef j
      intro i σ hσ
      exact (sum_mul_parallelInputWeight_le weights hw S δ hδ hS i hσ).trans_eq (by ring)
    _ = ENNReal.ofReal δ * R.totalWeight I
        (fun i σ ↦ i.2 * ENNReal.ofReal σ.trace.re) x ρ.matrix := by
      simp only [QuantumRuntime.totalWeight, QuantumRuntime.queryWeight_const_mul,
        ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal δ * (Q * ENNReal.ofReal ρ.matrix.trace.re) := by
      apply mul_le_mul le_rfl _ bot_le bot_le
      exact R.totalWeight_le_of_isPointBound I (fun _ _ _ ↦ le_rfl) hQ ρ.posSemidef
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_of_le_one_right (by positivity)
        (ENNReal.ofReal_le_one.mpr ρ.trace_re_le_one)

variable [AddCommGroup Y]

private theorem one_add_query_root_eq (q Q : ℕ) :
    (1 : ℝ≥0∞) + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ) =
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

/-- Finding a sampled hidden set after adaptive parallel calls. A single reference oracle,
program, initial state and guess are held fixed across the sampled sets. The incidence
hypothesis supplies the guessing rate and the expected query-union weight. The weights need
not be normalized; the conclusion is an unconditional weighted sum of success probabilities. -/
theorem sum_mul_evalDistMap_mem_parallel_le_of_isPointBound
    (I : L.Interp) (reference : X → Y) (oracles : Ω → X → Y)
    (weights : Ω → ℝ) (hw : ∀ ω, 0 ≤ weights ω) (S : Ω → Set X)
    (hsupport : ∀ ω z, z ∉ S ω → oracles ω z = reference z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ ω, (S ω).indicator (fun _ ↦ weights ω) z ≤ δ)
    {x : QuantumComp L (qromBatchSpec X Y) W A} {q Q : ℕ}
    (hq : x.IsTotalQueryBound q) (hQ : x.IsPointBound Q)
    (ρ : SubState A) (guess : (Σ B, W B) → X) :
    ∑ ω, ENNReal.ofReal (weights ω) *
      (parallelOracleRuntime (oracles ω)).evalDistMap I x ρ
        (fun leaf ↦ guess leaf ∈ S ω) {True} ≤
      ENNReal.ofReal δ * ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) := by
  classical
  let R := parallelOracleRuntime reference
  let τ : SubState (A × R.D) := ρ.prod (SubState.basis ())
  let c (ω : Ω) := ENNReal.ofReal (weights ω)
  let p (ω : Ω) := c ω * (parallelOracleRuntime (oracles ω)).evalDistMap I x ρ
    (fun leaf ↦ guess leaf ∈ S ω) {True}
  let a (ω : Ω) := c ω * R.evalDistMap I x ρ (fun leaf ↦ guess leaf ∈ S ω) {True}
  let m (j : ℕ) (ω : Ω) := c ω *
    (4 * R.queryWeight I (parallelInputWeight (D := R.D) (S ω)) x τ.matrix j)
  have ha : ∑' ω, a ω ≤ ENNReal.ofReal δ := by
    simpa only [tsum_fintype] using sum_mul_evalDistMap_mem_le R I weights hw S δ hS x ρ guess
  have hcut : ∀ j, q ≤ j → ∀ ω, m j ω = 0 := by
    intro j hj ω
    dsimp only [m]
    rw [R.queryWeight_eq_zero_of_isTotalQueryBound I hq hj τ.matrix, mul_zero, mul_zero]
  have hm : ∑' j, ∑' ω, m j ω ≤ 4 * (ENNReal.ofReal δ * Q) := by
    calc
      _ = 4 * ∑' j, ∑ ω, c ω *
          R.queryWeight I (parallelInputWeight (D := R.D) (S ω)) x τ.matrix j := by
        simp only [m, tsum_fintype, ← ENNReal.tsum_mul_left, Finset.mul_sum]
        apply tsum_congr
        intro j
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ _ := mul_le_mul le_rfl
        (tsum_sum_mul_queryWeight_parallelInputWeight_le_of_isPointBound
          R I weights hw S δ hδ hS hQ τ) bot_le bot_le
  have hh (ω : Ω) : p ω ^ (2⁻¹ : ℝ) ≤ a ω ^ (2⁻¹ : ℝ) +
      ∑' j, m j ω ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_evalDistMap_parallel_le_support I (oracles ω) reference (S ω)
      (hsupport ω) x ρ (fun leaf ↦ guess leaf ∈ S ω) (MeasurableSet.singleton True)
    calc
      _ = c ω ^ (2⁻¹ : ℝ) *
          (parallelOracleRuntime (oracles ω)).evalDistMap I x ρ
            (fun leaf ↦ guess leaf ∈ S ω) {True} ^ (2⁻¹ : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ c ω ^ (2⁻¹ : ℝ) * (R.evalDistMap I x ρ
          (fun leaf ↦ guess leaf ∈ S ω) {True} ^ (2⁻¹ : ℝ) +
            ∑' j, (4 * R.queryWeight I (parallelInputWeight (D := R.D) (S ω))
              x τ.matrix j) ^ (2⁻¹ : ℝ)) := mul_le_mul le_rfl h bot_le bot_le
      _ = _ := by
        simp only [a, m, mul_add, ENNReal.tsum_mul_left,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have hroot := rpow_inv_two_tsum_le_of_le_add_tsum_of_cutoff p a m q hcut hh
  have hamp : (∑' ω, p ω) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal δ ^ (2⁻¹ : ℝ) *
        (1 + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ)) := by
    refine hroot.trans ((add_le_add
      (ENNReal.rpow_le_rpow ha (by norm_num : (0 : ℝ) ≤ 2⁻¹))
      (ENNReal.rpow_le_rpow (mul_le_mul le_rfl hm bot_le bot_le) (by norm_num))).trans_eq ?_)
    rw [show (q : ℝ≥0∞) * (4 * (ENNReal.ofReal δ * Q)) =
        ENNReal.ofReal δ * ((q : ℝ≥0∞) * (4 * Q)) by ring,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    ring
  have hsquare := ENNReal.rpow_le_rpow hamp (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = ((∑' ω, p ω) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) := by
      rw [rpow_inv_two_rpow_two, tsum_fintype]
    _ ≤ (ENNReal.ofReal δ ^ (2⁻¹ : ℝ) *
        (1 + ((q : ℝ≥0∞) * (4 * Q)) ^ (2⁻¹ : ℝ))) ^ (2 : ℝ) := hsquare
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), rpow_inv_two_rpow_two,
        one_add_query_root_eq, ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]

end Quantum
