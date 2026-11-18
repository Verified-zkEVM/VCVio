/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ParallelFinding
public import VCVio.Quantum.Comp.Finisher
public import VCVio.Quantum.Oracle.LocalExecution
public import VCVio.Quantum.Foundations.SubState

/-!
# Parallel reprogramming before a common finisher

A hidden challenge can determine the continuation and acceptance event after preprocessing.
Only the oracle-query prefix must be independent of the fresh disagreement set. Oracle-free
suffixes preserve its query weights, allowing averaged incidence and round/point bounds to
control the change of the complete experiment. The challenge is retained in the final event.
-/

public section
open Matrix MeasureTheory
open scoped ENNReal Kronecker
namespace Quantum
universe u v w w₁
variable {X Y : Type} {Ω : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Ω] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {V : QReg → Type w₁} {A : QReg}

/-- Averaged root hybrid for a fixed oracle-query prefix followed by a common oracle-free
finisher for each sampled challenge. The finisher and final observation may depend on the
challenge; the reference prefix state does not. The nonnegative weights need not normalize. -/
theorem rpow_inv_two_sum_mul_evalDistMap_bind_parallel_le
    (I : L.Interp) (reference : X → Y) (oracles : Ω → X → Y)
    (weights : Ω → ℝ) (hw : ∀ ω, 0 ≤ weights ω) (S : Ω → Set X)
    (hsupport : ∀ ω z, z ∉ S ω → oracles ω z = reference z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ ω, (S ω).indicator (fun _ ↦ weights ω) z ≤ δ)
    {pre : QuantumComp L (qromBatchSpec X Y) W A} {r Q : ℕ}
    (hr : pre.IsTotalQueryBound r) (hQ : pre.IsPointBound Q)
    (finish : Ω → ∀ B, W B → QuantumComp L (qromBatchSpec X Y) V B)
    (hfinish : ∀ ω B b, (finish ω B b).IsTotalQueryBound 0)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : Ω → (Σ B, V B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (∑ ω, ENNReal.ofReal (weights ω) *
      (parallelOracleRuntime (oracles ω)).evalDistMap I (pre.bind (finish ω)) ρ (f ω) s)
        ^ (2⁻¹ : ℝ) ≤
      (∑ ω, ENNReal.ofReal (weights ω) *
        (parallelOracleRuntime reference).evalDistMap I (pre.bind (finish ω)) ρ (f ω) s)
          ^ (2⁻¹ : ℝ) +
      2 * ((r : ℝ≥0∞) * Q * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
  classical
  let R := parallelOracleRuntime reference
  let τ : SubState (A × R.D) := ρ.prod (SubState.basis ())
  let c (ω : Ω) := ENNReal.ofReal (weights ω)
  let p (ω : Ω) := c ω * (parallelOracleRuntime (oracles ω)).evalDistMap I
    (pre.bind (finish ω)) ρ (f ω) s
  let a (ω : Ω) := c ω * R.evalDistMap I (pre.bind (finish ω)) ρ (f ω) s
  let m (j : ℕ) (ω : Ω) := c ω *
    (4 * R.queryWeight I (parallelInputWeight (D := R.D) (S ω)) pre τ.matrix j)
  have hcut : ∀ j, r ≤ j → ∀ ω, m j ω = 0 := by
    intro j hj ω
    dsimp only [m]
    rw [R.queryWeight_eq_zero_of_isTotalQueryBound I hr hj τ.matrix, mul_zero, mul_zero]
  have hm : ∑' j, ∑' ω, m j ω ≤ 4 * (ENNReal.ofReal δ * Q) := by
    calc
      _ = 4 * ∑' j, ∑ ω, c ω *
          R.queryWeight I (parallelInputWeight (D := R.D) (S ω)) pre τ.matrix j := by
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
      (hsupport ω) (pre.bind (finish ω)) ρ (f ω) hs
    simp_rw [QuantumRuntime.queryWeight_bind_of_isTotalQueryBound_zero
      (parallelOracleRuntime reference) I
      (parallelInputWeight (D := (parallelOracleRuntime reference).D) (S ω))
      pre (finish ω) (hfinish ω)] at h
    calc
      _ = c ω ^ (2⁻¹ : ℝ) *
          (parallelOracleRuntime (oracles ω)).evalDistMap I
            (pre.bind (finish ω)) ρ (f ω) s ^ (2⁻¹ : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ c ω ^ (2⁻¹ : ℝ) * (R.evalDistMap I
          (pre.bind (finish ω)) ρ (f ω) s ^ (2⁻¹ : ℝ) +
            ∑' j, (4 * R.queryWeight I (parallelInputWeight (D := R.D) (S ω))
              pre τ.matrix j) ^ (2⁻¹ : ℝ)) := mul_le_mul le_rfl h bot_le bot_le
      _ = _ := by
        simp only [a, m, mul_add, ENNReal.tsum_mul_left,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have hroot := rpow_inv_two_tsum_le_of_le_add_tsum_of_cutoff p a m r hcut hh
  have herr : ((r : ℝ≥0∞) * (4 * (ENNReal.ofReal δ * Q))) ^ (2⁻¹ : ℝ) =
      2 * ((r : ℝ≥0∞) * Q * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
    rw [show (r : ℝ≥0∞) * (4 * (ENNReal.ofReal δ * Q)) =
        4 * ((r : ℝ≥0∞) * Q * ENNReal.ofReal δ) by ring,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have hfour : (4 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 2 := by
      rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 : ℕ) by norm_num,
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hfour]
  simpa only [p, a, tsum_fintype, herr] using
    hroot.trans (add_le_add le_rfl
      (ENNReal.rpow_le_rpow (mul_le_mul le_rfl hm bot_le bot_le) (by norm_num)))

/-- Event hybrid for a query-bounded prefix and challenge-dependent common finisher.
The weight sum is at most one, so both compared weighted events have subprobability mass. -/
theorem sum_mul_evalDistMap_bind_parallel_le
    (I : L.Interp) (reference : X → Y) (oracles : Ω → X → Y)
    (weights : Ω → ℝ) (hw : ∀ ω, 0 ≤ weights ω)
    (hnorm : ∑ ω, ENNReal.ofReal (weights ω) ≤ 1) (S : Ω → Set X)
    (hsupport : ∀ ω z, z ∉ S ω → oracles ω z = reference z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ ω, (S ω).indicator (fun _ ↦ weights ω) z ≤ δ)
    {pre : QuantumComp L (qromBatchSpec X Y) W A} {r Q : ℕ}
    (hr : pre.IsTotalQueryBound r) (hQ : pre.IsPointBound Q)
    (finish : Ω → ∀ B, W B → QuantumComp L (qromBatchSpec X Y) V B)
    (hfinish : ∀ ω B b, (finish ω B b).IsTotalQueryBound 0)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : Ω → (Σ B, V B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (∑ ω, ENNReal.ofReal (weights ω) *
      (parallelOracleRuntime (oracles ω)).evalDistMap I (pre.bind (finish ω)) ρ (f ω) s) ≤
      (∑ ω, ENNReal.ofReal (weights ω) *
        (parallelOracleRuntime reference).evalDistMap I (pre.bind (finish ω)) ρ (f ω) s) +
      4 * ((r : ℝ≥0∞) * Q * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
  have hmass (H : Ω → X → Y) :
      ∑ ω, ENNReal.ofReal (weights ω) *
        (parallelOracleRuntime (H ω)).evalDistMap I (pre.bind (finish ω)) ρ (f ω) s ≤ 1 := by
    calc
      _ ≤ ∑ ω, ENNReal.ofReal (weights ω) * 1 := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul le_rfl (measure_le_one _ _) bot_le bot_le
      _ ≤ 1 := by simpa only [mul_one] using hnorm
  have h := le_add_two_mul_of_rpow_inv_two_le (hmass oracles) (hmass fun _ ↦ reference)
    (rpow_inv_two_sum_mul_evalDistMap_bind_parallel_le
      I reference oracles weights hw S hsupport δ hδ hS hr hQ
      finish hfinish ρ f hs)
  simpa only [← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num] using h

/-! ## Complete continuations under a fixed oracle -/

/-- The retained preprocessing branches have total successful mass at most one. No branch is
renormalized and no bound is imposed on its retained register or classical output. -/
theorem tsum_mass_reducedPost_parallel_le_one (I : L.Interp) (H : X → Y)
    (pre : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) :
    ∑' leaf : Σ B, W B, ((parallelOracleRuntime H).reducedPost I pre ρ leaf).mass ≤ 1 := by
  change ∑' leaf : Σ B, W B,
    ((parallelOracleRuntime H).jointPost I pre ρ leaf).traceRight.mass ≤ 1
  simp only [SubState.mass_traceRight]
  have h := measure_univ_le ((parallelOracleRuntime H).evalDistMap I pre ρ (fun _ ↦ ()))
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ MeasurableSet.univ] at h
  simpa only [SubState.mass, Set.indicator_univ, Pi.one_apply, mul_one] using h

private theorem observed_parallelRunUnit_eq {Out γ : Type} [MeasurableSpace γ]
    {M : QReg} (H₀ H₁ : X → Y)
    (online : QuantumComp LocalSig.instruments (qromBatchSpec X Y) (fun _ ↦ Out) M)
    (σ : SubState (M × Unit)) (f : Out → γ) (s : Set γ) :
    letI : MeasurableSpace (Σ _B : QReg, Out) := ⊤
    ((((parallelOracleRuntime H₀).run .instruments
      (QuantumComp.localObservation (parallelRunUnit .instruments H₁ online))).outcomeMeasure σ).map
        (fun leaf ↦ f leaf.2)) s =
      (parallelOracleRuntime H₁).evalDistMap .instruments online σ.traceRight
        (fun leaf ↦ f leaf.2) s := by
  let : MeasurableSpace Out := ⊤
  let : MeasurableSpace (Σ _B : QReg, Out) := ⊤
  have h := map_outcomeMeasure_parallel_localObservation H₀
    (parallelRunUnit .instruments H₁ online) σ
  have hm := congrArg (fun μ : Measure Out ↦ μ.map f) h
  have he := (Measure.map_map Measurable.of_discrete Measurable.of_discrete).symm.trans
    (hm.trans (Measure.map_map Measurable.of_discrete Measurable.of_discrete))
  refine (congrArg (fun μ : Measure γ ↦ μ s) he).trans ?_
  rw [QuantumRuntime.evalDistMap_eq_map_evalDist _ _ _ _ _ Measurable.of_discrete]
  change (((parallelRunUnit .instruments H₁ online).outcomeMeasure σ).map
    (fun leaf ↦ f leaf.2)) s =
      (((parallelRunUnit .instruments H₁ online).outcomeMeasure
        (σ.traceRight.prod (SubState.basis ()))).map (fun leaf ↦ f leaf.2)) s
  exact congrArg (fun τ : SubState (M × Unit) ↦
    (((parallelRunUnit .instruments H₁ online).outcomeMeasure τ).map
      (fun leaf ↦ f leaf.2)) s) σ.prod_traceRight_basis_unit.symm

/-- Localizing the complete continuation preserves its observed output law on each actual
retained prefix state. The prefix and continuation may use different fixed raw oracles. -/
theorem evalDistMap_bind_parallelLocalObservation {Out γ : Type} [MeasurableSpace γ]
    (H₀ H₁ : X → Y)
    (pre : QuantumComp LocalSig.instruments (qromBatchSpec X Y) W A)
    (online : ∀ M, W M → QuantumComp LocalSig.instruments
      (qromBatchSpec X Y) (fun _ ↦ Out) M)
    (ρ : SubState A) (f : Out → γ) (s : Set γ) (hs : MeasurableSet s) :
    (parallelOracleRuntime H₀).evalDistMap .instruments
      (pre.bind fun M state ↦ QuantumComp.localObservation
        (parallelRunUnit .instruments H₁ (online M state))) ρ (fun leaf ↦ f leaf.2) s =
      ∑' leaf : Σ M, W M,
        (parallelOracleRuntime H₁).evalDistMap .instruments (online leaf.1 leaf.2)
          ((parallelOracleRuntime H₀).reducedPost .instruments pre ρ leaf)
          (fun out ↦ f out.2) s := by
  rw [QuantumRuntime.evalDistMap_bind, Measure.sum_apply _ hs]
  exact tsum_congr fun leaf ↦ observed_parallelRunUnit_eq H₀ H₁ (online leaf.1 leaf.2) _ f s

/-- For one fixed oracle, localizing a continuation leaves the complete prefix/continuation
experiment unchanged. It preserves the actual retained prefix state supplied to the continuation. -/
theorem evalDistMap_bind_same_parallelLocalObservation {Out γ : Type} [MeasurableSpace γ]
    (H : X → Y)
    (pre : QuantumComp LocalSig.instruments (qromBatchSpec X Y) W A)
    (online : ∀ M, W M → QuantumComp LocalSig.instruments
      (qromBatchSpec X Y) (fun _ ↦ Out) M)
    (ρ : SubState A) (f : Out → γ) (s : Set γ) (hs : MeasurableSet s) :
    (parallelOracleRuntime H).evalDistMap .instruments
      (pre.bind fun M state ↦ QuantumComp.localObservation
        (parallelRunUnit .instruments H (online M state))) ρ (fun leaf ↦ f leaf.2) s =
      (parallelOracleRuntime H).evalDistMap .instruments (pre.bind online) ρ
        (fun leaf ↦ f leaf.2) s := by
  let : MeasurableSpace (Σ _B : QReg, Out) := ⊤
  rw [evalDistMap_bind_parallelLocalObservation H H pre online ρ f s hs,
    QuantumRuntime.evalDistMap_bind, Measure.sum_apply _ hs]
  symm
  apply tsum_congr
  intro leaf
  rw [QuantumRuntime.evalDistMap_eq_map_evalDist _ _ _ _ _ Measurable.of_discrete]
  let σ : SubState (leaf.1 × Unit) :=
    (parallelOracleRuntime H).jointPost .instruments pre ρ leaf
  change (((parallelRunUnit .instruments H (online leaf.1 leaf.2)).outcomeMeasure σ).map
    (fun out ↦ f out.2)) s =
      (((parallelRunUnit .instruments H (online leaf.1 leaf.2)).outcomeMeasure
        (σ.traceRight.prod (SubState.basis ()))).map (fun out ↦ f out.2)) s
  exact congrArg (fun τ : SubState (leaf.1 × Unit) ↦
    (((parallelRunUnit .instruments H (online leaf.1 leaf.2)).outcomeMeasure τ).map
      (fun out ↦ f out.2)) s) σ.prod_traceRight_basis_unit.symm

end Quantum
