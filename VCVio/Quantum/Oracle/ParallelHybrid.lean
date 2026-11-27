/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.HybridBudget
public import VCVio.Quantum.Oracle.ParallelReprogramming

/-!
# Parallel-oracle hybrids for adaptive programs

Two fixed functions are compared by the square-root hybrid argument on their batched
runtimes. Query weights are charged to a designated reference execution, which permits a
reference independent of hidden reprogramming points. Their one-round disagreement weights
are bounded by the mass on the union of slots querying the disagreement set.

Local operations may be arbitrary instruments, including measurements and loss. The program,
interpretation, initial state and final observation are common to the two executions.
-/

public section

open Matrix MeasureTheory
open scoped ENNReal ComplexOrder Kronecker

universe u v w

namespace Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The weight of a parallel query on the union of slots with input in `S`. -/
@[expose]
noncomputable def parallelInputWeight {D : QReg} (S : Set X) (ik : Unit × ℕ)
    (σ : Matrix ((qromBatchSpec X Y).In ik × D) ((qromBatchSpec X Y).In ik × D) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (MatrixMap.conj (parallelInputProjector (Y := Y) ik.2 S ⊗ₖ
    (1 : Matrix D D ℂ)) σ).trace.re

/-- Summed over all possible marked inputs, the union-query weight is bounded by one input
trace per slot. Repeated inputs and width zero satisfy the same estimate. -/
theorem sum_parallelInputWeight_singleton_le {D : QReg} (ik : Unit × ℕ)
    {σ : Matrix ((qromBatchSpec X Y).In ik × D) ((qromBatchSpec X Y).In ik × D) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ y : X, parallelInputWeight (Y := Y) (D := D) {y} ik σ ≤
      ik.2 * ENNReal.ofReal σ.trace.re := by
  classical
  simp only [parallelInputWeight]
  have hn : ∀ y : X, 0 ≤ (MatrixMap.conj
      (parallelInputProjector (Y := Y) ik.2 {y} ⊗ₖ (1 : Matrix D D ℂ)) σ).trace.re :=
    fun _ ↦ (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ hn y)]
  have hc := sum_re_trace_conj_parallelInputProjector_singleton_frame_le ik.2 hσ
  calc
    _ ≤ ENNReal.ofReal ((ik.2 : ℝ) * σ.trace.re) := ENNReal.ofReal_le_ofReal hc
    _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Weighted incidence of a sampled disagreement set bounds its mean parallel-query
weight. The input state is held fixed across the sampled sets. -/
theorem sum_mul_parallelInputWeight_le {Ω : Type*} [Fintype Ω] {D : QReg}
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set X) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ ω, Set.indicator (S ω) (fun _ ↦ w ω) z ≤ δ)
    (i : Unit × ℕ) {σ : Matrix ((qromBatchSpec X Y).In i × D)
      ((qromBatchSpec X Y).In i × D) ℂ} (hσ : σ.PosSemidef) :
    ∑ ω, ENNReal.ofReal (w ω) * parallelInputWeight (D := D) (Y := Y) (S ω) i σ ≤
      (i.2 : ℝ≥0∞) * ENNReal.ofReal δ * ENNReal.ofReal σ.trace.re := by
  simp only [parallelInputWeight, ← ENNReal.ofReal_mul (hw _)]
  have hn (ω : Ω) : 0 ≤ w ω * (MatrixMap.conj
      (parallelInputProjector (Y := Y) i.2 (S ω) ⊗ₖ (1 : Matrix D D ℂ)) σ).trace.re :=
    mul_nonneg (hw ω) ((hσ.mul_mul_conjTranspose_same _).trace_re_nonneg)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ hn ω)]
  calc
    _ ≤ ENNReal.ofReal ((i.2 : ℝ) * δ * σ.trace.re) := ENNReal.ofReal_le_ofReal
      (sum_mul_re_trace_conj_parallelInputProjector_frame_le w hw S δ hS i.2 hσ)
    _ = _ := by rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hδ),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

variable [AddCommGroup Y]

/-- The sole Kraus operator of a parallel oracle call, with arbitrary spectator memory. -/
@[expose]
def parallelOracleKraus {D : QReg} (H : X → Y) (ik : Unit × ℕ) (_ : Unit) :
    Matrix ((qromBatchSpec X Y).Out ik × D) ((qromBatchSpec X Y).In ik × D) ℂ :=
  parallelOracleUnitary H ik.2 ⊗ₖ (1 : Matrix D D ℂ)

/-- A parallel runtime branch is conjugation by its simultaneous oracle Kraus operator. -/
theorem branch_parallelOracleRuntime (H : X → Y) (ik : Unit × ℕ) (r : Unit) :
    ((parallelOracleRuntime H).step ik).branch r =
      MatrixMap.conj (parallelOracleKraus (D := (parallelOracleRuntime H).D) H ik r) := by
  rcases ik with ⟨⟨⟩, k⟩
  rw [parallelOracleRuntime_step, DSubInstrument.branch_frame_apply,
    branch_parallelOracleQuery, MatrixMap.amplify_conj]
  rfl

/-- The squared Kraus weight of the difference between two parallel oracle calls. -/
@[expose]
noncomputable def parallelDisagreementWeight {D : QReg} (H H' : X → Y) (ik : Unit × ℕ)
    (σ : Matrix ((qromBatchSpec X Y).In ik × D) ((qromBatchSpec X Y).In ik × D) ℂ) : ℝ≥0∞ :=
  QuantumRuntime.krausWeight (spec := qromBatchSpec X Y) (D := D)
    (fun i r ↦ parallelOracleKraus (D := D) H i r - parallelOracleKraus (D := D) H' i r)
    ik σ

/-- A one-round disagreement has weight at most four times the union-query weight. -/
theorem parallelDisagreementWeight_le {D : QReg} (H H' : X → Y) (S : Set X)
    (h : ∀ x ∉ S, H x = H' x) (ik : Unit × ℕ)
    {σ : Matrix ((qromBatchSpec X Y).In ik × D) ((qromBatchSpec X Y).In ik × D) ℂ}
    (hσ : σ.PosSemidef) :
    parallelDisagreementWeight (D := D) H H' ik σ ≤
      4 * parallelInputWeight (D := D) S ik σ := by
  simp only [parallelDisagreementWeight, QuantumRuntime.krausWeight, tsum_fintype,
    Finset.univ_unique, Finset.sum_singleton]
  have hdiff : parallelOracleKraus (D := D) H ik () - parallelOracleKraus (D := D) H' ik () =
      (parallelOracleUnitary H ik.2 - parallelOracleUnitary H' ik.2) ⊗ₖ
        (1 : Matrix D D ℂ) := by
    ext ⟨a, c⟩ ⟨b, d⟩
    simp [parallelOracleKraus, kroneckerMap_apply, sub_mul]
  rw [hdiff]
  rw [parallelInputWeight, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  exact ENNReal.ofReal_le_ofReal (re_trace_parallel_disagreement_le H H' ik.2 S h hσ)

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The square-root event hybrid for parallel oracle calls, charging the Kraus differences
to the execution with `H'`. The final observation is common to both executions. -/
theorem rpow_inv_two_evalDistMap_parallel_le {γ : Type*} [MeasurableSpace γ]
    (I : L.Interp) (H H' : X → Y) (x : QuantumComp L (qromBatchSpec X Y) W A)
    (ρ : SubState A) (f : (Σ B, W B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (parallelOracleRuntime H).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (parallelOracleRuntime H').evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (parallelOracleRuntime H').queryWeight I
          (parallelDisagreementWeight (D := (parallelOracleRuntime H').D) H' H) x
          (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) j ^ (2⁻¹ : ℝ) := by
  let U := fun (ik : (qromBatchSpec X Y).Port) (r : Unit) ↦
    parallelOracleKraus (D := QReg.of Unit) H' ik r
  let V := fun (ik : (qromBatchSpec X Y).Port) (r : Unit) ↦
    parallelOracleKraus (D := QReg.of Unit) H ik r
  exact QuantumRuntime.rpow_inv_two_outcomeLawWith_le'
    (spec := qromBatchSpec X Y) (D := QReg.of Unit)
    (s₀ := (parallelOracleRuntime H').step) (s₁ := (parallelOracleRuntime H).step)
    (U := U) (W := V) I (SubState.basis ())
    (branch_parallelOracleRuntime H') (branch_parallelOracleRuntime H) x ρ f hs

/-- The parallel event hybrid charged to the reference execution's mass on slots whose
inputs lie in the disagreement set. Repeated inputs contribute only once to this union. -/
theorem rpow_inv_two_evalDistMap_parallel_le_support {γ : Type*} [MeasurableSpace γ]
    (I : L.Interp) (H H' : X → Y) (S : Set X) (h : ∀ x ∉ S, H x = H' x)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (f : (Σ B, W B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (parallelOracleRuntime H).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (parallelOracleRuntime H').evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * (parallelOracleRuntime H').queryWeight I
          (parallelInputWeight (D := (parallelOracleRuntime H').D) S) x
          (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) j) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_evalDistMap_parallel_le I H H' x ρ f hs).trans (add_le_add le_rfl ?_)
  refine tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [← QuantumRuntime.queryWeight_const_mul]
  exact QuantumRuntime.queryWeight_mono _ I
    (fun ik σ hσ ↦ parallelDisagreementWeight_le H' H S (fun x hx ↦ (h x hx).symm) ik hσ)
    x (ρ.prod (SubState.basis ())).posSemidef j

end Quantum
