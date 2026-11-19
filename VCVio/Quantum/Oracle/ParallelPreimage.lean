/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable.Target
public import VCVio.Quantum.Oracle.ParallelFinding
import VCVio.Quantum.Oracle.Sequentialize

/-!
# Parallel preimage search in a random function

One uniform function serves every call. The target, program, local interpretation, initial
substate and input-guessing rule are fixed independently of that function. The adversary may
depend on the fixed target. Recovery means that the same sampled function sends the returned
input to the target; the target is not sampled by evaluating the function at a hidden input.

An avoiding reference table and an independent label table generate the random function.
The labels determine its target preimage, independently of the reference execution. The
sampled-set finding theorem therefore applies at incidence `1 / |Y|`. Singleton answer spaces
are handled by the unconditional probability cap rather than by an empty avoiding-table sampler.

## References

* C. Zalka, *Grover's quantum searching algorithm is optimal*, arXiv:quant-ph/9711070v2, §4.
* Chung, Fehr, Huang and Liao, *On the Compressed-Oracle Technique, and Post-Quantum Security
  of Proofs of Sequential Work*, arXiv:2010.11658v4, Example 5.18, for the fixed-target game.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Quantum

universe u v w

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Unconditional success at finding a preimage of a fixed target under one uniform function.
The verifier reads the same function that answered every parallel oracle call. -/
@[expose]
noncomputable def preimageSearchAdvantage (target : Y) (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (guess : (Σ B, W B) → X) : ℝ≥0∞ :=
  sampledEvalDistMap parallelOracleRuntime I x ρ
    (fun H leaf ↦ H (guess leaf) = target) {True}

/-- Preimage success is the uniform average of fixed-function success events. -/
theorem preimageSearchAdvantage_eq_sum (target : Y) (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (guess : (Σ B, W B) → X) :
    preimageSearchAdvantage target I x ρ guess =
      ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        (parallelOracleRuntime H).evalDistMap I x ρ
          (fun leaf ↦ H (guess leaf) = target) {True} := by
  rw [preimageSearchAdvantage,
    sampledEvalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True)]

/-- Missing mass remains failure, so preimage-search success is at most one. -/
theorem preimageSearchAdvantage_le_one (target : Y) (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (guess : (Σ B, W B) → X) : preimageSearchAdvantage target I x ρ guess ≤ 1 := by
  rw [preimageSearchAdvantage_eq_sum]
  calc
    _ ≤ ∑ _H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * 1 := by
      apply Finset.sum_le_sum
      intro H _
      exact mul_le_mul le_rfl (measure_le_one _ _) bot_le bot_le
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)

/-- A zero-point adversary guesses a fixed target with its successful execution mass
at any reference oracle divided by the answer-space size. Empty batches are permitted. -/
theorem preimageSearchAdvantage_eq_of_isPointBound_zero (target : Y) (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X Y) W A} (hQ : x.IsPointBound 0)
    (ρ : SubState A) (guess : (Σ B, W B) → X) (reference : X → Y) :
    preimageSearchAdvantage target I x ρ guess =
      (parallelOracleRuntime reference).evalDistMap I x ρ (fun _ ↦ ()) Set.univ /
        Fintype.card Y := by
  have hf : (fun (H : X → Y) (leaf : Σ B, W B) ↦ H (guess leaf) = target) =
      (fun H leaf ↦ target = H (guess leaf)) := by
    funext H leaf
    exact propext eq_comm
  rw [preimageSearchAdvantage, hf, ← qromEvalDistMap_sequentialize I x ρ,
    qromEvalDistMap_guess_zero .instruments (hQ.qrom_sequentialize I) ρ
      guess (fun _ ↦ target) reference,
    (additiveOracleRuntime reference).run_sequentialize I x,
    (parallelOracleRuntime reference).evalDistMap_apply_univ I x ρ (fun _ ↦ ())]
  rfl

/-- With zero queried points and lossless local execution, the guessing probability is the
initial adversary mass divided by the range cardinality. No round bound is needed. -/
theorem preimageSearchAdvantage_eq_of_isPointBound_zero_of_lossless
    (target : Y) (I : L.Interp) {x : QuantumComp L (qromBatchSpec X Y) W A}
    (hQ : x.IsPointBound 0) (hl : x.Lossless I) (ρ : SubState A)
    (guess : (Σ B, W B) → X) :
    preimageSearchAdvantage target I x ρ guess =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card Y := by
  rw [preimageSearchAdvantage_eq_of_isPointBound_zero target I hQ ρ guess 0,
    (parallelOracleRuntime (0 : X → Y)).evalDistMap_apply_univ I x ρ (fun _ ↦ ()),
    lossless_run_parallelOracleRuntime I hl 0
      (ρ.prod (parallelOracleRuntime (0 : X → Y)).init).matrix]
  have ht : (parallelOracleRuntime (0 : X → Y)).init.matrix.trace.re = 1 := by
    change (SubState.basis ()).matrix.trace.re = 1
    rw [SubState.trace_basis]
    rfl
  rw [SubState.trace_re_prod, ht, mul_one]

/-- Random-function preimage search under adaptive round and total-point bounds. The target
and complete adversary are fixed independently of the sampled function. There is no maximum
width restriction, no conditioning on the target having a preimage, and no renormalization
of failed executions. The guessing term applies even when no oracle call is made. -/
theorem preimageSearchAdvantage_le_of_isPointBound (target : Y) (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X Y) W A} {q Q : ℕ}
    (hq : x.IsTotalQueryBound q) (hQ : x.IsPointBound Q)
    (ρ : SubState A) (guess : (Σ B, W B) → X) :
    preimageSearchAdvantage target I x ρ guess ≤ min 1
      (ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) / Fintype.card Y) := by
  refine le_min (preimageSearchAdvantage_le_one target I x ρ guess) ?_
  by_cases hc : Nonempty {y : Y // y ≠ target}
  · let _ := hc
    let F (H : X → Y) (S : Set X) :=
      (parallelOracleRuntime H).evalDistMap I x ρ (fun leaf ↦ guess leaf ∈ S) {True}
    rw [preimageSearchAdvantage_eq_sum]
    change (∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * F H (H ⁻¹' {target})) ≤ _
    rw [average_targetPatch_with_preimage target F]
    have hw : ENNReal.ofReal ((Fintype.card (X → Y) : ℝ)⁻¹) =
        (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
        ENNReal.ofReal_natCast]
    have hδ : ENNReal.ofReal ((Fintype.card Y : ℝ)⁻¹) =
        (Fintype.card Y : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
        ENNReal.ofReal_natCast]
    have hb (base : X → {y : Y // y ≠ target}) :
        (∑ labels : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
          F (targetPatch target base labels) (labels ⁻¹' {target})) ≤
        ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) / Fintype.card Y := by
      have h := sum_mul_evalDistMap_mem_parallel_le_of_isPointBound I
        (fun z ↦ (base z : Y)) (targetPatch target base)
        (fun _ : X → Y ↦ (Fintype.card (X → Y) : ℝ)⁻¹) (fun _ ↦ by positivity)
        (fun labels ↦ labels ⁻¹' {target})
        (fun labels z hz ↦ targetPatch_eq_base_of_ne target base labels z hz)
        ((Fintype.card Y : ℝ)⁻¹) (by positivity)
        (fun z ↦ (sum_indicator_target_eq target z).le) hq hQ ρ guess
      simpa only [hw, hδ, div_eq_mul_inv, mul_comm] using h
    calc
      _ ≤ ∑ _base : X → {y : Y // y ≠ target},
          (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
            (ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) / Fintype.card Y) := by
        apply Finset.sum_le_sum
        intro base _
        exact mul_le_mul le_rfl (hb base) bot_le bot_le
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _), one_mul]
  · have hcard : Fintype.card Y = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨target, fun y ↦ ?_⟩
      by_contra hy
      exact hc ⟨⟨y, hy⟩⟩
    rw [hcard, Nat.cast_one, div_one]
    refine (preimageSearchAdvantage_le_one target I x ρ guess).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.sqrt_nonneg ((q : ℝ) * Q)]

/-- Random-function preimage search after at most `q` parallel rounds of width at most `k`.
The zero-query guessing term and unconditional probability cap are retained. -/
theorem preimageSearchAdvantage_le (target : Y) (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X Y) W A} {q k : ℕ}
    (hq : x.IsTotalQueryBound q) (hk : x.IsWidthBound k)
    (ρ : SubState A) (guess : (Σ B, W B) → X) :
    preimageSearchAdvantage target I x ρ guess ≤ min 1
      (ENNReal.ofReal ((1 + 2 * (q : ℝ) * Real.sqrt k) ^ 2) / Fintype.card Y) := by
  have h := preimageSearchAdvantage_le_of_isPointBound target I hq (hq.isPointBound hk) ρ guess
  have hsqrt : Real.sqrt ((q : ℝ) * ((k * q : ℕ) : ℝ)) = (q : ℝ) * Real.sqrt k := by
    rw [Nat.cast_mul, show (q : ℝ) * ((k : ℝ) * q) = (q : ℝ) ^ 2 * k by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  simpa only [hsqrt, mul_assoc] using h

end Quantum
