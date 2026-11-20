/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable.PlantedTarget
public import VCVio.Quantum.Oracle.ParallelFinding

/-!
# Parallel inversion of a random function at a hidden input

The challenger samples one uniform function and one independent uniform secret input, then
publishes the function's value at that input. The complete adversary may depend on this public
target. It wins by returning any preimage, rather than necessarily the hidden input itself.
The same sampled function serves every call and the final check. There is no preprocessing or
oracle-dependent advice, and missing execution mass remains failure.

An exact table coupling plants the target at the secret input and selects all other preimages
by independent labels. The sampled-set finding theorem applies to their union at density
`ProbabilityTheory.plantedTargetDensity`, including its zero-query guessing contribution.

## References

* `docs/quantum/reference/literature.md`, “Search-calibrated security bits”, states the
  normalization and the planted-preimage density.
* C. Zalka, *Grover's quantum searching algorithm is optimal*, arXiv:quant-ph/9711070v2, §4.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Quantum

universe u v w

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- All adversary choices are indexed by the public target. This family is fixed before the
random function and secret input are sampled, so it carries no oracle-dependent advice. -/
structure PlantedPreimageAdversary (X Y : Type) [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (L : LocalSig.{u, v}) (W : QReg → Type w) (A : QReg) where
  /-- Local operations selected from the public target. -/
  interp : Y → L.Interp
  /-- Parallel program selected from the public target. -/
  program : Y → QuantumComp L (qromBatchSpec X Y) W A
  /-- Initial substate selected by the public target, with no additional oracle-dependent advice. -/
  initial : Y → SubState A
  /-- A returned input, which need not be the challenger's hidden input. -/
  guess : Y → (Σ B, W B) → X

variable [AddCommGroup Y]

/-- Unconditional preimage recovery when the target is the image of an independent uniform
secret input. The verifier uses the same function as the adversary's parallel oracle. -/
@[expose]
noncomputable def plantedPreimageAdvantage
    (adv : PlantedPreimageAdversary X Y L W A) : ℝ≥0∞ :=
  ∑ secret : X, (Fintype.card X : ℝ≥0∞)⁻¹ *
    ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
      (parallelOracleRuntime H).evalDistMap (adv.interp (H secret))
        (adv.program (H secret)) (adv.initial (H secret))
        (fun leaf ↦ H (adv.guess (H secret) leaf) = H secret) {True}

/-- Missing mass counts as failure, so hidden-input inversion succeeds with probability at most
one. This does not assume lossless local operations or normalized initial states. -/
theorem plantedPreimageAdvantage_le_one [Nonempty X] (adv : PlantedPreimageAdversary X Y L W A) :
    plantedPreimageAdvantage adv ≤ 1 := by
  unfold plantedPreimageAdvantage
  calc
    _ ≤ ∑ _secret : X, (Fintype.card X : ℝ≥0∞)⁻¹ *
        ∑ _H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * 1 := by
      apply Finset.sum_le_sum
      intro secret _
      apply mul_le_mul le_rfl _ bot_le bot_le
      apply Finset.sum_le_sum
      intro H _
      exact mul_le_mul le_rfl (measure_le_one _ _) bot_le bot_le
    _ = 1 := by
      simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), mul_one,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _)]

/-- The full game equals an avoiding-base execution with the target planted at a hidden input.
The secret and extra target-labelled cells remain joint with the final success event. -/
theorem plantedPreimageAdvantage_eq_plantedTargetPatch
    (adv : PlantedPreimageAdversary X Y L W A)
    (hcompl : ∀ target : Y, Nonempty {y : Y // y ≠ target}) :
    plantedPreimageAdvantage adv =
      ∑ target : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
        ∑ base : X → {y : Y // y ≠ target},
          (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
            ∑ sample : X × (X → Y),
              ((Fintype.card X : ℝ≥0∞)⁻¹ * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹) *
                (parallelOracleRuntime (plantedTargetPatch target base sample)).evalDistMap
                  (adv.interp target) (adv.program target) (adv.initial target)
                  (fun leaf ↦ adv.guess target leaf = sample.1 ∨
                    sample.2 (adv.guess target leaf) = target) {True} := by
  have h := average_image_eq_plantedTargetPatch hcompl
    (fun (_secret : X) (H : X → Y) (target : Y) ↦
      (parallelOracleRuntime H).evalDistMap (adv.interp target)
        (adv.program target) (adv.initial target)
        (fun leaf ↦ H (adv.guess target leaf) = target) {True})
  simpa only [plantedPreimageAdvantage, plantedTargetPatch_eq_target_iff] using h

/-- Parallel inversion of a uniform secret input's image, with adaptive rounds and a total-point
budget. Each public target may select its own complete adversary; the budgets hold for all of
those choices. The density contains the planted preimage as well as accidental preimages. -/
theorem plantedPreimageAdvantage_le_of_isPointBound [Nonempty X]
    (adv : PlantedPreimageAdversary X Y L W A) {q Q : ℕ}
    (hq : ∀ target, (adv.program target).IsTotalQueryBound q)
    (hQ : ∀ target, (adv.program target).IsPointBound Q) :
    plantedPreimageAdvantage adv ≤ min 1
      (ENNReal.ofReal (plantedTargetDensity (X := X) (Y := Y)) *
        ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2)) := by
  refine le_min (plantedPreimageAdvantage_le_one adv) ?_
  by_cases hcard : Fintype.card Y = 1
  · have hδ : plantedTargetDensity (X := X) (Y := Y) = 1 := by
      simp only [plantedTargetDensity, hcard, Nat.cast_one, inv_one, mul_one]
      ring
    rw [hδ, ENNReal.ofReal_one, one_mul]
    refine (plantedPreimageAdvantage_le_one adv).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.sqrt_nonneg ((q : ℝ) * Q)]
  · have hcompl (target : Y) : Nonempty {y : Y // y ≠ target} := by
      have : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.mp
        (by have hpos := Fintype.card_pos (α := Y); omega)
      obtain ⟨y, hy⟩ := exists_ne target
      exact ⟨⟨y, hy⟩⟩
    rw [plantedPreimageAdvantage_eq_plantedTargetPatch adv hcompl]
    have hw : ENNReal.ofReal
        ((Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹) =
        (Fintype.card X : ℝ≥0∞)⁻¹ * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
        ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hb (target : Y) (base : X → {y : Y // y ≠ target}) :
        (∑ sample : X × (X → Y),
          ((Fintype.card X : ℝ≥0∞)⁻¹ * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹) *
            (parallelOracleRuntime (plantedTargetPatch target base sample)).evalDistMap
              (adv.interp target) (adv.program target) (adv.initial target)
              (fun leaf ↦ adv.guess target leaf = sample.1 ∨
                sample.2 (adv.guess target leaf) = target) {True}) ≤
          ENNReal.ofReal (plantedTargetDensity (X := X) (Y := Y)) *
            ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) := by
      have h := sum_mul_evalDistMap_mem_parallel_le_of_isPointBound (adv.interp target)
        (fun z ↦ (base z : Y)) (plantedTargetPatch target base)
        (fun _ : X × (X → Y) ↦
          (Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹)
        (fun _ ↦ by positivity)
        (fun sample ↦ {z | z = sample.1 ∨ sample.2 z = target})
        (fun sample z hz ↦ plantedTargetPatch_eq_base_of_not_mem target base sample z hz)
        (plantedTargetDensity (X := X) (Y := Y)) plantedTargetDensity_nonneg
        (fun z ↦ (sum_indicator_plantedTarget_eq target z).le)
        (hq target) (hQ target) (adv.initial target) (adv.guess target)
      simpa only [hw, Set.mem_ofPred_eq] using h
    calc
      _ ≤ ∑ target : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
          ∑ _base : X → {y : Y // y ≠ target},
            (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
              (ENNReal.ofReal (plantedTargetDensity (X := X) (Y := Y)) *
                ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2)) := by
        apply Finset.sum_le_sum
        intro target _
        apply mul_le_mul le_rfl _ bot_le bot_le
        apply Finset.sum_le_sum
        intro base _
        exact mul_le_mul le_rfl (hb target base) bot_le bot_le
      _ = _ := by
        have havg (target : Y) :
            (∑ _base : X → {y : Y // y ≠ target},
              (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
                (ENNReal.ofReal (plantedTargetDensity (X := X) (Y := Y)) *
                  ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2))) =
              ENNReal.ofReal (plantedTargetDensity (X := X) (Y := Y)) *
                ENNReal.ofReal ((1 + 2 * Real.sqrt ((q : ℝ) * Q)) ^ 2) := by
          let _ := hcompl target
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
            ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
              (ENNReal.natCast_ne_top _), one_mul]
        simp_rw [havg]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _), one_mul]

/-- A maximum-width form of secret-input image inversion, retaining the zero-query term. -/
theorem plantedPreimageAdvantage_le [Nonempty X]
    (adv : PlantedPreimageAdversary X Y L W A) {q k : ℕ}
    (hq : ∀ target, (adv.program target).IsTotalQueryBound q)
    (hk : ∀ target, (adv.program target).IsWidthBound k) :
    plantedPreimageAdvantage adv ≤ min 1
      (ENNReal.ofReal (plantedTargetDensity (X := X) (Y := Y)) *
        ENNReal.ofReal ((1 + 2 * (q : ℝ) * Real.sqrt k) ^ 2)) := by
  have h := plantedPreimageAdvantage_le_of_isPointBound adv hq
    (fun target ↦ (hq target).isPointBound (hk target))
  have hsqrt : Real.sqrt ((q : ℝ) * ((k * q : ℕ) : ℝ)) = (q : ℝ) * Real.sqrt k := by
    rw [Nat.cast_mul, show (q : ℝ) * ((k : ℝ) * q) = (q : ℝ) ^ 2 * k by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  simpa only [hsqrt, mul_assoc] using h

end Quantum
