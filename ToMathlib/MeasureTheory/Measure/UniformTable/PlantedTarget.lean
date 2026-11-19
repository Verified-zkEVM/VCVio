/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable.Target

/-!
# Uniform tables with a target planted at a hidden input

Sampling a uniform table and publishing its value at a uniform hidden input is equivalent to
sampling an independent uniform target and programming it at that input. An avoiding base and
independent labels then determine every other preimage. The resulting hidden set contains the
planted input with certainty and each other input with inverse-range probability.

All coupling identities retain the full table, hidden input and public target in an arbitrary
continuation. The target complement need only be inhabited for the avoiding-base decomposition.
-/

public section

open scoped ENNReal

namespace ProbabilityTheory

universe u v

variable {X : Type u} {Y : Type v}

section Programming

variable [DecidableEq X]

private def coordinateExchange (s : X) (p : (X → Y) × Y) : (X → Y) × Y :=
  (Function.update p.1 s p.2, p.1 s)

private theorem coordinateExchange_involutive (s : X) :
    Function.Involutive (coordinateExchange (Y := Y) s) := by
  rintro ⟨H, t⟩
  apply Prod.ext
  · funext z
    by_cases h : z = s <;> simp [coordinateExchange, h]
  · simp [coordinateExchange]

private def coordinateExchangeEquiv (s : X) : ((X → Y) × Y) ≃ ((X → Y) × Y) :=
  (coordinateExchange_involutive s).toPerm

private theorem sum_update_eval [Fintype X] [Fintype Y] (s : X)
    (f : (X → Y) → Y → ℝ≥0∞) :
    (∑ H : X → Y, ∑ t : Y, f (Function.update H s t) t) =
      (Fintype.card Y : ℝ≥0∞) * ∑ H : X → Y, f H (H s) := by
  classical
  calc
    _ = ∑ p : (X → Y) × Y,
        f ((coordinateExchangeEquiv s p).1) ((coordinateExchangeEquiv s p).1 s) := by
      simp [Fintype.sum_prod_type, coordinateExchangeEquiv, coordinateExchange]
    _ = ∑ p : (X → Y) × Y, f p.1 (p.1 s) :=
      Equiv.sum_comp (coordinateExchangeEquiv s) (fun p ↦ f p.1 (p.1 s))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]

/-- A published table value has the joint law obtained by programming an independent uniform
value at the same input. The continuation may inspect the complete table and published value. -/
theorem average_eval_eq_update [Fintype X] [Fintype Y] [Nonempty Y]
    (s : X) (f : (X → Y) → Y → ℝ≥0∞) :
    (∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * f H (H s)) =
      ∑ t : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
        ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
          f (Function.update H s t) t := by
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm, sum_update_eval]
  symm
  calc
    _ = ((Fintype.card Y : ℝ≥0∞)⁻¹ * Fintype.card Y) *
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * ∑ H, f H (H s)) := by ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), one_mul]

section Target

variable [DecidableEq Y]

/-- An avoiding base supplies non-target answers, independent labels select further preimages,
and the distinguished input always receives the target. -/
@[expose]
def plantedTargetPatch (target : Y) (base : X → {y : Y // y ≠ target})
    (sample : X × (X → Y)) : X → Y :=
  Function.update (targetPatch target base sample.2) sample.1 target

/-- The target preimage is the union of the planted input and the independently labelled cells. -/
@[simp]
theorem plantedTargetPatch_eq_target_iff (target : Y) (base : X → {y : Y // y ≠ target})
    (sample : X × (X → Y)) (z : X) :
    plantedTargetPatch target base sample z = target ↔ z = sample.1 ∨ sample.2 z = target := by
  by_cases hz : z = sample.1
  · simp [plantedTargetPatch, hz]
  · simp [plantedTargetPatch, hz]

/-- Outside the planted target set, the oracle agrees with the independent avoiding base. -/
theorem plantedTargetPatch_eq_base_of_not_mem (target : Y)
    (base : X → {y : Y // y ≠ target}) (sample : X × (X → Y)) (z : X)
    (hz : ¬ (z = sample.1 ∨ sample.2 z = target)) :
    plantedTargetPatch target base sample z = (base z : Y) := by
  simp only [not_or] at hz
  rw [plantedTargetPatch, Function.update_of_ne hz.1,
    targetPatch_eq_base_of_ne target base sample.2 z hz.2]

/-- The published value at a hidden input can be sampled by choosing an independent target,
avoiding base and labels, and then planting that target. The continuation retains the input. -/
theorem average_image_eq_plantedTargetPatch [Fintype X] [Fintype Y] [Nonempty Y]
    (hcompl : ∀ target : Y, Nonempty {y : Y // y ≠ target})
    (f : X → (X → Y) → Y → ℝ≥0∞) :
    (∑ s : X, (Fintype.card X : ℝ≥0∞)⁻¹ *
      ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * f s H (H s)) =
      ∑ target : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
        ∑ base : X → {y : Y // y ≠ target},
          (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
            ∑ sample : X × (X → Y),
              ((Fintype.card X : ℝ≥0∞)⁻¹ * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹) *
                f sample.1 (plantedTargetPatch target base sample) target := by
  classical
  calc
    _ = ∑ s : X, (Fintype.card X : ℝ≥0∞)⁻¹ *
        ∑ target : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
          ∑ base : X → {y : Y // y ≠ target},
            (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
              ∑ labels : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
                f s (Function.update (targetPatch target base labels) s target) target := by
      apply Finset.sum_congr rfl
      intro s _
      rw [average_eval_eq_update]
      congr 1
      apply Finset.sum_congr rfl
      intro target _
      let _ := hcompl target
      rw [average_targetPatch target]
    _ = _ := by
      simp only [Finset.mul_sum, Fintype.sum_prod_type, plantedTargetPatch]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro target _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro base _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro labels _
      ring

end Target

end Programming

/-- The exact marginal target density in a uniform-secret image game. -/
@[expose]
noncomputable def plantedTargetDensity [Fintype X] [Fintype Y] : ℝ :=
  (Fintype.card X : ℝ)⁻¹ + (1 - (Fintype.card X : ℝ)⁻¹) * (Fintype.card Y : ℝ)⁻¹

section Incidence

variable [Fintype X] [Nonempty X] [Fintype Y]

/-- A hidden input is present with probability one; all other cells have inverse-range density. -/
theorem sum_indicator_plantedTarget_eq [Nonempty Y] [DecidableEq X] (target : Y) (z : X) :
    (∑ sample : X × (X → Y), Set.indicator {x | x = sample.1 ∨ sample.2 x = target}
      (fun _ ↦ (Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹) z) =
      plantedTargetDensity (X := X) (Y := Y) := by
  classical
  rw [Fintype.sum_prod_type]
  have hc : (Fintype.card (X → Y) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmx : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = ∑ s : X, if z = s then (Fintype.card X : ℝ)⁻¹ else
        (Fintype.card X : ℝ)⁻¹ * (Fintype.card Y : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hz : z = s
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, true_or, ite_true,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc
          _ = (Fintype.card X : ℝ)⁻¹ *
              ((Fintype.card (X → Y) : ℝ) * (Fintype.card (X → Y) : ℝ)⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hc, mul_one]
      · simp only [ite_eq_right hz]
        calc
          _ = (Fintype.card X : ℝ)⁻¹ * ∑ labels : X → Y,
              Set.indicator {x | labels x = target}
                (fun _ ↦ (Fintype.card (X → Y) : ℝ)⁻¹) z := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro labels _
            by_cases ht : labels z = target <;> simp [hz, ht]
          _ = _ := by rw [sum_indicator_target_eq]
    _ = ∑ s : X, ((if z = s then
        (Fintype.card X : ℝ)⁻¹ -
          (Fintype.card X : ℝ)⁻¹ * (Fintype.card Y : ℝ)⁻¹ else 0) +
        (Fintype.card X : ℝ)⁻¹ * (Fintype.card Y : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hz : z = s <;> simp [hz]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, plantedTargetDensity]
      field_simp [hmx]
      ring

/-- The image-game density is positive for nonempty input and output spaces. -/
theorem plantedTargetDensity_pos : 0 < plantedTargetDensity (X := X) (Y := Y) := by
  have hx : 1 ≤ (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos (α := X)
  have hi : (Fintype.card X : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hx
  exact add_pos_of_pos_of_nonneg (by positivity)
    (mul_nonneg (sub_nonneg.mpr hi) (by positivity))

/-- The image-game density is nonnegative, including singleton input and output spaces. -/
theorem plantedTargetDensity_nonneg : 0 ≤ plantedTargetDensity (X := X) (Y := Y) :=
  plantedTargetDensity_pos.le

/-- Planting a preimage cannot give a marginal density larger than one. -/
theorem plantedTargetDensity_le_one [Nonempty Y] :
    plantedTargetDensity (X := X) (Y := Y) ≤ 1 := by
  have hx : 1 ≤ (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos (α := X)
  have hy : 1 ≤ (Fintype.card Y : ℝ) := by exact_mod_cast Fintype.card_pos (α := Y)
  have hix : (Fintype.card X : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hx
  have hiy : (Fintype.card Y : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hy
  unfold plantedTargetDensity
  nlinarith [mul_le_mul_of_nonneg_left hiy (sub_nonneg.mpr hix)]

end Incidence

end ProbabilityTheory
