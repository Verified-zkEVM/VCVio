/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable.Bounds
import Mathlib.Data.Fintype.Prod

/-!
# Uniform tables with independently sampled target sets

A uniform table can be generated from an independent table of values avoiding a fixed target
and a uniform label table. A cell receives the target exactly when its label equals the target;
otherwise it receives its value from the avoiding table. A coordinatewise permutation proves
the full continuation law, including observations of the target set together with the table.

The normalized decomposition requires a nonempty target complement. It makes no such claim
when the answer type is a singleton. Point-incidence identities hold for every specified target.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

universe u v

variable {X : Type u} {Y : Type v} [DecidableEq Y]

/-- Replace each target-labelled cell by the target, using an avoiding table at every other cell. -/
@[expose]
def targetPatch (target : Y) (base : X → {y : Y // y ≠ target}) (labels : X → Y) : X → Y :=
  fun x ↦ if labels x = target then target else (base x : Y)

/-- Target membership is read entirely from the label table, independently of the avoiding table. -/
@[simp]
theorem targetPatch_eq_target_iff (target : Y) (base : X → {y : Y // y ≠ target})
    (labels : X → Y) (x : X) :
    targetPatch target base labels x = target ↔ labels x = target := by
  by_cases h : labels x = target <;> simp [targetPatch, h, (base x).property]

/-- Outside the target-labelled cells, the patched table agrees with the avoiding table. -/
theorem targetPatch_eq_base_of_ne (target : Y) (base : X → {y : Y // y ≠ target})
    (labels : X → Y) (x : X) (h : labels x ≠ target) :
    targetPatch target base labels x = (base x : Y) := by
  simp [targetPatch, h]

/-- The target preimage of the patched table is the target preimage of its independent labels. -/
@[simp]
theorem targetPatch_preimage_singleton (target : Y) (base : X → {y : Y // y ≠ target})
    (labels : X → Y) :
    (targetPatch target base labels) ⁻¹' {target} = labels ⁻¹' {target} := by
  ext x
  exact targetPatch_eq_target_iff target base labels x

private def targetSwap (target : Y) (p : Y × {y : Y // y ≠ target}) :
    Y × {y : Y // y ≠ target} :=
  if h : p.1 = target then p else (p.2, ⟨p.1, h⟩)

private theorem targetSwap_involutive (target : Y) : Function.Involutive (targetSwap target) := by
  rintro ⟨a, b⟩
  by_cases h : a = target
  · simp [targetSwap, h]
  · simp [targetSwap, h, b.property]

private def targetEquiv (target : Y) :
    (Y × {y : Y // y ≠ target}) ≃ (Y × {y : Y // y ≠ target}) :=
  (targetSwap_involutive target).toPerm

private theorem targetEquiv_fst (target a : Y) (b : {y : Y // y ≠ target}) :
    (targetEquiv target (a, b)).1 = if a = target then target else (b : Y) := by
  change (targetSwap target (a, b)).1 = _
  by_cases h : a = target <;> simp [targetSwap, h]

private def targetTableEquiv (target : Y) :
    ((X → Y) × (X → {y : Y // y ≠ target})) ≃
      ((X → Y) × (X → {y : Y // y ≠ target})) :=
  (Equiv.arrowProdEquivProdArrow X (fun _ ↦ Y) (fun _ ↦ {y : Y // y ≠ target})).symm.trans
    ((Equiv.piCongrRight (fun _ : X ↦ targetEquiv target)).trans
      (Equiv.arrowProdEquivProdArrow X (fun _ ↦ Y) (fun _ ↦ {y : Y // y ≠ target})))

private theorem targetTableEquiv_fst (target : Y) (labels : X → Y)
    (base : X → {y : Y // y ≠ target}) :
    (targetTableEquiv target (labels, base)).1 = targetPatch target base labels := by
  funext x
  exact targetEquiv_fst target (labels x) (base x)

/-- Summing independent labels and avoiding tables counts every table equally often.
This unnormalized identity also covers an empty target complement. -/
theorem sum_targetPatch [Fintype X] [DecidableEq X] [Fintype Y] (target : Y) (f : (X → Y) → ℝ≥0∞) :
    (∑ labels : X → Y, ∑ base : X → {y : Y // y ≠ target},
      f (targetPatch target base labels)) =
      (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞) * ∑ H : X → Y, f H := by
  classical
  calc
    _ = ∑ p : (X → Y) × (X → {y : Y // y ≠ target}),
        f ((targetTableEquiv target p).1) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro labels _
      apply Finset.sum_congr rfl
      intro base _
      rw [targetTableEquiv_fst]
    _ = ∑ p : (X → Y) × (X → {y : Y // y ≠ target}), f p.1 :=
      Equiv.sum_comp (targetTableEquiv target) (fun p ↦ f p.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]

/-- A uniform table equals the independent average over an avoiding base and uniform labels.
Every continuation sees the same patched table in all of its observations. -/
theorem average_targetPatch [Fintype X] [DecidableEq X] [Fintype Y]
    (target : Y) [Nonempty {y : Y // y ≠ target}] (f : (X → Y) → ℝ≥0∞) :
    (∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * f H) =
      ∑ base : X → {y : Y // y ≠ target},
        (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
          ∑ labels : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
            f (targetPatch target base labels) := by
  have hs := sum_targetPatch target f
  rw [Finset.sum_comm] at hs
  simp only [← Finset.mul_sum]
  rw [hs]
  have hn : (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ht : (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  symm
  calc
    _ = ((Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
          (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)) *
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * ∑ H, f H) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hn ht, one_mul]

/-- The decomposition retains the joint law of a table and its target preimage. -/
theorem average_targetPatch_with_preimage [Fintype X] [DecidableEq X] [Fintype Y]
    (target : Y) [Nonempty {y : Y // y ≠ target}]
    (f : (X → Y) → Set X → ℝ≥0∞) :
    (∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * f H (H ⁻¹' {target})) =
      ∑ base : X → {y : Y // y ≠ target},
        (Fintype.card (X → {y : Y // y ≠ target}) : ℝ≥0∞)⁻¹ *
          ∑ labels : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
            f (targetPatch target base labels) (labels ⁻¹' {target}) := by
  simpa only [targetPatch_preimage_singleton] using
    average_targetPatch target (fun H ↦ f H (H ⁻¹' {target}))

private theorem card_target_labels [Fintype X] [DecidableEq X] [Fintype Y]
    (target : Y) (x : X) :
    ((Finset.univ.filter fun labels : X → Y ↦ labels x = target).card : ℝ≥0∞) /
      Fintype.card (X → Y) = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  let : Nonempty Y := ⟨target⟩
  let : MeasurableSpace Y := ⊤
  have h := uniform_eval_eq (D := X) (R := Y) x target
  rwa [uniformOn_univ_apply_setOf] at h

section Incidence

omit [DecidableEq Y]

/-- Every input is target-labelled with probability exactly the inverse answer-space size. -/
theorem sum_indicator_target_eq_ennreal [Fintype X] [DecidableEq X] [Fintype Y]
    (target : Y) (x : X) :
    (∑ labels : X → Y, Set.indicator {z | labels z = target}
      (fun _ ↦ (Fintype.card (X → Y) : ℝ≥0∞)⁻¹) x) =
      (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ = ((Finset.univ.filter fun labels : X → Y ↦ labels x = target).card : ℝ≥0∞) /
        Fintype.card (X → Y) := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rfl
    _ = _ := card_target_labels target x

/-- Real uniform weights give the same pointwise target incidence, including singleton ranges. -/
theorem sum_indicator_target_eq [Fintype X] [DecidableEq X] [Fintype Y]
    (target : Y) (x : X) :
    (∑ labels : X → Y, Set.indicator {z | labels z = target}
      (fun _ ↦ (Fintype.card (X → Y) : ℝ)⁻¹) x) =
      (Fintype.card Y : ℝ)⁻¹ := by
  classical
  have h := congrArg ENNReal.toReal (card_target_labels target x)
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_inv] at h
  calc
    _ = ((Finset.univ.filter fun labels : X → Y ↦ labels x = target).card : ℝ) /
        Fintype.card (X → Y) := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rfl
    _ = _ := h

end Incidence

end ProbabilityTheory
