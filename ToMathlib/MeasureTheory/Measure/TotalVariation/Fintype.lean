/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import ToMathlib.MeasureTheory.Measure.Coupling.Maximal

/-!
# Total variation on a finite type

On a finite type with measurable singletons, total variation between probability measures is half
the L1 distance of their point masses. The formula follows from the finite-support expression
`MeasureTheory.Measure.etvDist_eq_sum_tsub`, applied in both directions.
-/

public section

noncomputable section

open ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]

/-- On a finite type, total variation between probability measures is half of the L1 distance of
their point masses. -/
theorem tvDist_eq_half_sum_abs (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    μ.tvDist ν = (∑ x, |(μ {x}).toReal - (ν {x}).toReal|) / 2 := by
  have h2 : 2 * μ.etvDist ν = ∑ x, ENNReal.absDiff (μ {x}) (ν {x}) := by
    rw [two_mul]
    nth_rw 2 [etvDist_comm]
    rw [etvDist_eq_sum_tsub (F := Finset.univ) (by simp) (by simp),
      etvDist_eq_sum_tsub (μ := ν) (ν := μ) (F := Finset.univ) (by simp) (by simp),
      ← Finset.sum_add_distrib]
    rfl
  have hfin : ∀ x, ENNReal.absDiff (μ {x}) (ν {x}) ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top ν _⟩)
      (ENNReal.absDiff_le_add _ _)
  rw [Measure.tvDist, _root_.eq_div_iff two_ne_zero, mul_comm,
    show (2 : ℝ) = (2 : ℝ≥0∞).toReal by simp, ← ENNReal.toReal_mul, h2,
    ENNReal.toReal_sum fun x _ => hfin x]
  exact Finset.sum_congr rfl fun x _ =>
    ENNReal.absDiff_toReal (measure_ne_top _ _) (measure_ne_top _ _)

end MeasureTheory.Measure
