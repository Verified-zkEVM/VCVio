/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Event-supremum total variation versus Mathlib's variation distance

`MeasureTheory.Measure.etvDist` is the supremum over measurable events of `ENNReal.absDiff`, while
`MeasureTheory.etvDist` is the total variation of `μ - ν` on the whole space. For finite measures
twice the first is the second plus the discrepancy of total masses, so on probability measures the
second is twice the first.
-/

public section

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- On a Hahn decomposition `s` of `μ` and `ν`, the excess `μ t - ν t` of a measurable event is at
most the excess on `sᶜ`. -/
private lemma tsub_le_tsub_compl_of_isHahnDecomposition [IsFiniteMeasure ν] {s t : Set α}
    (h : IsHahnDecomposition μ ν s) (ht : MeasurableSet t) :
    μ t - ν t ≤ μ sᶜ - ν sᶜ :=
  calc μ t - ν t
      = (μ.restrict s t + μ.restrict sᶜ t) - (ν.restrict s t + ν.restrict sᶜ t) := by
        rw [← Measure.add_apply, ← Measure.add_apply,
          restrict_add_restrict_compl h.measurableSet, restrict_add_restrict_compl h.measurableSet]
    _ ≤ (μ.restrict s t - ν.restrict s t) + (μ.restrict sᶜ t - ν.restrict sᶜ t) :=
        add_tsub_add_le_tsub_add_tsub
    _ = (μ.restrict sᶜ - ν.restrict sᶜ) t := by
        rw [tsub_eq_zero_of_le (h.le_on t), zero_add, sub_apply ht h.ge_on_compl]
    _ ≤ (μ.restrict sᶜ - ν.restrict sᶜ) Set.univ := measure_mono (Set.subset_univ t)
    _ = μ sᶜ - ν sᶜ := by simp [sub_apply MeasurableSet.univ h.ge_on_compl]

/-- On a Hahn decomposition `s` of `μ` and `ν`, `Measure.etvDist μ ν` is the larger of the two
one-sided discrepancies `ν s - μ s` and `μ sᶜ - ν sᶜ`, attained at `s` and at `sᶜ`. -/
theorem etvDist_eq_max_of_isHahnDecomposition [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (h : IsHahnDecomposition μ ν s) :
    μ.etvDist ν = max (ν s - μ s) (μ sᶜ - ν sᶜ) := by
  refine le_antisymm (iSup_le fun t => ?_) (max_le ?_ ?_)
  · rw [ENNReal.absDiff_eq_max]
    refine max_le (le_max_of_le_right ?_) (le_max_of_le_left ?_)
    · exact tsub_le_tsub_compl_of_isHahnDecomposition h t.2
    · simpa using tsub_le_tsub_compl_of_isHahnDecomposition h.compl t.2
  · exact le_add_self.trans (absDiff_apply_le_etvDist μ ν h.measurableSet)
  · exact le_self_add.trans (absDiff_apply_le_etvDist μ ν h.measurableSet.compl)

/-- For finite measures, twice the event-supremum distance `Measure.etvDist` is the variation
distance `MeasureTheory.etvDist` plus the discrepancy of the total masses. -/
theorem two_mul_etvDist_eq_etvDist_add_absDiff (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    2 * μ.etvDist ν = MeasureTheory.etvDist μ ν + ENNReal.absDiff (μ Set.univ) (ν Set.univ) := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  obtain ⟨a, ha⟩ := exists_add_of_le (h.le_on Set.univ)
  obtain ⟨b, hb⟩ := exists_add_of_le (h.ge_on_compl Set.univ)
  simp only [restrict_apply_univ] at ha hb
  rw [etvDist_eq_max_of_isHahnDecomposition h, h.etvDist_eq,
    ← measure_add_measure_compl (μ := μ) h.measurableSet,
    ← measure_add_measure_compl (μ := ν) h.measurableSet, ha, hb,
    ENNReal.add_sub_cancel_left (measure_ne_top _ _),
    ENNReal.add_sub_cancel_left (measure_ne_top _ _), ← add_assoc, add_right_comm (μ s) a,
    ENNReal.absDiff_eq_edist, ENNReal.edist_add_left _ _ (by finiteness),
    ← ENNReal.absDiff_eq_edist]
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, ENNReal.absDiff, tsub_eq_zero_of_le hab, add_zero, two_mul,
      add_right_comm, add_tsub_cancel_of_le hab]
  · rw [max_eq_left hab, ENNReal.absDiff, tsub_eq_zero_of_le hab, zero_add, two_mul, add_assoc,
      add_tsub_cancel_of_le hab]

/-- The event-supremum distance `Measure.etvDist` is at most the variation distance
`MeasureTheory.etvDist`. -/
theorem etvDist_le_etvDist (μ ν : Measure α) : μ.etvDist ν ≤ MeasureTheory.etvDist μ ν := by
  by_cases hfin : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := hfin
    obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
    rw [etvDist_eq_max_of_isHahnDecomposition h, h.etvDist_eq]
    exact max_le le_self_add le_add_self
  · simp [MeasureTheory.etvDist_of_not_isFiniteMeasure hfin]

/-- On probability measures the variation distance `MeasureTheory.etvDist`, valued in `[0, 2]`, is
twice the event-supremum distance `Measure.etvDist`, valued in `[0, 1]`. -/
theorem _root_.MeasureTheory.etvDist_eq_two_mul_etvDist (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasureTheory.etvDist μ ν = 2 * μ.etvDist ν := by
  simp [two_mul_etvDist_eq_etvDist_add_absDiff]

/-- For finite measures, twice `Measure.tvDist` is the variation distance `MeasureTheory.tvDist`
plus the absolute difference of the total masses. -/
theorem two_mul_tvDist_eq_tvDist_add_abs (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    2 * μ.tvDist ν = MeasureTheory.tvDist μ ν + |μ.real Set.univ - ν.real Set.univ| := by
  have h := congrArg ENNReal.toReal (two_mul_etvDist_eq_etvDist_add_absDiff μ ν)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_add (MeasureTheory.etvDist_ne_top μ ν)
    (ne_top_of_le_ne_top (by finiteness) (ENNReal.absDiff_le_add _ _)),
    ENNReal.absDiff_toReal (measure_ne_top _ _) (measure_ne_top _ _)] at h

/-- For finite measures `Measure.tvDist` is at most the variation distance
`MeasureTheory.tvDist`. -/
theorem tvDist_le_tvDist (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ.tvDist ν ≤ MeasureTheory.tvDist μ ν :=
  ENNReal.toReal_mono (MeasureTheory.etvDist_ne_top μ ν) (etvDist_le_etvDist μ ν)

/-- On probability measures the variation distance `MeasureTheory.tvDist` is twice
`Measure.tvDist`. -/
theorem _root_.MeasureTheory.tvDist_eq_two_mul_tvDist (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasureTheory.tvDist μ ν = 2 * μ.tvDist ν := by
  simp [Measure.tvDist, MeasureTheory.tvDist, MeasureTheory.etvDist_eq_two_mul_etvDist μ ν]

end MeasureTheory.Measure

end
