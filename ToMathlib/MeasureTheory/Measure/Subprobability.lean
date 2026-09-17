/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Data.FunLike.IsApply

/-!
# Subprobability measures

`IsSubprobabilityMeasure μ` states that `μ Set.univ ≤ 1`. It is the mass discipline of a
computation that may fail to return: the defect `1 - μ Set.univ` is the mass that never reached a
value, so a returned result and a failure stay distinguishable without an `Option` wrapper.

Mathlib has no such class. `IsZeroOrProbabilityMeasure` is a different condition — it admits only
total mass `0` or `1`, and so cannot describe a computation that fails with probability strictly
between the two.

The class has automatic instances for `dirac`, `map`, and `bind` against a subprobability family.
These upper mass bounds hold without measurability: Mathlib assigns zero to a nonmeasurable
pushforward, and `Measure.bind_apply_le` bounds a bind before measurability is known. Exact mass
preservation and probability-measure instances still require the relevant measurability proofs.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The zero measure evaluates pointwise to zero. -/
instance Measure.instIsZeroApply : IsZeroApply (Measure α) (Set α) ℝ≥0∞ where
  zero_apply _ := rfl

/-- A measure with total mass at most one. -/
class IsSubprobabilityMeasure (μ : Measure α) : Prop where
  /-- The total mass of a subprobability measure is at most one. -/
  measure_univ_le' : μ Set.univ ≤ 1

section

variable (μ : Measure α) [IsSubprobabilityMeasure μ]

/-- The total mass of a subprobability measure is at most one. -/
theorem measure_univ_le : μ Set.univ ≤ 1 := IsSubprobabilityMeasure.measure_univ_le'

/-- Every set has measure at most one under a subprobability measure. -/
theorem measure_le_one (s : Set α) : μ s ≤ 1 :=
  le_trans (measure_mono (Set.subset_univ s)) (measure_univ_le μ)

instance (priority := 100) IsSubprobabilityMeasure.toIsFiniteMeasure : IsFiniteMeasure μ :=
  ⟨lt_of_le_of_lt (measure_univ_le μ) ENNReal.one_lt_top⟩

/-- The mass a subprobability measure does not assign to any value. -/
noncomputable def Measure.defect : ℝ≥0∞ := 1 - μ Set.univ

/-- The real-valued defect is one minus the real-valued total mass. -/
@[simp]
theorem Measure.defect_toReal : μ.defect.toReal = 1 - (μ Set.univ).toReal := by
  rw [Measure.defect, ENNReal.toReal_sub_of_le (measure_univ_le μ) ENNReal.one_ne_top,
    ENNReal.toReal_one]

@[simp]
theorem Measure.defect_add_measure_univ : μ.defect + μ Set.univ = 1 :=
  tsub_add_cancel_of_le (measure_univ_le μ)

end

instance (priority := 100) IsProbabilityMeasure.toIsSubprobabilityMeasure (μ : Measure α)
    [IsProbabilityMeasure μ] : IsSubprobabilityMeasure μ :=
  ⟨le_of_eq (measure_univ (μ := μ))⟩

instance : IsSubprobabilityMeasure (0 : Measure α) := ⟨by simp⟩

instance (a : α) : IsSubprobabilityMeasure (Measure.dirac a) := inferInstance

/-- Pushing a subprobability measure forward along a measurable function preserves its mass
bound. Stated as a theorem because the measurability hypothesis cannot be synthesised. -/
theorem isSubprobabilityMeasure_map (μ : Measure α) [IsSubprobabilityMeasure μ] {f : α → β}
    (hf : Measurable f) : IsSubprobabilityMeasure (μ.map f) :=
  ⟨by rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]; exact measure_univ_le μ⟩

/-- Every pushforward of a subprobability measure is a subprobability measure, including the
zero measure Mathlib assigns when the map is not almost-everywhere measurable. -/
instance Measure.isSubprobabilityMeasure_map (μ : Measure α) [IsSubprobabilityMeasure μ]
    (f : α → β) : IsSubprobabilityMeasure (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · refine ⟨?_⟩
    rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ_le μ
  · rw [Measure.map_of_not_aemeasurable hf]
    infer_instance

/-- Giry bind of a subprobability family against a subprobability measure stays a
subprobability measure. The measurability hypothesis is the one `Measure.bind_apply` needs. -/
theorem isSubprobabilityMeasure_bind {μ : Measure α} [IsSubprobabilityMeasure μ]
    {f : α → Measure β} (hf : AEMeasurable f μ)
    [hsub : ∀ a, IsSubprobabilityMeasure (f a)] :
    IsSubprobabilityMeasure (μ.bind f) := by
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ hf]
  calc ∫⁻ a, f a Set.univ ∂μ
      ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun a => measure_univ_le (f a)
    _ = μ Set.univ := by simp
    _ ≤ 1 := measure_univ_le μ

/-- Giry bind of subprobability measures has mass at most one even before the continuation's
measurability is known. -/
instance Measure.isSubprobabilityMeasure_bind (μ : Measure α) [IsSubprobabilityMeasure μ]
    (f : α → Measure β) [∀ a, IsSubprobabilityMeasure (f a)] :
    IsSubprobabilityMeasure (μ.bind f) := by
  refine ⟨(Measure.bind_apply_le _ MeasurableSet.univ).trans ?_⟩
  calc ∫⁻ a, f a Set.univ ∂μ
      ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun a ↦ measure_univ_le (f a)
    _ = μ Set.univ := by simp
    _ ≤ 1 := measure_univ_le μ

end MeasureTheory
