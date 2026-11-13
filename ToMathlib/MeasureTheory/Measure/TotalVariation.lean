/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.Data.ENNReal.AbsDiff
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Statistical distance for subprobability measures

`Measure.statEDist μ ν` is the supremum over measurable events of the absolute difference of the
two measures, and `Measure.statDist` is its real value. This is the statistical distance of the
cryptography literature: on probability distributions over a countable discrete space it is
`½ · ∑ x, |P x - Q x|`, the largest discrepancy of an event. The formulation is native to Mathlib
measures, applies to continuous spaces, and detects differing total mass: on subprobability
measures it is the statistical distance of the distributions completed by an explicit failure
point that carries the missing mass. Two probability measures differ by at most the mass missing
from any common lower measure.

Mathlib's `MeasureTheory.etvDist` is the total variation of `μ - ν`, valued in `[0, 2]`. On
probability measures it is twice `Measure.statEDist`; on finite measures
`Measure.two_mul_statEDist_eq_etvDist_add_absDiff` adds the discrepancy of the total masses, so on
subprobability measures the two distances do not differ by a constant factor.
`ToMathlib.MeasureTheory.Measure.TotalVariation.Variation` proves these relations.
-/

@[expose] public section

noncomputable section

open ENNReal

universe u v

namespace MeasureTheory.Measure

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]

/-- The statistical distance of two measures in `ℝ≥0∞`: the largest discrepancy
`ENNReal.absDiff (μ s) (ν s)` of a measurable event `s`.

This is the statistical distance of the cryptography literature, `½ · ∑ x, |P x - Q x|` on
probability distributions over a countable discrete space, which equals the supremum over events.
On probability measures it is half of Mathlib's variation distance `MeasureTheory.etvDist`. On
subprobability measures it is the statistical distance of the distributions completed by a failure
point that carries the missing mass; for finite measures the exact relation to Mathlib's distance
is `Measure.two_mul_statEDist_eq_etvDist_add_absDiff`,
`2 * μ.statEDist ν = MeasureTheory.etvDist μ ν + ENNReal.absDiff (μ Set.univ) (ν Set.univ)`.
-/
protected noncomputable def statEDist (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ s : {s : Set α // MeasurableSet s}, ENNReal.absDiff (μ s.1) (ν s.1)

/-- The real-valued statistical distance, `(μ.statEDist ν).toReal`; see `Measure.statEDist`.
On probability measures it is half of Mathlib's `MeasureTheory.tvDist`. -/
protected noncomputable def statDist (μ ν : Measure α) : ℝ :=
  (μ.statEDist ν).toReal

/-- Every individual measurable event discrepancy is bounded by the statistical distance. -/
theorem absDiff_apply_le_statEDist (μ ν : Measure α) {s : Set α} (hs : MeasurableSet s) :
    ENNReal.absDiff (μ s) (ν s) ≤ μ.statEDist ν :=
  le_iSup_of_le ⟨s, hs⟩ le_rfl

@[simp]
theorem statEDist_self (μ : Measure α) : μ.statEDist μ = 0 := by
  simp [Measure.statEDist]

theorem statEDist_comm (μ ν : Measure α) : μ.statEDist ν = ν.statEDist μ := by
  simp only [Measure.statEDist, ENNReal.absDiff_comm]

theorem statEDist_nonneg (μ ν : Measure α) : 0 ≤ μ.statEDist ν := bot_le

theorem statEDist_triangle (μ ν κ : Measure α) :
    μ.statEDist κ ≤ μ.statEDist ν + ν.statEDist κ := by
  refine iSup_le fun s => ?_
  exact (ENNReal.absDiff_triangle (μ s.1) (ν s.1) (κ s.1)).trans
    (add_le_add (le_iSup (fun t : {t : Set α // MeasurableSet t} =>
      ENNReal.absDiff (μ t.1) (ν t.1)) s)
      (le_iSup (fun t : {t : Set α // MeasurableSet t} =>
        ENNReal.absDiff (ν t.1) (κ t.1)) s))

@[simp]
theorem statEDist_eq_zero_iff {μ ν : Measure α} : μ.statEDist ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply Measure.ext
    intro s hs
    apply ENNReal.absDiff_eq_zero.mp
    exact nonpos_iff_eq_zero.mp <| (absDiff_apply_le_statEDist μ ν hs).trans_eq h
  · rintro rfl
    exact statEDist_self μ

private theorem absDiff_le_one {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    ENNReal.absDiff a b ≤ 1 := by
  rcases le_total a b with hab | hba
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le hab, zero_add]
    exact tsub_le_self.trans hb
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le hba, add_zero]
    exact tsub_le_self.trans ha

/-- The statistical distance of subprobability measures is at most one. -/
theorem statEDist_le_one (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.statEDist ν ≤ 1 := by
  refine iSup_le fun s => absDiff_le_one ?_ ?_
  · exact (measure_mono (Set.subset_univ s.1)).trans hμ
  · exact (measure_mono (Set.subset_univ s.1)).trans hν

theorem statEDist_ne_top (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.statEDist ν ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (statEDist_le_one μ ν hμ hν)

/-- The statistical distance of two probability measures is at most the missing mass of any
common lower measure. -/
theorem statEDist_le_one_sub_of_le {μ ν c : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : c ≤ μ) (hν : c ≤ ν) :
    μ.statEDist ν ≤ 1 - c Set.univ := by
  have hcfin : IsFiniteMeasure c :=
    ⟨(Measure.le_iff'.mp hμ Set.univ).trans_lt (measure_lt_top μ Set.univ)⟩
  have hrest : ∀ {ρ : Measure α} [IsProbabilityMeasure ρ], c ≤ ρ → ∀ T, MeasurableSet T →
      ρ T - c T ≤ 1 - c Set.univ := by
    intro ρ _ hρ T hT
    rw [← Measure.sub_apply hT hρ, ← measure_univ (μ := ρ),
      ← Measure.sub_apply MeasurableSet.univ hρ]
    exact measure_mono (Set.subset_univ T)
  refine iSup_le fun T => ?_
  have hcT : c T.1 ≠ ⊤ := measure_ne_top c T.1
  have hμT : μ T.1 = c T.1 + (μ T.1 - c T.1) :=
    (add_tsub_cancel_of_le (Measure.le_iff'.mp hμ T.1)).symm
  have hνT : ν T.1 = c T.1 + (ν T.1 - c T.1) :=
    (add_tsub_cancel_of_le (Measure.le_iff'.mp hν T.1)).symm
  have ha := hrest hμ T.1 T.2
  have hb := hrest hν T.1 T.2
  rw [hμT, hνT, ENNReal.absDiff, ENNReal.add_sub_add_eq_sub_left hcT,
    ENNReal.add_sub_add_eq_sub_left hcT]
  rcases le_total (μ T.1 - c T.1) (ν T.1 - c T.1) with hab | hab
  · rw [tsub_eq_zero_of_le hab, zero_add]
    exact tsub_le_self.trans hb
  · rw [tsub_eq_zero_of_le hab, add_zero]
    exact tsub_le_self.trans ha

/-- Deterministic measurable post-processing cannot increase the statistical distance. -/
theorem statEDist_map_le (μ ν : Measure α) (f : α → β) (hf : Measurable f) :
    (μ.map f).statEDist (ν.map f) ≤ μ.statEDist ν := by
  refine iSup_le fun s => ?_
  rw [Measure.map_apply hf s.2, Measure.map_apply hf s.2]
  exact absDiff_apply_le_statEDist μ ν (s.2.preimage hf)

@[simp]
theorem statDist_self (μ : Measure α) : μ.statDist μ = 0 := by
  simp [Measure.statDist]

theorem statDist_comm (μ ν : Measure α) : μ.statDist ν = ν.statDist μ := by
  simp only [Measure.statDist, statEDist_comm]

theorem statDist_nonneg (μ ν : Measure α) : 0 ≤ μ.statDist ν := ENNReal.toReal_nonneg

theorem statDist_triangle (μ ν κ : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) (hκ : κ Set.univ ≤ 1) :
    μ.statDist κ ≤ μ.statDist ν + ν.statDist κ := by
  rw [Measure.statDist, Measure.statDist, Measure.statDist,
    ← ENNReal.toReal_add (statEDist_ne_top μ ν hμ hν) (statEDist_ne_top ν κ hν hκ)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨statEDist_ne_top μ ν hμ hν, statEDist_ne_top ν κ hν hκ⟩)
    (statEDist_triangle μ ν κ)

theorem statDist_le_one (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.statDist ν ≤ 1 := by
  rw [Measure.statDist, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono one_ne_top (statEDist_le_one μ ν hμ hν)

@[simp]
theorem statDist_eq_zero_iff (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.statDist ν = 0 ↔ μ = ν := by
  rw [Measure.statDist, ENNReal.toReal_eq_zero_iff, statEDist_eq_zero_iff]
  simp [statEDist_ne_top μ ν hμ hν]

theorem statDist_map_le (μ ν : Measure α) (f : α → β) (hf : Measurable f)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) :
    (μ.map f).statDist (ν.map f) ≤ μ.statDist ν := by
  rw [Measure.statDist, Measure.statDist]
  exact ENNReal.toReal_mono (statEDist_ne_top μ ν hμ hν) (statEDist_map_le μ ν f hf)

/-- On a one-point space, the statistical distance is the absolute difference of the point
masses. -/
theorem statDist_punit (μ ν : Measure PUnit) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ.statDist ν = |(μ {PUnit.unit}).toReal - (ν {PUnit.unit}).toReal| := by
  have hetv : μ.statEDist ν = ENNReal.absDiff (μ {PUnit.unit}) (ν {PUnit.unit}) := by
    apply le_antisymm
    · refine iSup_le fun s => ?_
      by_cases hunit : PUnit.unit ∈ s.1
      · have hs : s.1 = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          simpa [Subsingleton.elim x PUnit.unit] using hunit
        rw [hs]
        have hsingleton : ({PUnit.unit} : Set PUnit) = Set.univ := by
          ext x
          simp
        rw [hsingleton]
      · have hs : s.1 = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x
          simpa [Subsingleton.elim x PUnit.unit] using hunit
        simp [hs]
    · exact le_iSup_of_le ⟨{PUnit.unit}, MeasurableSet.singleton _⟩ le_rfl
  rw [Measure.statDist, hetv]
  exact ENNReal.absDiff_toReal (measure_ne_top μ _) (measure_ne_top ν _)

end MeasureTheory.Measure
