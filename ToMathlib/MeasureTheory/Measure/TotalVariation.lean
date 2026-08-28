/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.Data.ENNReal.AbsDiff
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Total variation distance for subprobability measures

The extended distance is the supremum of the absolute difference of the two measures over
measurable events.  This formulation is native to Mathlib measures, applies to continuous spaces,
and also detects differing total mass.  On probability measures it is the usual total variation
distance; on subprobability measures it agrees with first completing the missing mass as an
explicit failure outcome.
-/

@[expose] public section

noncomputable section

open ENNReal

universe u v

namespace MeasureTheory.Measure

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]

/-- Extended total variation: the largest mass discrepancy on a measurable event. -/
protected noncomputable def etvDist (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ s : {s : Set α // MeasurableSet s}, ENNReal.absDiff (μ s.1) (ν s.1)

/-- Real-valued total variation distance. -/
protected noncomputable def tvDist (μ ν : Measure α) : ℝ :=
  (μ.etvDist ν).toReal

/-- Every individual measurable event discrepancy is bounded by extended total variation. -/
theorem absDiff_apply_le_etvDist (μ ν : Measure α) {s : Set α} (hs : MeasurableSet s) :
    ENNReal.absDiff (μ s) (ν s) ≤ μ.etvDist ν :=
  le_iSup_of_le ⟨s, hs⟩ le_rfl

@[simp]
theorem etvDist_self (μ : Measure α) : μ.etvDist μ = 0 := by
  simp [Measure.etvDist]

theorem etvDist_comm (μ ν : Measure α) : μ.etvDist ν = ν.etvDist μ := by
  simp only [Measure.etvDist, ENNReal.absDiff_comm]

theorem etvDist_nonneg (μ ν : Measure α) : 0 ≤ μ.etvDist ν := bot_le

theorem etvDist_triangle (μ ν κ : Measure α) :
    μ.etvDist κ ≤ μ.etvDist ν + ν.etvDist κ := by
  refine iSup_le fun s => ?_
  exact (ENNReal.absDiff_triangle (μ s.1) (ν s.1) (κ s.1)).trans
    (add_le_add (le_iSup (fun t : {t : Set α // MeasurableSet t} =>
      ENNReal.absDiff (μ t.1) (ν t.1)) s)
      (le_iSup (fun t : {t : Set α // MeasurableSet t} =>
        ENNReal.absDiff (ν t.1) (κ t.1)) s))

@[simp]
theorem etvDist_eq_zero_iff {μ ν : Measure α} : μ.etvDist ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply Measure.ext
    intro s hs
    apply ENNReal.absDiff_eq_zero.mp
    exact nonpos_iff_eq_zero.mp <| (absDiff_apply_le_etvDist μ ν hs).trans_eq h
  · rintro rfl
    exact etvDist_self μ

private theorem absDiff_le_one {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    ENNReal.absDiff a b ≤ 1 := by
  rcases le_total a b with hab | hba
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le hab, zero_add]
    exact tsub_le_self.trans hb
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le hba, add_zero]
    exact tsub_le_self.trans ha

/-- Extended TV is at most one for subprobability measures. -/
theorem etvDist_le_one (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.etvDist ν ≤ 1 := by
  refine iSup_le fun s => absDiff_le_one ?_ ?_
  · exact (measure_mono (Set.subset_univ s.1)).trans hμ
  · exact (measure_mono (Set.subset_univ s.1)).trans hν

theorem etvDist_ne_top (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.etvDist ν ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (etvDist_le_one μ ν hμ hν)

/-- Deterministic measurable post-processing cannot increase total variation. -/
theorem etvDist_map_le (μ ν : Measure α) (f : α → β) (hf : Measurable f) :
    (μ.map f).etvDist (ν.map f) ≤ μ.etvDist ν := by
  refine iSup_le fun s => ?_
  rw [Measure.map_apply hf s.2, Measure.map_apply hf s.2]
  exact absDiff_apply_le_etvDist μ ν (s.2.preimage hf)

@[simp]
theorem tvDist_self (μ : Measure α) : μ.tvDist μ = 0 := by
  simp [Measure.tvDist]

theorem tvDist_comm (μ ν : Measure α) : μ.tvDist ν = ν.tvDist μ := by
  simp only [Measure.tvDist, etvDist_comm]

theorem tvDist_nonneg (μ ν : Measure α) : 0 ≤ μ.tvDist ν := ENNReal.toReal_nonneg

theorem tvDist_triangle (μ ν κ : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) (hκ : κ Set.univ ≤ 1) :
    μ.tvDist κ ≤ μ.tvDist ν + ν.tvDist κ := by
  rw [Measure.tvDist, Measure.tvDist, Measure.tvDist,
    ← ENNReal.toReal_add (etvDist_ne_top μ ν hμ hν) (etvDist_ne_top ν κ hν hκ)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨etvDist_ne_top μ ν hμ hν, etvDist_ne_top ν κ hν hκ⟩)
    (etvDist_triangle μ ν κ)

theorem tvDist_le_one (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.tvDist ν ≤ 1 := by
  rw [Measure.tvDist, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono one_ne_top (etvDist_le_one μ ν hμ hν)

@[simp]
theorem tvDist_eq_zero_iff (μ ν : Measure α)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.tvDist ν = 0 ↔ μ = ν := by
  rw [Measure.tvDist, ENNReal.toReal_eq_zero_iff, etvDist_eq_zero_iff]
  simp [etvDist_ne_top μ ν hμ hν]

theorem tvDist_map_le (μ ν : Measure α) (f : α → β) (hf : Measurable f)
    (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) :
    (μ.map f).tvDist (ν.map f) ≤ μ.tvDist ν := by
  rw [Measure.tvDist, Measure.tvDist]
  exact ENNReal.toReal_mono (etvDist_ne_top μ ν hμ hν) (etvDist_map_le μ ν f hf)

end MeasureTheory.Measure
