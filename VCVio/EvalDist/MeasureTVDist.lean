/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import VCVio.EvalDist.TVDist

/-!
# Total variation for measure-valued computation semantics

This module is the primary total-variation interface for VCVio computations. It applies
Mathlib-measure total variation directly to `𝒟[…]`; no finite-distribution backend, countability
assumption, or failure completion appears in its definitions.

The older `VCVio.EvalDist.TVDist` module remains the discrete compatibility development.  New
measure-native security statements should use `measureTVDist` and `measureETVDist` from this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

universe u v

variable {m : Type u → Type v} {α : Type u}

/-- Extended total variation between the primary measure denotations of two computations. -/
noncomputable def measureETVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : ℝ≥0∞ :=
  Measure.etvDist (𝒟[mx]) (𝒟[my])

/-- Real-valued total variation between the primary measure denotations of two computations. -/
noncomputable def measureTVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : ℝ :=
  Measure.tvDist (𝒟[mx]) (𝒟[my])

@[simp]
theorem measureETVDist_self [EvalDistSemantics m] [MeasurableSpace α] (mx : m α) :
    measureETVDist mx mx = 0 :=
  Measure.etvDist_self _

theorem measureETVDist_comm [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureETVDist mx my = measureETVDist my mx :=
  Measure.etvDist_comm _ _

theorem measureETVDist_triangle [EvalDistSemantics m] [MeasurableSpace α]
    (mx my mz : m α) :
    measureETVDist mx mz ≤ measureETVDist mx my + measureETVDist my mz :=
  Measure.etvDist_triangle _ _ _

@[simp]
theorem measureETVDist_eq_zero_iff [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : measureETVDist mx my = 0 ↔ 𝒟[mx] = 𝒟[my] :=
  Measure.etvDist_eq_zero_iff

theorem measureETVDist_le_one [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureETVDist mx my ≤ 1 :=
  Measure.etvDist_le_one _ _ (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

@[simp]
theorem measureTVDist_self [EvalDistSemantics m] [MeasurableSpace α] (mx : m α) :
    measureTVDist mx mx = 0 :=
  Measure.tvDist_self _

theorem measureTVDist_comm [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureTVDist mx my = measureTVDist my mx :=
  Measure.tvDist_comm _ _

theorem measureTVDist_nonneg [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    0 ≤ measureTVDist mx my :=
  Measure.tvDist_nonneg _ _

theorem measureTVDist_triangle [EvalDistSemantics m] [MeasurableSpace α]
    (mx my mz : m α) :
    measureTVDist mx mz ≤ measureTVDist mx my + measureTVDist my mz :=
  Measure.tvDist_triangle _ _ _
    (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)
    (evalDist_apply_univ_le_one mz)

theorem measureTVDist_le_one [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureTVDist mx my ≤ 1 :=
  Measure.tvDist_le_one _ _ (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

@[simp]
theorem measureTVDist_eq_zero_iff [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : measureTVDist mx my = 0 ↔ 𝒟[mx] = 𝒟[my] :=
  Measure.tvDist_eq_zero_iff _ _
    (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

/-- Every measurable-event discrepancy is bounded by measure-native extended TV. -/
theorem measure_absDiff_apply_le_measureETVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) {s : Set α} (hs : MeasurableSet s) :
    ENNReal.absDiff (𝒟[mx] s) (𝒟[my] s) ≤ measureETVDist mx my :=
  Measure.absDiff_apply_le_etvDist _ _ hs

/-- The measure and executable `SPMF` TV distances have the same zero-distance relation on a
discrete space. In particular, transporting a perfect-indistinguishability proof across
`SPMF.toMeasure` is lossless. -/
theorem SPMF.toMeasure_tvDist_eq_zero_iff [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p q : SPMF α) :
    Measure.tvDist p.toMeasure q.toMeasure = 0 ↔ SPMF.tvDist p q = 0 := by
  rw [Measure.tvDist_eq_zero_iff _ _ (SPMF.toMeasure_apply_univ_le_one p)
    (SPMF.toMeasure_apply_univ_le_one q), SPMF.tvDist_eq_zero_iff]
  constructor
  · intro h
    exact congrArg SPMF.toPMF (SPMF.toMeasure_injective h)
  · intro h
    exact congrArg SPMF.toMeasure ((SPMF.toPMF_inj p q).mp h)

/-- Exact compatibility for the `Unit` observation space used by bundled UC semantics. -/
theorem SPMF.toMeasure_tvDist_punit (p q : SPMF PUnit.{1}) :
    Measure.tvDist p.toMeasure q.toMeasure = SPMF.tvDist p q := by
  apply congrArg ENNReal.toReal
  rw [PMF.etvDist_option_punit p.toPMF q.toPMF]
  apply le_antisymm
  · refine iSup_le fun s => ?_
    by_cases hunit : PUnit.unit ∈ s.1
    · have hs : s.1 = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        simpa [Subsingleton.elim x PUnit.unit] using hunit
      rw [hs]
      simp [SPMF.toMeasure_apply_univ, SPMF.apply_eq_toPMF_some]
    · have hs : s.1 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x
        simpa [Subsingleton.elim x PUnit.unit] using hunit
      rw [hs]
      simp
  · refine le_iSup_of_le ⟨Set.univ, MeasurableSet.univ⟩ ?_
    simp [SPMF.toMeasure_apply_univ, SPMF.apply_eq_toPMF_some]
