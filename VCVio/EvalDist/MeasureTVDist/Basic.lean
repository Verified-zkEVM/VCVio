/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Total variation of successful-output measures

Extended and real total variation compare measure denotations. Event discrepancy bounds and
zero-distance characterizations apply without countability or losslessness assumptions.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

universe u v

variable {m : Type u → Type v} {α : Type u}

/-- Extended total variation between the primary measure denotations of two computations. -/
@[expose]
noncomputable def measureETVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : ℝ≥0∞ :=
  Measure.statEDist (𝒟[mx]) (𝒟[my])

/-- Real-valued total variation between the primary measure denotations of two computations. -/
@[expose]
noncomputable def measureTVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : ℝ :=
  Measure.statDist (𝒟[mx]) (𝒟[my])

@[simp]
theorem measureETVDist_self [EvalDistSemantics m] [MeasurableSpace α] (mx : m α) :
    measureETVDist mx mx = 0 :=
  Measure.statEDist_self _

theorem measureETVDist_comm [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureETVDist mx my = measureETVDist my mx :=
  Measure.statEDist_comm _ _

theorem measureETVDist_triangle [EvalDistSemantics m] [MeasurableSpace α]
    (mx my mz : m α) :
    measureETVDist mx mz ≤ measureETVDist mx my + measureETVDist my mz :=
  Measure.statEDist_triangle _ _ _

@[simp]
theorem measureETVDist_eq_zero_iff [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : measureETVDist mx my = 0 ↔ 𝒟[mx] = 𝒟[my] :=
  Measure.statEDist_eq_zero_iff

theorem measureETVDist_le_one [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureETVDist mx my ≤ 1 :=
  Measure.statEDist_le_one _ _ (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

theorem measureETVDist_ne_top [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureETVDist mx my ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (measureETVDist_le_one mx my)

/-- Real total variation is the real part of the extended one. -/
theorem measureTVDist_eq_toReal_measureETVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : measureTVDist mx my = (measureETVDist mx my).toReal := rfl

@[simp]
theorem measureTVDist_self [EvalDistSemantics m] [MeasurableSpace α] (mx : m α) :
    measureTVDist mx mx = 0 :=
  Measure.statDist_self _

theorem measureTVDist_comm [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureTVDist mx my = measureTVDist my mx :=
  Measure.statDist_comm _ _

theorem measureTVDist_nonneg [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    0 ≤ measureTVDist mx my :=
  Measure.statDist_nonneg _ _

theorem measureTVDist_triangle [EvalDistSemantics m] [MeasurableSpace α]
    (mx my mz : m α) :
    measureTVDist mx mz ≤ measureTVDist mx my + measureTVDist my mz :=
  Measure.statDist_triangle _ _ _
    (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)
    (evalDist_apply_univ_le_one mz)

theorem measureTVDist_le_one [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureTVDist mx my ≤ 1 :=
  Measure.statDist_le_one _ _ (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

@[simp]
theorem measureTVDist_eq_zero_iff [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : measureTVDist mx my = 0 ↔ 𝒟[mx] = 𝒟[my] :=
  Measure.statDist_eq_zero_iff _ _
    (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

/-- Two `pure` computations returning distinct values are at extended TV one, on a space whose
measurable sets separate points. -/
theorem measureETVDist_pure_pure_of_ne [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] [MeasurableSpace α] [MeasurableSpace.SeparatesPoints α]
    {a b : α} (h : a ≠ b) : measureETVDist (pure a : m α) (pure b) = 1 := by
  rw [measureETVDist, evalDist_pure, evalDist_pure, Measure.statEDist_dirac_dirac_of_ne h]

/-- Two `pure` computations returning distinct values are at TV one, on a space whose measurable
sets separate points. -/
theorem measureTVDist_pure_pure_of_ne [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] [MeasurableSpace α] [MeasurableSpace.SeparatesPoints α]
    {a b : α} (h : a ≠ b) : measureTVDist (pure a : m α) (pure b) = 1 := by
  rw [measureTVDist_eq_toReal_measureETVDist, measureETVDist_pure_pure_of_ne h]
  simp

/-- Two `pure` computations are at extended TV zero when they return the same value and one
otherwise, on a space whose measurable sets separate points. -/
theorem measureETVDist_pure_pure [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    [MeasurableSpace α] [MeasurableSpace.SeparatesPoints α] (a b : α) [Decidable (a = b)] :
    measureETVDist (pure a : m α) (pure b) = if a = b then 0 else 1 := by
  split_ifs with h
  · subst h
    exact measureETVDist_self _
  · exact measureETVDist_pure_pure_of_ne h

/-- Two `pure` computations are at TV zero when they return the same value and one otherwise, on
a space whose measurable sets separate points. -/
theorem measureTVDist_pure_pure [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    [MeasurableSpace α] [MeasurableSpace.SeparatesPoints α] (a b : α) [Decidable (a = b)] :
    measureTVDist (pure a : m α) (pure b) = if a = b then 0 else 1 := by
  split_ifs with h
  · subst h
    exact measureTVDist_self _
  · exact measureTVDist_pure_pure_of_ne h

/-- Every measurable-event discrepancy is bounded by the extended TV distance. -/
theorem measure_absDiff_apply_le_measureETVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) {s : Set α} (hs : MeasurableSet s) :
    ENNReal.absDiff (𝒟[mx] s) (𝒟[my] s) ≤ measureETVDist mx my :=
  Measure.absDiff_apply_le_statEDist _ _ hs
