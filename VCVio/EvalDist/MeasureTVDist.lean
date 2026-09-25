/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.EvalDist.TVDist

/-!
# Discrete total-variation compatibility

Agreement of discrete and measure-valued total variation on zero distance and unit observations.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u

variable {α : Type u}

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
