/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Bounds
public import VCVio.EvalDist.PFunctorMeasure
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Uniform oracle semantics agreement

A finite uniform oracle's measure-valued and probability-mass-valued answer
interpretations assign the same measure to each response type. The agreement
certificate lets a direct measure fold retain the discrete probability bridges.
-/

public section

open MeasureTheory ProbabilityTheory

universe u v

namespace OracleSpec.IsUniformMeasureSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}
  [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [IsUniformSpec spec] [IsUniformMeasureSpec spec]

/-- Uniform measure and mass-function interpretations agree on every oracle answer type. -/
instance instCompatible : PFunctor.IsMeasureSpec.Compatible spec.toPFunctor := by
  -- Both specifications carry finite instances; use the one in the mass-function certificate.
  let : spec.Fintype := IsUniformSpec.fintype
  refine ⟨fun t => ?_⟩
  rw [IsUniformMeasureSpec.toMeasure_eq_uniform t, IsUniformSpec.toPMF_eq_uniform t]
  apply Measure.ext_of_singleton
  intro x
  classical
  have h := uniformOn_univ_apply_setOf (fun y : spec.Range t => y = x)
  have hset : {y : spec.Range t | y = x} = {x} := by ext y; simp
  rw [hset] at h
  rw [PMF.toMeasure_apply_singleton _ x (MeasurableSet.singleton x),
    PMF.uniformOfFintype_apply]
  have hc : (Finset.univ.filter fun y : spec.Range t => y = x).card = 1 := by
    simp [Finset.filter_eq']
  rw [hc] at h
  simpa [ENNReal.div_eq_inv_mul] using h

end OracleSpec.IsUniformMeasureSpec
