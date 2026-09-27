/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Measure compatibility for the discrete sampling frontend

The uniformity certificate of `SampleableType` calibrates its compatibility evaluation
as a uniform measure. Measure identities can then recover the existing discrete equality
statements. Measure proof cores take their calibration hypotheses explicitly and do not
use these adapters.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory

/-- A certified uniform sampler has uniform measure whenever its measure semantics agrees
with its finite distribution on singleton masses. -/
theorem evalDist_uniformSample {α : Type} [SampleableType α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [EvalDistSemantics ProbComp]
    [DiscreteEvalDistCompatible ProbComp] :
    𝒟[$ᵗ α] = uniformOn Set.univ := by
  classical
  let : Fintype α := Fintype.ofFinite α
  apply Measure.ext_of_singleton
  intro x
  rw [evalDist_apply_singleton, probOutput_uniformSample, uniformOn_univ]
  simp

namespace ProbComp.DiscreteCompatibility

-- Give the existing finite adapter precedence in explicitly scoped compatibility proofs.
scoped[ProbComp.DiscreteCompatibility] attribute [instance 1000]
  instEvalDistSemanticsOfMonadLiftTSPMF

end ProbComp.DiscreteCompatibility
