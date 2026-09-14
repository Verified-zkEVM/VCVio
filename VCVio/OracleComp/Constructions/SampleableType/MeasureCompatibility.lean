/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.UniformCompatibility

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

/-- Recover a discrete frontend equality from equality of its successful-output measures. -/
theorem evalSPMF_eq_of_evalDist_eq {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [EvalDistSemantics ProbComp]
    [DiscreteEvalDistCompatible ProbComp]
    (mx my : ProbComp α) (h : 𝒟[mx] = 𝒟[my]) :
    𝒮[mx] = 𝒮[my] := by
  apply evalSPMF_ext
  intro x
  simpa only [evalDist_apply_singleton] using congrArg (fun μ : Measure α => μ {x}) h

/-- Equality of discrete frontend distributions preserves their successful-output measures. -/
theorem evalDist_eq_of_evalSPMF_eq {α : Type} [MeasurableSpace α]
    [EvalDistSemantics ProbComp] [DiscreteEvalDistCompatible ProbComp]
    (mx my : ProbComp α) (h : 𝒮[mx] = 𝒮[my]) : 𝒟[mx] = 𝒟[my] :=
  Measure.ext fun s hs => by
    rw [evalDist_apply mx hs, evalDist_apply my hs]
    simp only [probEvent_def, h]

namespace ProbComp.DiscreteCompatibility

-- Give the existing finite adapter precedence in explicitly scoped compatibility proofs.
scoped[ProbComp.DiscreteCompatibility] attribute [instance 1000]
  instEvalDistSemanticsOfMonadLiftTSPMF

end ProbComp.DiscreteCompatibility
