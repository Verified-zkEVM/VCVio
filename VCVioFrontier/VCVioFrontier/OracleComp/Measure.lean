/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Languages.Probabilistic.Basic

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.SimSemantics.Measure
public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# The measure of a finite-choice program

VCVio and cslib-frontier interpret the same finite-choice program as a measure and a probability
mass function. Their evaluations agree on every measurable event.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp

namespace VCVioFrontier

/-- Frontier and VCVio use the same free programs over uniform finite choices. -/
theorem probComp_eq (α : Type) : _root_.ProbComp α = Cslib.ProbComp α := rfl

/-- The VCVio measure of a uniform-choice program is the measure of Frontier's PMF. -/
theorem evalDist_eq_toMeasure {α : Type} [MeasurableSpace α] (p : _root_.ProbComp α) :
    𝒟[p] = (Cslib.ProbComp.eval p).toMeasure := by
  induction p using Cslib.OracleComp.induction with
  | pure a =>
    change Measure.dirac a = (PMF.pure a).toMeasure
    exact (PMF.toMeasure_pure _).symm
  | query_bind q k ih =>
    let _ : MeasurableSpace (Fin (q + 1)) := ⊤
    change PFunctor.FreeM.denote (PFunctor.FreeM.liftBind (P := unifSpec.toPFunctor) q k) =
      ((Cslib.ProbComp.unifOracle q).bind fun i => Cslib.ProbComp.eval (k i)).toMeasure
    rw [PFunctor.FreeM.denote_liftBind _ _ Measurable.of_discrete.aemeasurable]
    apply Measure.ext
    intro s hs
    rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
      PMF.toMeasure_bind_apply _ _ s hs]
    change @MeasureTheory.lintegral (unifSpec.Range q) ⊤
      (OracleSpec.AnswerMeasure.toMeasure (spec := unifSpec) q) (fun i => 𝒟[k i] s) = _
    rw [OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn]
    simp only [lintegral_fintype, uniformOn_univ_apply_singleton, Cslib.ProbComp.unifOracle,
      Cslib.Probability.PMF.uniformOfFintype_apply, tsum_fintype]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    exact congrArg (fun m : Measure α => _ * m s) (ih i)

/-- VCVio's typed uniform sampler has Frontier's uniform PMF. -/
theorem eval_uniformSample (α : Type) [Fintype α] [SampleableType α] :
    Cslib.ProbComp.eval ($ᵗ α : _root_.ProbComp α) = Cslib.Probability.PMF.uniformOfFintype α := by
  let _ : MeasurableSpace α := ⊤
  ext a
  rw [← PMF.toMeasure_apply_singleton, ← evalDist_eq_toMeasure,
    SampleableType.evalDist_uniformSample_singleton, Cslib.Probability.PMF.uniformOfFintype_apply]
  exact measurableSet_singleton a

/-- Answer each source coin request with Frontier's fair bit. -/
@[expose] noncomputable def fairBits : QueryImpl coinSpec _root_.ProbComp :=
  fun _ => Cslib.ProbComp.uniform Bool

/-- Interpreting explicit coin requests in Frontier preserves VCVio's fair-coin measure. -/
theorem evalDist_fairBits {α : Type} [MeasurableSpace α] (p : OracleComp coinSpec α) :
    𝒟[p] = (Cslib.ProbComp.eval (simulateQ fairBits p)).toMeasure := by
  rw [← evalDist_eq_toMeasure]
  apply (OracleComp.evalDist_simulateQ_eq_of_forall fairBits _ p).symm
  intro q
  change @evalDist _root_.ProbComp _ Bool ⊤ (Cslib.ProbComp.uniform Bool) = _
  rw [OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn]
  let _ : MeasurableSpace Bool := ⊤
  calc
    𝒟[Cslib.ProbComp.uniform Bool] = 𝒟[($ᵗ Bool : _root_.ProbComp Bool)] := by
      rw [evalDist_eq_toMeasure, evalDist_eq_toMeasure, Cslib.ProbComp.eval_uniform,
        eval_uniformSample]
    _ = _ := SampleableType.evalDist_uniformSample

end VCVioFrontier
