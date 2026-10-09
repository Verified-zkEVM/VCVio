/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.EvalDist.Defs.Measure.OptionT
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Chosen-space integration regressions

Usual real spaces support AE-valuations and conditional measure equality. Arbitrary hidden
outputs admit structural oracle interchange and expectation comparison. A continuous Gaussian
operation uses explicit AE continuation hypotheses rather than an unrestricted monad bind law.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp PFunctor
open scoped ENNReal

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `NeverFail, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native integration unexpectedly imports {name}"

namespace VCVioTest.MeasureIntegration

example {α β : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → ProbComp ℝ) :
    𝒟[mx >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ mx >>= fun a ↦ f a b] :=
  OracleComp.evalDist_bind_bind_swap mx my f

example {α : Type} (mx : ProbComp α) (f g : α → ProbComp ENNReal)
    (h : ∀ a ∈ support mx, (∫⁻ x, x ∂𝒟[f a]) ≤ ∫⁻ x, x ∂𝒟[g a]) :
    (∫⁻ x, x ∂𝒟[mx >>= f]) ≤ ∫⁻ x, x ∂𝒟[mx >>= g] :=
  OracleComp.lintegral_evalDist_bind_mono_of_support mx f g measurable_id measurable_id h

example : 𝒟[(pure (0 : ℝ) : ProbComp ℝ) >>= fun x ↦ pure x] =
    𝒟[(pure (0 : ℝ) : ProbComp ℝ) >>= fun _ ↦ pure (0 : ℝ)] := by
  apply evalDist_bind_congr_ae
    (pure (0 : ℝ) : ProbComp ℝ) (fun x ↦ pure x) (fun _ ↦ pure (0 : ℝ))
  · simpa only [evalDist_pure] using Measure.measurable_dirac
  · simpa only [evalDist_pure] using (measurable_const : Measurable fun _ : ℝ ↦
      Measure.dirac (0 : ℝ))
  · simp only [evalDist_pure]
    exact ae_eq_dirac (fun x : ℝ ↦ Measure.dirac x)

example (g : ℝ → ENNReal) :
    (∫⁻ y, g y ∂𝒟[(fun x : ℝ ↦ x + 1) <$> (pure (0 : ℝ) : ProbComp ℝ)]) =
      ∫⁻ x, g (x + 1) ∂𝒟[(pure (0 : ℝ) : ProbComp ℝ)] := by
  apply lintegral_evalDist_map_of_aemeasurable _ (measurable_id.add_const 1)
  simpa only [map_pure, evalDist_pure, id_eq] using
    (aemeasurable_dirac : AEMeasurable g (Measure.dirac (0 + 1 : ℝ)))

example (mx : OptionT ProbComp ℝ) :
    𝒟[mx >>= fun x ↦ pure (-x)] Set.univ = 𝒟[mx] Set.univ := by
  rw [evalDist_bind_apply_univ mx (fun x ↦ pure (-x)) (by
    simp only [evalDist_pure]
    exact Measure.measurable_dirac.comp measurable_neg)]
  simp

example (mx : ProbComp ℝ) (h : ∀ᵐ x ∂𝒟[mx], x = 0) :
    Pr{let x ← mx}[x ≤ 0] = Pr{let x ← mx}[x = 0] := by
  apply prEvent_congr_ae mx (fun x ↦ x ≤ 0) (fun x ↦ x = 0) (by fun_prop) (by fun_prop)
  exact h.mono fun x hx ↦ by simp [hx]

/-- An interface with one real-valued Gaussian operation. -/
abbrev GaussianSpec : PFunctor := ⟨Unit, fun _ ↦ ℝ⟩

instance : (a : GaussianSpec.A) → MeasurableSpace (GaussianSpec.B a) :=
  fun _ ↦ inferInstanceAs (MeasurableSpace ℝ)

noncomputable instance : IsMeasureSpec GaussianSpec where
  toMeasure _ := gaussianReal 0 1
  isProbabilityMeasure _ := instIsProbabilityMeasureGaussianReal 0 1

/-- The real-valued operation has the standard Gaussian answer law. -/
@[simp]
theorem gaussian_toMeasure : IsMeasureSpec.toMeasure (P := GaussianSpec) () =
    gaussianReal 0 1 := rfl

example (g : ℝ → ENNReal) (hg : AEMeasurable g (gaussianReal 0 1)) :
    (∫⁻ y, g y ∂𝒟[(FreeM.liftBind () (fun x ↦ pure x) : FreeM GaussianSpec ℝ)]) =
      ∫⁻ x, g x ∂gaussianReal 0 1 := by
  have hcont : AEMeasurable
      (fun x : ℝ ↦ 𝒟[(pure x : FreeM GaussianSpec ℝ)]) (gaussianReal 0 1) := by
    simpa only [evalDist_pure] using Measure.measurable_dirac.aemeasurable
  have hdenote : AEMeasurable
      (fun x : ℝ ↦ FreeM.denote (pure x : FreeM GaussianSpec ℝ)) (gaussianReal 0 1) := by
    simpa only [FreeM.evalDist_eq_denote] using hcont
  have hroot : 𝒟[(FreeM.liftBind () (fun x ↦ pure x) : FreeM GaussianSpec ℝ)] =
      gaussianReal 0 1 := by
    rw [FreeM.evalDist_liftBind (P := GaussianSpec) () _ hdenote]
    simp only [evalDist_pure, Measure.bind_dirac, gaussian_toMeasure]
  rw [FreeM.lintegral_evalDist_liftBind (P := GaussianSpec) () _ hcont
    (by simpa only [hroot] using hg)]
  simp only [evalDist_pure, gaussian_toMeasure, lintegral_dirac]

end VCVioTest.MeasureIntegration
