/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Losslessness of measure-valued computations

Losslessness is Mathlib's `IsProbabilityMeasure` on the successful-output measure. Bind preserves
this property when its continuation is lossless almost everywhere. Structurally possible
zero-probability branches impose no additional obligation.
-/

public section

open MeasureTheory

universe u v

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- A lossless computation followed by almost everywhere lossless continuations is lossless. -/
theorem evalDist.isProbabilityMeasure_bind_of_ae (mx : m α) (f : α → m β)
    [IsProbabilityMeasure 𝒟[mx]] (hf : Measurable fun a ↦ 𝒟[f a])
    (hprob : ∀ᵐ a ∂𝒟[mx], IsProbabilityMeasure 𝒟[f a]) :
    IsProbabilityMeasure 𝒟[mx >>= f] := by
  rw [evalDist_bind mx f hf]
  exact MeasureTheory.isProbabilityMeasure_bind hf.aemeasurable hprob

/-- For a lossless input, losslessness after bind means almost everywhere lossless continuation. -/
theorem evalDist.isProbabilityMeasure_bind_iff (mx : m α) (f : α → m β)
    [IsProbabilityMeasure 𝒟[mx]] (hf : Measurable fun a ↦ 𝒟[f a]) :
    IsProbabilityMeasure 𝒟[mx >>= f] ↔ ∀ᵐ a ∂𝒟[mx], IsProbabilityMeasure 𝒟[f a] := by
  simp only [isProbabilityMeasure_iff, evalDist_bind mx f hf,
    Measure.bind_apply MeasurableSet.univ hf.aemeasurable]
  have hfinite : (∫⁻ a, 𝒟[f a] Set.univ ∂𝒟[mx]) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤) <| by
      calc
        (∫⁻ a, 𝒟[f a] Set.univ ∂𝒟[mx]) ≤ ∫⁻ _ : α, 1 ∂𝒟[mx] :=
          lintegral_mono fun a ↦ evalDist_apply_univ_le_one (f a)
        _ = 1 := by simp
  have h : (∫⁻ a, 𝒟[f a] Set.univ ∂𝒟[mx]) = 1 ↔
      (fun a ↦ 𝒟[f a] Set.univ) =ᵐ[𝒟[mx]] (fun _ ↦ 1) := by
    simpa only [lintegral_const, measure_univ, mul_one] using
      lintegral_eq_iff_ae_eq_of_ae_le
        (μ := 𝒟[mx]) (f := fun a ↦ 𝒟[f a] Set.univ) (g := fun _ ↦ 1)
        hfinite
        measurable_const.aemeasurable
        (Filter.Eventually.of_forall fun a ↦ evalDist_apply_univ_le_one (f a))
  exact h

/-- Pointwise losslessness is a sufficient discrete bind rule with no source-space argument. -/
theorem evalDist.isProbabilityMeasure_bind (mx : m α) (f : α → m β)
    [DiscreteMeasurableSpace α] [IsProbabilityMeasure 𝒟[mx]]
    (hprob : ∀ a, IsProbabilityMeasure 𝒟[f a]) : IsProbabilityMeasure 𝒟[mx >>= f] :=
  evalDist.isProbabilityMeasure_bind_of_ae mx f Measurable.of_discrete
    (Filter.Eventually.of_forall hprob)
