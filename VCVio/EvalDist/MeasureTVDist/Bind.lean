/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MeasureTVDist.Basic
public import ToMathlib.MeasureTheory.Measure.TotalVariation.Bind
public import ToMathlib.Probability.Kernel.TotalVariation

/-!
# Sequential total variation of native computations

Measurably parameterized continuations obey Mathlib measure contraction and conditional-majorant
laws. Prefix failure retains its actual mass; conditional premises need only hold almost
everywhere under the denoted prefix. The same measure rules govern kernel composition.
-/

public section

open MeasureTheory
open scoped ENNReal

universe u v

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type u}
  [MeasurableSpace α] [MeasurableSpace β]

/-- A common measurable continuation contracts the native denotational distance. -/
theorem measureETVDist_bind_le (mx my : m α) (f : α → m β)
    (hf : Measurable fun a ↦ 𝒟[f a]) :
    measureETVDist (mx >>= f) (my >>= f) ≤ measureETVDist mx my := by
  simp only [measureETVDist, evalDist_bind _ _ hf]
  exact Measure.etvDist_bind_le 𝒟[mx] 𝒟[my] (fun a ↦ 𝒟[f a]) hf

/-- An AE conditional majorant bounds the distance after a common prefix. -/
theorem measureETVDist_bind_bind_le_lintegral (mx : m α) (f g : α → m β)
    (hf : Measurable fun a ↦ 𝒟[f a]) (hg : Measurable fun a ↦ 𝒟[g a])
    (bound : α → ENNReal) (hbound : ∀ᵐ a ∂𝒟[mx], measureETVDist (f a) (g a) ≤ bound a) :
    measureETVDist (mx >>= f) (mx >>= g) ≤ ∫⁻ a, bound a ∂𝒟[mx] := by
  simp only [measureETVDist, evalDist_bind _ _ hf, evalDist_bind _ _ hg] at hbound ⊢
  exact Measure.etvDist_bind_bind_le_lintegral 𝒟[mx] (fun a ↦ 𝒟[f a]) (fun a ↦ 𝒟[g a])
    hf.aemeasurable hg.aemeasurable bound hbound

/-- Vary the prefix and continuation, integrating the conditional bound under the second
prefix's chosen output measure. -/
theorem measureETVDist_bind_bind_le_add_lintegral (mx my : m α) (f g : α → m β)
    (hf : Measurable fun a ↦ 𝒟[f a]) (hg : Measurable fun a ↦ 𝒟[g a])
    (bound : α → ENNReal) (hbound : ∀ᵐ a ∂𝒟[my], measureETVDist (f a) (g a) ≤ bound a) :
    measureETVDist (mx >>= f) (my >>= g) ≤
      measureETVDist mx my + ∫⁻ a, bound a ∂𝒟[my] := by
  simp only [measureETVDist, evalDist_bind _ _ hf, evalDist_bind _ _ hg] at hbound ⊢
  exact Measure.etvDist_bind_bind_le_add_lintegral 𝒟[mx] 𝒟[my]
    (fun a ↦ 𝒟[f a]) (fun a ↦ 𝒟[g a]) hf hg.aemeasurable bound hbound

/-- Charge a measurable exceptional prefix event and retain the successful good-branch mass. -/
theorem measureETVDist_bind_bind_le_of_bad (mx : m α) (f g : α → m β)
    (hf : Measurable fun a ↦ 𝒟[f a]) (hg : Measurable fun a ↦ 𝒟[g a])
    {bad : Set α} (hbad : MeasurableSet bad) (ε : ENNReal)
    (hgood : ∀ᵐ a ∂𝒟[mx], a ∉ bad → measureETVDist (f a) (g a) ≤ ε) :
    measureETVDist (mx >>= f) (mx >>= g) ≤ 𝒟[mx] bad + ε * 𝒟[mx] badᶜ := by
  simp only [measureETVDist, evalDist_bind _ _ hf, evalDist_bind _ _ hg] at hgood ⊢
  exact Measure.etvDist_bind_bind_le_of_bad 𝒟[mx] (fun a ↦ 𝒟[f a]) (fun a ↦ 𝒟[g a])
    hf.aemeasurable hg.aemeasurable hbad ε hgood

/-- A common measurable continuation contracts real native denotational distance. -/
theorem measureTVDist_bind_le (mx my : m α) (f : α → m β)
    (hf : Measurable fun a ↦ 𝒟[f a]) :
    measureTVDist (mx >>= f) (my >>= f) ≤ measureTVDist mx my := by
  simp only [measureTVDist, evalDist_bind _ _ hf]
  exact Measure.tvDist_bind_le 𝒟[mx] 𝒟[my] (fun a ↦ 𝒟[f a]) hf

/-- A finite integrated majorant bounds real native conditional distance. -/
theorem measureTVDist_bind_bind_le_lintegral (mx : m α) (f g : α → m β)
    (hf : Measurable fun a ↦ 𝒟[f a]) (hg : Measurable fun a ↦ 𝒟[g a])
    (bound : α → ENNReal) (hbound : ∀ᵐ a ∂𝒟[mx], measureETVDist (f a) (g a) ≤ bound a)
    (hfinite : (∫⁻ a, bound a ∂𝒟[mx]) ≠ ⊤) :
    measureTVDist (mx >>= f) (mx >>= g) ≤ (∫⁻ a, bound a ∂𝒟[mx]).toReal := by
  simp only [measureTVDist, measureETVDist, evalDist_bind _ _ hf, evalDist_bind _ _ hg]
    at hbound ⊢
  exact Measure.tvDist_bind_bind_le_lintegral 𝒟[mx] (fun a ↦ 𝒟[f a]) (fun a ↦ 𝒟[g a])
    hf.aemeasurable hg.aemeasurable bound hbound hfinite
