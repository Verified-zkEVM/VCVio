/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Disagreement.Measure
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Native observed continuation comparison regressions

Chosen real source spaces admit AE continuation comparisons. Finite references may observe
different payload types; hidden function-valued prefixes need no measurable space. Lossy
prefixes retain their successful-mass factor.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `NeverFail, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native disagreement unexpectedly imports {name}"

namespace VCVioTest.DisagreementMeasure

universe v

example {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (mx : m ℝ) (f : ℝ → m ℝ) (g : Fin 2 → ℝ → m Prop)
    (hf : Measurable fun x ↦ 𝒟[do let y ← f x; return y ≤ 0])
    (hg : ∀ i, Measurable fun x ↦ 𝒟[g i x]) (bound : ℝ → ENNReal)
    (h : ∀ᵐ x ∂𝒟[mx], Pr{let y ← f x}[y ≤ 0] ≤
      (∑ i, Pr{let q ← g i x}[q]) + bound x) :
    Pr{let y ← mx >>= f}[y ≤ 0] ≤
      (∑ i, Pr{let q ← mx >>= g i}[q]) + ∫⁻ x, bound x ∂𝒟[mx] :=
  prEvent_bind_le_sum_add_lintegral_ae mx f (fun y ↦ y ≤ 0) g hf hg bound h

example (κ : Kernel ℝ ℝ) (η : Fin 2 → Kernel ℝ Bool) (bound : ℝ → ENNReal)
    (h : ∀ᵐ x ∂gaussianReal 0 1, κ x (Set.Iic 0) ≤
      (∑ i, η i x {true}) + bound x) :
    (κ ∘ₘ gaussianReal 0 1) (Set.Iic 0) ≤
      (∑ i, (η i ∘ₘ gaussianReal 0 1) {true}) + ∫⁻ x, bound x ∂gaussianReal 0 1 :=
  Kernel.comp_apply_le_sum_add_lintegral_ae κ η (gaussianReal 0 1) measurableSet_Iic
    (fun _ ↦ {true}) (fun _ ↦ measurableSet_singleton true) bound h

example (f : ℝ → Measure ℝ) (g : Fin 2 → ℝ → Measure Bool) (bound : ℝ → ENNReal)
    (h : ∀ᵐ x ∂Measure.dirac (0 : ℝ), f x (Set.Iic 0) ≤
      (∑ i, g i x {true}) + bound x) :
    (Measure.dirac (0 : ℝ)).bind f (Set.Iic 0) ≤
      (∑ i, (Measure.dirac (0 : ℝ)).bind (g i) {true}) +
        ∫⁻ x, bound x ∂Measure.dirac (0 : ℝ) :=
  Measure.bind_apply_le_sum_add_lintegral_ae (Measure.dirac (0 : ℝ)) f g
    aemeasurable_dirac (fun _ ↦ aemeasurable_dirac) measurableSet_Iic
    (fun _ ↦ {true}) (fun _ ↦ measurableSet_singleton true) bound h

example {α β : Type} (mx : Option α) (f : α → Option β) (p : β → Prop)
    (g : Fin 2 → α → Option Prop) (ε : ENNReal)
    (h : ∀ x ∈ support mx, Pr{let y ← f x}[p y] ≤
      (∑ i, Pr{let q ← g i x}[q]) + ε) :
    Pr{let y ← mx >>= f}[p y] ≤ (∑ i, Pr{let q ← mx >>= g i}[q]) +
      ε * Pr{let _x ← mx}[True] :=
  prEvent_bind_le_sum_add_mul_mass_of_support mx f p g ε h

example (mx : Option (Nat → Nat)) (f g : (Nat → Nat) → Option ℝ)
    (bad : (Nat → Nat) → Option (ℝ × ℝ)) (D : (Nat → Nat) → Prop) (ε₁ ε₂ : ENNReal)
    (hD : Pr{let x ← mx}[D x] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬D x → Pr{let y ← f x}[y ≤ 0] ≤
      Pr{let y ← g x}[y ≤ 0] + Pr{let z ← bad x}[z.1 ≤ z.2] + ε₂) :
    Pr{let y ← mx >>= f}[y ≤ 0] ≤ Pr{let y ← mx >>= g}[y ≤ 0] +
      Pr{let z ← mx >>= bad}[z.1 ≤ z.2] + ε₁ + ε₂ :=
  prEvent_bind_le_add_bad_disagree hD h

end VCVioTest.DisagreementMeasure
