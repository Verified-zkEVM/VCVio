/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub, Devon Tuma
-/

module
public import ToMathlib.Probability.Kernel.Bounds
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.Monad.Branch
public import VCVio.EvalDist.ProbabilityBounds
import Mathlib.Data.Fin.VecNotation

/-!
# Additive comparison of observed continuations

Expectations after a common prefix satisfy finite-sum comparison rules: a comparison of an
observation with finitely many reference observations and an allowance, on the reachable outputs
of the prefix, holds between their expectations. Measurable observations admit AE premises on a
chosen prefix law instead. Constant allowances retain the prefix's success mass. Arbitrary hidden
payloads need no measurable space.

The disagreement rules charge an exceptional event or an observed bad world while sharing this
argument.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v
variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {α β ι : Type}

/-- AE comparison with a finite family of reference observations integrates the conditional
allowance. No measurability of the allowance is required. -/
theorem wp_le_sum_add_lintegral_ae [Fintype ι] [MeasurableSpace α] (mx : m α)
    {f : α → ℝ≥0∞} (F : ι → α → ℝ≥0∞) (hf : Measurable f) (hF : ∀ i, Measurable (F i))
    (bound : α → ℝ≥0∞) (h : ∀ᵐ a ∂𝒟[mx], f a ≤ (∑ i, F i a) + bound a) :
    wp⟦mx⟧ f ≤ (∑ i, wp⟦mx⟧ (F i)) + ∫⁻ a, bound a ∂𝒟[mx] := by
  rw [ExpectationWP.wp_eq_lintegral mx f hf]
  simp_rw [ExpectationWP.wp_eq_lintegral mx _ (hF _)]
  exact lintegral_le_sum_add_lintegral_of_le_ae Finset.univ
    (fun i _ ↦ (hF i).aemeasurable) h

/-- AE comparison of continuation events with a finite family of reference observations
integrates the conditional allowance. -/
theorem prEvent_bind_le_sum_add_lintegral_ae [Fintype ι] [MeasurableSpace α]
    (mx : m α) (f : α → m β) (p : β → Prop) (F : ι → α → ℝ≥0∞)
    (hf : Measurable fun a ↦ 𝒟[p <$> f a]) (hF : ∀ i, Measurable (F i)) (bound : α → ℝ≥0∞)
    (h : ∀ᵐ a ∂𝒟[mx], Pr{let b ← f a}[p b] ≤ (∑ i, F i a) + bound a) :
    Pr{let a ← mx; let b ← f a}[p b] ≤ (∑ i, wp⟦mx⟧ (F i)) + ∫⁻ a, bound a ∂𝒟[mx] :=
  wp_le_sum_add_lintegral_ae mx F (measurable_prEvent hf) hF bound h

variable [MonadAttach m] [WeaklyLawfulMonadAttach m]

/-- A reachable comparison with finitely many reference observations holds between their
expectations, retaining the allowance's successful-mass factor. -/
theorem wp_le_sum_add_mul_mass_of_support [Fintype ι] (mx : m α) {f : α → ℝ≥0∞}
    (F : ι → α → ℝ≥0∞) (ε : ℝ≥0∞) (h : ∀ a ∈ support mx, f a ≤ (∑ i, F i a) + ε) :
    wp⟦mx⟧ f ≤ (∑ i, wp⟦mx⟧ (F i)) + ε * Pr{let _ ← mx}[True] :=
  (wp_mono_of_support mx h).trans_eq <| by
    rw [ExpectationWP.wp_add, ExpectationWP.wp_finsetSum, wp_const]

/-- A reachable comparison with finitely many reference observations and a uniform allowance
holds between their expectations. -/
theorem wp_le_sum_add_of_support [Fintype ι] (mx : m α) {f : α → ℝ≥0∞} (F : ι → α → ℝ≥0∞)
    (ε : ℝ≥0∞) (h : ∀ a ∈ support mx, f a ≤ (∑ i, F i a) + ε) :
    wp⟦mx⟧ f ≤ (∑ i, wp⟦mx⟧ (F i)) + ε :=
  (wp_le_sum_add_mul_mass_of_support mx F ε h).trans <|
    add_le_add le_rfl ((mul_le_mul' le_rfl (prEvent_le_one _)).trans_eq (mul_one ε))

variable {γ : Type}

/-- A reachable comparison of a bounded observation with two others outside a disagreement
event charges the event's probability and a uniform allowance. -/
theorem wp_le_add_add_of_disagree {mx : m α} {f g h : α → ℝ≥0∞} {D : α → Prop}
    {ε₁ ε₂ : ℝ≥0∞} (hD : Pr{let x ← mx}[D x] ≤ ε₁) (hf : ∀ x, f x ≤ 1)
    (hfgh : ∀ x ∈ support mx, ¬D x → f x ≤ g x + h x + ε₂) :
    wp⟦mx⟧ f ≤ wp⟦mx⟧ g + wp⟦mx⟧ h + ε₁ + ε₂ := by
  calc wp⟦mx⟧ f
      ≤ wp⟦mx⟧ fun x ↦ g x + h x + propInd (D x) + ε₂ :=
        wp_mono_of_support mx fun x hx ↦ by
          by_cases hDx : D x
          · simp only [hDx, propInd_true]
            exact (hf x).trans (le_add_right le_add_self)
          · simpa only [hDx, propInd_false, add_zero] using hfgh x hx hDx
    _ ≤ wp⟦mx⟧ g + wp⟦mx⟧ h + Pr{let x ← mx}[D x] + ε₂ := by
        rw [ExpectationWP.wp_add, ExpectationWP.wp_add, ExpectationWP.wp_add,
          wp_const]
        exact add_le_add le_rfl (mul_le_of_le_one_right' (prEvent_le_one _))
    _ ≤ _ := by gcongr

/-- A reachable conditional comparison outside a disagreement event charges its probability
and a uniform allowance. -/
theorem prEvent_bind_le_add_of_disagree {mx : m α} {my oc : α → m β}
    {q : β → Prop} {D : α → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (hD : Pr{let x ← mx}[D x] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬D x →
      Pr{let y ← my x}[q y] ≤ Pr{let y ← oc x}[q y] + ε₂) :
    Pr{let x ← mx; let y ← my x}[q y] ≤ Pr{let x ← mx; let y ← oc x}[q y] + ε₁ + ε₂ := by
  calc Pr{let x ← mx; let y ← my x}[q y]
      ≤ wp⟦mx⟧ fun x ↦ Pr{let y ← oc x}[q y] + propInd (D x) + ε₂ :=
        wp_mono_of_support mx fun x hx ↦ by
          by_cases hDx : D x
          · simp only [hDx, propInd_true]
            exact (prEvent_le_one _).trans (le_add_right le_add_self)
          · simpa only [hDx, propInd_false, add_zero] using h x hx hDx
    _ ≤ Pr{let x ← mx; let y ← oc x}[q y] + Pr{let x ← mx}[D x] + ε₂ := by
        rw [ExpectationWP.wp_add, ExpectationWP.wp_add, wp_const]
        exact add_le_add le_rfl (mul_le_of_le_one_right' (prEvent_le_one _))
    _ ≤ _ := by gcongr

/-- A bad world that certainly fires on disagreement absorbs that event's charge. The
good-branch comparison may already contain the conditional bad-world probability. -/
theorem prEvent_bind_le_add_bad_of_disagree' {mx : m α}
    {my oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → Pr{let z ← ob x}[r z] = 1)
    (h : ∀ x ∈ support mx, ¬D x → Pr{let y ← my x}[q y] ≤
      Pr{let y ← oc x}[q y] + Pr{let z ← ob x}[r z] + ε) :
    Pr{let x ← mx; let y ← my x}[q y] ≤
      Pr{let x ← mx; let y ← oc x}[q y] + Pr{let x ← mx; let z ← ob x}[r z] + ε := by
  calc Pr{let x ← mx; let y ← my x}[q y]
      ≤ wp⟦mx⟧ fun x ↦ Pr{let y ← oc x}[q y] + Pr{let z ← ob x}[r z] + ε :=
        wp_mono_of_support mx fun x hx ↦ by
          by_cases hDx : D x
          · rw [hbad x hx hDx]
            exact (prEvent_le_one _).trans (le_add_right le_add_self)
          · exact h x hx hDx
    _ ≤ _ := by
        rw [ExpectationWP.wp_add, ExpectationWP.wp_add, wp_const]
        exact add_le_add le_rfl (mul_le_of_le_one_right' (prEvent_le_one _))

/-- A bad world that certainly fires on disagreement pays for the exceptional branches. -/
theorem prEvent_bind_le_add_bad_of_disagree {mx : m α}
    {my oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → Pr{let z ← ob x}[r z] = 1)
    (h : ∀ x ∈ support mx, ¬D x →
      Pr{let y ← my x}[q y] ≤ Pr{let y ← oc x}[q y] + ε) :
    Pr{let x ← mx; let y ← my x}[q y] ≤
      Pr{let x ← mx; let y ← oc x}[q y] + Pr{let x ← mx; let z ← ob x}[r z] + ε :=
  prEvent_bind_le_add_bad_of_disagree' hbad fun x hx hDx ↦
    (h x hx hDx).trans (add_le_add (le_add_right le_rfl) le_rfl)

/-- Disagreement and a separate conditional bad world are both charged after a shared prefix. -/
theorem prEvent_bind_le_add_bad_disagree {mx : m α}
    {my oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (hD : Pr{let x ← mx}[D x] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬D x → Pr{let y ← my x}[q y] ≤
      Pr{let y ← oc x}[q y] + Pr{let z ← ob x}[r z] + ε₂) :
    Pr{let x ← mx; let y ← my x}[q y] ≤ Pr{let x ← mx; let y ← oc x}[q y] +
      Pr{let x ← mx; let z ← ob x}[r z] + ε₁ + ε₂ := by
  calc Pr{let x ← mx; let y ← my x}[q y]
      ≤ wp⟦mx⟧ fun x ↦ Pr{let y ← oc x}[q y] + Pr{let z ← ob x}[r z] + propInd (D x) + ε₂ :=
        wp_mono_of_support mx fun x hx ↦ by
          by_cases hDx : D x
          · simp only [hDx, propInd_true]
            exact (prEvent_le_one _).trans (le_add_right le_add_self)
          · simpa only [hDx, propInd_false, add_zero] using h x hx hDx
    _ ≤ Pr{let x ← mx; let y ← oc x}[q y] + Pr{let x ← mx; let z ← ob x}[r z] +
          Pr{let x ← mx}[D x] + ε₂ := by
        rw [ExpectationWP.wp_add, ExpectationWP.wp_add, ExpectationWP.wp_add,
          wp_const]
        exact add_le_add le_rfl (mul_le_of_le_one_right' (prEvent_le_one _))
    _ ≤ _ := by gcongr
