/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.Measure.TotalVariation.Bind
public import ToMathlib.Probability.Kernel.Subprobability

/-!
# Statistical distance for composed kernels

Mathlib kernel composition obeys the measure-level contraction and conditional-majorant laws of
the statistical distance `Measure.statEDist` at each input. Majorants are integrated under the
actual intermediate kernel law; no measurability of a conditional distance function or choice of
coupling witnesses is assumed.
-/

public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {ρ α β : Type*}
  [MeasurableSpace ρ] [MeasurableSpace α] [MeasurableSpace β]

/-- A common subprobability transition contracts the statistical distance of the input-indexed
laws. -/
theorem statEDist_comp_le (κ η : Kernel ρ α) (τ : Kernel α β)
    [IsSubprobabilityKernel τ] (r : ρ) :
    ((τ ∘ₖ κ) r).statEDist ((τ ∘ₖ η) r) ≤ (κ r).statEDist (η r) := by
  rw [comp_apply, comp_apply]
  exact Measure.statEDist_bind_le (κ r) (η r) τ τ.measurable

/-- The statistical distance of the composed laws is bounded by an AE majorant of the conditional
distance integrated over the prefix kernel. -/
theorem statEDist_comp_comp_le_lintegral (κ : Kernel ρ α) (η τ : Kernel α β)
    (r : ρ) (bound : α → ENNReal)
    (hbound : ∀ᵐ a ∂κ r, (η a).statEDist (τ a) ≤ bound a) :
    ((η ∘ₖ κ) r).statEDist ((τ ∘ₖ κ) r) ≤ ∫⁻ a, bound a ∂κ r := by
  rw [comp_apply, comp_apply]
  exact Measure.statEDist_bind_bind_le_lintegral (κ r) η τ
    η.aemeasurable τ.aemeasurable bound hbound

/-- Compose different prefix kernels and transitions, integrating the conditional statistical
distance under the second intermediate law. -/
theorem statEDist_comp_comp_le_add_lintegral (κ ξ : Kernel ρ α) (η τ : Kernel α β)
    [IsSubprobabilityKernel η] (r : ρ) (bound : α → ENNReal)
    (hbound : ∀ᵐ a ∂ξ r, (η a).statEDist (τ a) ≤ bound a) :
    ((η ∘ₖ κ) r).statEDist ((τ ∘ₖ ξ) r) ≤
      (κ r).statEDist (ξ r) + ∫⁻ a, bound a ∂ξ r := by
  rw [comp_apply, comp_apply]
  exact Measure.statEDist_bind_bind_le_add_lintegral (κ r) (ξ r) η τ
    η.measurable τ.aemeasurable bound hbound

/-- A conditional exceptional event is charged at its intermediate kernel mass. -/
theorem statEDist_comp_comp_le_of_bad (κ : Kernel ρ α) (η τ : Kernel α β)
    [IsSubprobabilityKernel η] [IsSubprobabilityKernel τ]
    (r : ρ) {bad : Set α} (hbad : MeasurableSet bad) (ε : ENNReal)
    (hgood : ∀ᵐ a ∂κ r, a ∉ bad → (η a).statEDist (τ a) ≤ ε) :
    ((η ∘ₖ κ) r).statEDist ((τ ∘ₖ κ) r) ≤ (κ r) bad + ε * (κ r) badᶜ := by
  rw [comp_apply, comp_apply]
  exact Measure.statEDist_bind_bind_le_of_bad (κ r) η τ
    η.aemeasurable τ.aemeasurable hbad ε hgood

end ProbabilityTheory.Kernel
