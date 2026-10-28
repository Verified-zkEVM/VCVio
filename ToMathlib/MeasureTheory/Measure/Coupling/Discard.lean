/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Coupling.Residual
public import ToMathlib.MeasureTheory.Measure.Subprobability

/-!
# State-law comparison by discarding an exceptional region

Two measurable continuations agreeing outside an exceptional region admit an explicit
subcoupling: run their common continuation on the retained region and keep the discarded left
execution as residual. The loss is measured under the initial law, and successful-output mass
may decrease in either continuation.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A common continuation on a measurable region gives an explicit diagonal subcoupling of
the two bound state laws. Its residual is the left continuation on the discarded region. -/
theorem IsSubcouplingWithResidual.discard (μ : Measure α) {k l : α → Measure β}
    (hk : Measurable k) (hl : Measurable l) {good : Set α} (hgood : MeasurableSet good)
    (heq : ∀ᵐ x ∂μ, x ∈ good → k x = l x) :
    IsSubcouplingWithResidual (((μ.restrict good).bind k).map fun x => (x, x))
      ((μ.restrict goodᶜ).bind k) (μ.bind k) (μ.bind l) := by
  have hretained : (μ.restrict good).bind k = (μ.restrict good).bind l := by
    apply bind_congr_right
    filter_upwards [heq.filter_mono (ae_mono restrict_le_self), ae_restrict_mem hgood] with x hx hg
    exact hx hg
  constructor
  · rw [(IsCoupling.refl ((μ.restrict good).bind k)).fst_eq,
      ← bind_add_left _ _ hk, restrict_add_restrict_compl hgood]
  · rw [(IsCoupling.refl ((μ.restrict good).bind k)).snd_eq, hretained]
    exact bind_mono_left restrict_le_self hl

/-- A subprobability continuation cannot increase the mass of a discarded initial region. -/
theorem bind_restrict_apply_univ_le (μ : Measure α) {k : α → Measure β}
    (hk : Measurable k) [∀ x, IsSubprobabilityMeasure (k x)] (bad : Set α) :
    ((μ.restrict bad).bind k) Set.univ ≤ μ bad := by
  rw [bind_apply MeasurableSet.univ hk.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : α, (1 : ℝ≥0∞) ∂μ.restrict bad := lintegral_mono fun x => measure_univ_le _
    _ = μ bad := by simp

/-- Discarding an exceptional initial-state region bounds event loss by that region's mass.
The local agreement is almost everywhere and no losslessness assumption is required. -/
theorem bind_apply_le_of_discard (μ : Measure α) {k l : α → Measure β}
    (hk : Measurable k) (hl : Measurable l) [∀ x, IsSubprobabilityMeasure (k x)]
    {bad : Set α} (hbad : MeasurableSet bad)
    (heq : ∀ᵐ x ∂μ, x ∉ bad → k x = l x) {event : Set β} (hevent : MeasurableSet event) :
    (μ.bind k) event ≤ (μ.bind l) event + μ bad := by
  have hc := IsSubcouplingWithResidual.discard μ hk hl hbad.compl heq
  have hpost : ∀ᵐ z ∂((μ.restrict badᶜ).bind k).map (fun x => (x, x)),
      z.1 ∈ event → z.2 ∈ event := by
    apply (ae_map_iff (measurable_id.prodMk measurable_id).aemeasurable
      (by measurability)).2
    exact Filter.Eventually.of_forall fun _ h => h
  have h := hc.event_le_add_residual hevent hevent hpost
  simp only [compl_compl] at h
  exact h.trans (add_le_add le_rfl (bind_restrict_apply_univ_le μ hk bad))

end MeasureTheory.Measure
