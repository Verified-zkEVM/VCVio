/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import ToMathlib.MeasureTheory.Integral.AbsDiff
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Total variation under measurable sequential composition

Bounded measurable observations are controlled by event total variation through the layer cake
formula. Measurable subprobability transitions contract total variation. Conditional comparisons
use explicit measurable majorants and almost-everywhere premises on the actual prefix law.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A bounded nonnegative observation has a layer cake integral over the unit interval. -/
theorem lintegral_eq_lintegral_Ioc_meas_lt_of_le_one (μ : Measure α)
    (f : α → ENNReal) (hf : Measurable f) (hbound : ∀ a, f a ≤ 1) :
    ∫⁻ a, f a ∂μ = ∫⁻ t : ℝ in Ioc 0 1, μ {a | t < (f a).toReal} := by
  have hfin (a : α) : f a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hbound a)
  have hreal (a : α) : (f a).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hbound a)
  calc
    _ = ∫⁻ a, ENNReal.ofReal (f a).toReal ∂μ := by simp only [ENNReal.ofReal_toReal (hfin _)]
    _ = ∫⁻ t : ℝ in Ioi 0, μ {a | t < (f a).toReal} :=
      lintegral_eq_lintegral_meas_lt μ
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hf.ennreal_toReal.aemeasurable
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro t
      by_cases ht : 0 < t
      · by_cases ht' : t ≤ 1
        · simp [ht, ht']
        · have hempty : {a : α | t < (f a).toReal} = ∅ := by
            ext a
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
            exact not_lt_of_ge ((hreal a).trans (le_of_not_ge ht'))
          simp [ht, ht', hempty]
      · simp [ht]

/-- Total variation bounds the increase of a bounded measurable nonnegative observation. -/
theorem lintegral_le_add_etvDist (μ ν : Measure α) (f : α → ENNReal)
    (hf : Measurable f) (hbound : ∀ a, f a ≤ 1) :
    ∫⁻ a, f a ∂μ ≤ (∫⁻ a, f a ∂ν) + μ.etvDist ν := by
  have htail (t : ℝ) :
      μ {a | t < (f a).toReal} ≤ ν {a | t < (f a).toReal} + μ.etvDist ν := by
    have h := absDiff_apply_le_etvDist μ ν (s := {a | t < (f a).toReal})
      (measurableSet_lt measurable_const hf.ennreal_toReal)
    have hsub : μ {a | t < (f a).toReal} - ν {a | t < (f a).toReal} ≤ μ.etvDist ν :=
      (le_add_right le_rfl).trans h
    simpa only [add_comm] using tsub_le_iff_right.mp hsub
  have hmeas : Measurable (fun t : ℝ ↦ ν {a | t < (f a).toReal}) :=
    (show Antitone (fun t : ℝ ↦ ν {a | t < (f a).toReal}) from
      fun t u htu ↦ measure_mono fun a ha ↦ htu.trans_lt ha).measurable
  rw [lintegral_eq_lintegral_Ioc_meas_lt_of_le_one μ f hf hbound,
    lintegral_eq_lintegral_Ioc_meas_lt_of_le_one ν f hf hbound]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioc 0 1,
        ν {a | t < (f a).toReal} + μ.etvDist ν := lintegral_mono htail
    _ = _ := by rw [lintegral_add_left hmeas, lintegral_const]; simp

/-- Event total variation controls every bounded measurable nonnegative observation. -/
theorem absDiff_lintegral_le_etvDist (μ ν : Measure α) (f : α → ENNReal)
    (hf : Measurable f) (hbound : ∀ a, f a ≤ 1) :
    ENNReal.absDiff (∫⁻ a, f a ∂μ) (∫⁻ a, f a ∂ν) ≤ μ.etvDist ν := by
  rw [ENNReal.absDiff_eq_edist, ENNReal.edist_le_iff_le_add_right]
  exact ⟨lintegral_le_add_etvDist μ ν f hf hbound,
    by simpa only [etvDist_comm ν μ] using lintegral_le_add_etvDist ν μ f hf hbound⟩

/-- A common measurable subprobability transition contracts event total variation. -/
theorem etvDist_bind_le (μ ν : Measure α) (k : α → Measure β) (hk : Measurable k)
    [∀ a, IsSubprobabilityMeasure (k a)] :
    (μ.bind k).etvDist (ν.bind k) ≤ μ.etvDist ν := by
  refine iSup_le fun s ↦ ?_
  rw [bind_apply s.2 hk.aemeasurable, bind_apply s.2 hk.aemeasurable]
  exact absDiff_lintegral_le_etvDist μ ν (fun a ↦ k a s.1)
    ((measurable_coe s.2).comp hk) (fun a ↦ measure_le_one (k a) s.1)

/-- Integrating an AE majorant bounds conditional variation without a measurable distance
function or a measurable selection of couplings. -/
theorem etvDist_bind_bind_le_lintegral (μ : Measure α) (k l : α → Measure β)
    (hk : AEMeasurable k μ) (hl : AEMeasurable l μ) (bound : α → ENNReal)
    (hbound : ∀ᵐ a ∂μ, (k a).etvDist (l a) ≤ bound a) :
    (μ.bind k).etvDist (μ.bind l) ≤ ∫⁻ a, bound a ∂μ := by
  refine iSup_le fun s ↦ ?_
  rw [bind_apply s.2 hk, bind_apply s.2 hl]
  refine (ENNReal.absDiff_lintegral_le μ
    ((measurable_coe s.2).comp_aemeasurable hk)
    ((measurable_coe s.2).comp_aemeasurable hl)).trans ?_
  apply lintegral_mono_ae
  exact hbound.mono fun a ha ↦ (absDiff_apply_le_etvDist (k a) (l a) s.2).trans ha

/-- Vary both the prefix law and the transition, with the conditional bound integrated under
the actual second prefix law. -/
theorem etvDist_bind_bind_le_add_lintegral (μ ν : Measure α) (k l : α → Measure β)
    (hk : Measurable k) (hl : AEMeasurable l ν)
    [∀ a, IsSubprobabilityMeasure (k a)] (bound : α → ENNReal)
    (hbound : ∀ᵐ a ∂ν, (k a).etvDist (l a) ≤ bound a) :
    (μ.bind k).etvDist (ν.bind l) ≤ μ.etvDist ν + ∫⁻ a, bound a ∂ν :=
  (etvDist_triangle _ (ν.bind k) _).trans <| add_le_add
    (etvDist_bind_le μ ν k hk)
    (etvDist_bind_bind_le_lintegral ν k l hk.aemeasurable hl bound hbound)

/-- Charge arbitrary conditional behavior on a measurable exceptional event, and integrate
the conditional majorant only over its complement. -/
theorem etvDist_bind_bind_le_add_lintegral_of_bad (μ : Measure α) (k l : α → Measure β)
    (hk : AEMeasurable k μ) (hl : AEMeasurable l μ)
    [∀ a, IsSubprobabilityMeasure (k a)] [∀ a, IsSubprobabilityMeasure (l a)]
    {bad : Set α} (hbad : MeasurableSet bad) (bound : α → ENNReal)
    (hgood : ∀ᵐ a ∂μ, a ∉ bad → (k a).etvDist (l a) ≤ bound a) :
    (μ.bind k).etvDist (μ.bind l) ≤ μ bad + ∫⁻ a in badᶜ, bound a ∂μ := by
  calc
    _ ≤ ∫⁻ a, bad.indicator 1 a + badᶜ.indicator bound a ∂μ := by
      apply etvDist_bind_bind_le_lintegral μ k l hk hl
      filter_upwards [hgood] with a ha
      by_cases h : a ∈ bad
      · simpa [h] using etvDist_le_one (k a) (l a) (measure_univ_le _) (measure_univ_le _)
      · simpa [h] using ha h
    _ = _ := by
      rw [lintegral_add_left (measurable_one.indicator hbad), lintegral_indicator_one hbad,
        lintegral_indicator hbad.compl]

/-- A constant conditional allowance retains the mass of the nonexceptional prefix. -/
theorem etvDist_bind_bind_le_of_bad (μ : Measure α) (k l : α → Measure β)
    (hk : AEMeasurable k μ) (hl : AEMeasurable l μ)
    [∀ a, IsSubprobabilityMeasure (k a)] [∀ a, IsSubprobabilityMeasure (l a)]
    {bad : Set α} (hbad : MeasurableSet bad) (ε : ENNReal)
    (hgood : ∀ᵐ a ∂μ, a ∉ bad → (k a).etvDist (l a) ≤ ε) :
    (μ.bind k).etvDist (μ.bind l) ≤ μ bad + ε * μ badᶜ := by
  simpa only [lintegral_const, restrict_apply_univ] using
    etvDist_bind_bind_le_add_lintegral_of_bad μ k l hk hl hbad (fun _ ↦ ε) hgood

/-- Measurable subprobability transitions contract real-valued total variation. -/
theorem tvDist_bind_le (μ ν : Measure α) [IsSubprobabilityMeasure μ]
    [IsSubprobabilityMeasure ν] (k : α → Measure β) (hk : Measurable k)
    [∀ a, IsSubprobabilityMeasure (k a)] :
    (μ.bind k).tvDist (ν.bind k) ≤ μ.tvDist ν := by
  exact ENNReal.toReal_mono (etvDist_ne_top μ ν (measure_univ_le _) (measure_univ_le _))
    (etvDist_bind_le μ ν k hk)

/-- A finite integrated majorant bounds real-valued conditional variation. -/
theorem tvDist_bind_bind_le_lintegral (μ : Measure α) (k l : α → Measure β)
    (hk : AEMeasurable k μ) (hl : AEMeasurable l μ) (bound : α → ENNReal)
    (hbound : ∀ᵐ a ∂μ, (k a).etvDist (l a) ≤ bound a)
    (hfinite : (∫⁻ a, bound a ∂μ) ≠ ⊤) :
    (μ.bind k).tvDist (μ.bind l) ≤ (∫⁻ a, bound a ∂μ).toReal :=
  ENNReal.toReal_mono hfinite (etvDist_bind_bind_le_lintegral μ k l hk hl bound hbound)

end MeasureTheory.Measure
