/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.Measure.Monotone
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Continuous operations on increasing chains of measures

Increasing limits are measurable and commute with Giry bind in either argument.
The continuation argument is bundled as a continuous map when the source has
the discrete sigma algebra. The measure argument needs only a measurable
continuation, so continuous result spaces remain available.
-/

public section

open MeasureTheory OmegaCompletePartialOrder

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- An increasing pointwise supremum of measurable measure-valued maps is measurable. -/
theorem measurable_iSup_of_monotone {f : ℕ → α → Measure β}
    (hf : ∀ n, Measurable (f n)) (hm : Monotone f) :
    Measurable (fun a => ⨆ n, f n a) := by
  apply measurable_of_measurable_coe
  intro s hs
  simp_rw [iSup_apply_of_monotone _ (fun _ _ h => hm h _) s hs]
  exact Measurable.iSup fun n => (measurable_coe hs).comp (hf n)

/-- Giry bind commutes with an increasing sequence of measurable continuations. -/
theorem bind_iSup_right (μ : Measure α) {f : ℕ → α → Measure β}
    (hf : ∀ n, Measurable (f n)) (hm : Monotone f) :
    μ.bind (fun a => ⨆ n, f n a) = ⨆ n, μ.bind (f n) := by
  ext s hs
  rw [bind_apply hs (measurable_iSup_of_monotone hf hm).aemeasurable,
    iSup_apply_of_monotone _ (fun i j hij =>
      bind_mono_right_of_forall (hf i).aemeasurable (hf j).aemeasurable (hm hij)) s hs]
  simp_rw [iSup_apply_of_monotone _ (fun _ _ h => hm h _) s hs,
    bind_apply hs (hf _).aemeasurable]
  exact lintegral_iSup (fun n => (measurable_coe hs).comp (hf n))
    (fun _ _ hij a => hm hij a s)

/-- Nonnegative integration commutes with increasing limits of measures. -/
theorem lintegral_iSup_measure (μ : ℕ → Measure α) (hm : Monotone μ)
    {f : α → ENNReal} (hf : Measurable f) :
    ∫⁻ a, f a ∂(⨆ n, μ n) = ⨆ n, ∫⁻ a, f a ∂μ n := by
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hf, SimpleFunc.lintegral,
    iSup_apply_of_monotone μ hm _ (SimpleFunc.measurableSet_preimage _ _), ENNReal.mul_iSup]
  rw [iSup_comm]
  congr 1
  funext k
  exact ENNReal.finsetSum_iSup_of_monotone fun x i j hij => by
    gcongr
    exact hm hij

/-- Bind into a measurable continuation preserves order of input measures. -/
theorem bind_mono_left_of_measurable {μ ν : Measure α} (h : μ ≤ ν)
    {f : α → Measure β} (hf : Measurable f) : μ.bind f ≤ ν.bind f := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [bind_apply hs hf.aemeasurable, bind_apply hs hf.aemeasurable]
  exact lintegral_mono' h le_rfl

/-- Giry bind commutes with increasing limits of its input measure. -/
theorem bind_iSup_left (μ : ℕ → Measure α) (hm : Monotone μ)
    {f : α → Measure β} (hf : Measurable f) :
    (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  ext s hs
  rw [bind_apply hs hf.aemeasurable,
    iSup_apply_of_monotone _ (fun _ _ h => bind_mono_left_of_measurable (hm h) hf) s hs]
  simp_rw [bind_apply hs hf.aemeasurable]
  exact lintegral_iSup_measure μ hm ((measurable_coe hs).comp hf)

/-- Bind into a fixed measurable continuation is continuous in the input measure. -/
noncomputable def bindContinuousLeft {f : α → Measure β} (hf : Measurable f) :
    Measure α →𝒄 Measure β :=
  .ofFun (fun μ => μ.bind f) (by
    apply ωScottContinuous.of_monotone_map_ωSup
    refine ⟨fun _ _ h => bind_mono_left_of_measurable h hf, ?_⟩
    intro c
    exact bind_iSup_left c c.monotone hf)

@[simp] theorem bindContinuousLeft_apply {f : α → Measure β} (hf : Measurable f)
    (μ : Measure α) : bindContinuousLeft hf μ = μ.bind f := by rfl

/-- A discrete answer measure is a continuous algebra in its continuation meanings. -/
noncomputable def bindContinuousRight [DiscreteMeasurableSpace α] (μ : Measure α) :
    (α → Measure β) →𝒄 Measure β :=
  .ofFun (fun f => μ.bind f) (by
    apply ωScottContinuous.of_monotone_map_ωSup
    refine ⟨fun _ _ h => bind_mono_right_of_forall
      Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable h, ?_⟩
    intro c
    exact bind_iSup_right μ (fun _ => Measurable.of_discrete) c.monotone)

@[simp] theorem bindContinuousRight_apply [DiscreteMeasurableSpace α] (μ : Measure α)
    (f : α → Measure β) : bindContinuousRight μ f = μ.bind f := by rfl

end MeasureTheory.Measure
