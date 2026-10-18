/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Measurable observations of a kernel's input and output

An observation can retain input information together with the sampled result.
Its law is measurable in the input, and integrating these laws is the pushforward
of the joint input/output measure.
-/

public section

open MeasureTheory ProbabilityTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A jointly measurable observation may depend on both a kernel's input and its output. -/
theorem ProbabilityTheory.Kernel.measurable_map_withInput (κ : Kernel α β)
    [IsSFiniteKernel κ] {f : α × β → γ} (hf : Measurable f) :
    Measurable (fun a => (κ a).map (fun b => f (a, b))) := by
  refine Measure.measurable_of_measurable_coe _ fun event hevent => ?_
  convert Kernel.measurable_kernel_prodMk_left (κ := κ) (hf hevent) using 1
  funext a
  exact Measure.map_apply (hf.comp measurable_prodMk_left) hevent

/-- Observing a joint input/output law agrees with binding the observed conditional laws. -/
theorem MeasureTheory.Measure.map_compProd_eq_bind (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] {f : α × β → γ} (hf : Measurable f) :
    (μ ⊗ₘ κ).map f = μ.bind (fun a => (κ a).map (fun b => f (a, b))) := by
  ext event hevent
  rw [Measure.map_apply hf hevent, Measure.compProd_apply (hf hevent),
    Measure.bind_apply hevent (κ.measurable_map_withInput hf).aemeasurable]
  apply lintegral_congr
  intro a
  exact (Measure.map_apply (hf.comp measurable_prodMk_left) hevent).symm
