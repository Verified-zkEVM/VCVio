/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.Measure.OmegaCompletePartialOrder
public import ToMathlib.Probability.Kernel.Subprobability

/-!
# Increasing limits of kernels

The pointwise supremum of an increasing sequence of kernels remains a kernel.
This supplies the omega-complete order needed for least continuous interpretations
of stateful services. Kernel composition is continuous in each argument.
-/

public section

open MeasureTheory OmegaCompletePartialOrder

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Increasing kernel limits are taken pointwise as increasing limits of measures. -/
noncomputable instance instOmegaCompletePartialOrder : OmegaCompletePartialOrder (Kernel α β) where
  ωSup c := ⟨fun a => ⨆ n, c n a,
    Measure.measurable_iSup_of_monotone (fun n => (c n).measurable)
      (fun _ _ h a => c.monotone h a)⟩
  le_ωSup c n a := le_iSup (fun k => c k a) n
  ωSup_le _ _ h a := iSup_le fun n => h n a

/-- Increasing kernel suprema agree pointwise with measure suprema. -/
theorem ωSup_apply (c : Chain (Kernel α β)) (a : α) :
    ωSup c a = ⨆ n, c n a := by rfl

/-- An increasing limit of subprobability kernels is a subprobability kernel. -/
instance isSubprobabilityKernel_ωSup (c : Chain (Kernel α β))
    [∀ n, IsSubprobabilityKernel (c n)] : IsSubprobabilityKernel (ωSup c) := by
  constructor
  intro a
  rw [ωSup_apply]
  have hm : Monotone (fun n : ℕ => c n a) := fun _ _ h => c.monotone h a
  rw [Measure.iSup_apply_of_monotone _ hm _ MeasurableSet.univ]
  exact iSup_le fun n => (c n).measure_univ_le a

/-- Postcomposition with a fixed kernel preserves increasing limits. -/
theorem comp_ωSup_right (η : Kernel β γ) (c : Chain (Kernel α β)) :
    η ∘ₖ ωSup c = ωSup (c.map ⟨fun κ => η ∘ₖ κ, fun _ _ h a => by
      simp only [comp_apply]
      exact Measure.bind_mono_left_of_measurable (h a) η.measurable⟩) := by
  ext a : 1
  rw [comp_apply, ωSup_apply, ωSup_apply]
  change (⨆ n, c n a).bind η = ⨆ n, (η ∘ₖ c n) a
  simp_rw [comp_apply]
  exact Measure.bind_iSup_left (fun n => c n a) (fun _ _ h => c.monotone h a) η.measurable

/-- Composition is continuous in the first kernel executed. -/
noncomputable def compContinuousRight (η : Kernel β γ) : Kernel α β →𝒄 Kernel α γ :=
  .ofFun (fun κ => η ∘ₖ κ) (by
    apply ωScottContinuous.of_monotone_map_ωSup
    refine ⟨fun _ _ h a => ?_, fun c => comp_ωSup_right η c⟩
    simp only [comp_apply]
    exact Measure.bind_mono_left_of_measurable (h a) η.measurable)

/-- Composition is continuous in the continuation kernel. -/
noncomputable def compContinuousLeft (κ : Kernel α β) : Kernel β γ →𝒄 Kernel α γ :=
  .ofFun (fun η => η ∘ₖ κ) (by
    apply ωScottContinuous.of_monotone_map_ωSup
    refine ⟨fun η η' h a => ?_, ?_⟩
    · simp only [comp_apply]
      exact Measure.bind_mono_right_of_forall η.measurable.aemeasurable
        η'.measurable.aemeasurable h
    · intro c
      ext a : 1
      rw [comp_apply, ωSup_apply]
      change (κ a).bind (fun b => ωSup c b) = ⨆ n, (c n ∘ₖ κ) a
      simp_rw [ωSup_apply, comp_apply]
      have hm : Monotone (fun n : ℕ => (c n : β → Measure γ)) := fun _ _ h => c.monotone h
      exact Measure.bind_iSup_right (κ a) (fun n => (c n).measurable) hm)

@[simp] theorem compContinuousRight_apply (η : Kernel β γ) (κ : Kernel α β) :
    compContinuousRight η κ = η ∘ₖ κ := by rfl

@[simp] theorem compContinuousLeft_apply (κ : Kernel α β) (η : Kernel β γ) :
    compContinuousLeft κ η = η ∘ₖ κ := by rfl

/-- Select a kernel by a countable first coordinate and run it at the second coordinate. -/
noncomputable def uncurryCountable [Countable α] [MeasurableSingletonClass α] :
    (α → Kernel β γ) →𝒄 Kernel (α × β) γ :=
  .ofFun (fun f => ⟨fun x => f x.1 x.2,
    measurable_from_prod_countable_right (fun a => (f a).measurable)⟩) (by
      apply ωScottContinuous.of_monotone_map_ωSup
      refine ⟨fun _ _ h x => h x.1 x.2, ?_⟩
      intro c
      ext x : 1
      change (ωSup (c.map (Pi.evalOrderHom x.1))) x.2 = _
      rw [ωSup_apply, ωSup_apply]
      rfl)

@[simp] theorem uncurryCountable_apply [Countable α] [MeasurableSingletonClass α]
    (f : α → Kernel β γ) (x : α × β) : uncurryCountable f x = f x.1 x.2 := by rfl

end ProbabilityTheory.Kernel
