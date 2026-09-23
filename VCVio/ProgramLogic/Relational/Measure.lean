/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.MeasureTheory.Measure.Coupling
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Measure-native relational program logic

This module establishes the foundational relational semantics directly over couplings of Mathlib
measures. The postcondition holds almost everywhere under the joint measure, which is the
appropriate notion for continuous distributions: it does not mistake a zero-mass singleton for an
impossible output.

`eRelWP` is the quantitative counterpart. It takes a supremum over measure couplings and
integrates the post-expectation with `lintegral`. Neither definition depends on a finite
distribution, countable support, or point probabilities. Witness constructors, reflexivity, and
monotonicity are provided here. `VCVio.ProgramLogic.Relational.Measure.Bind` gives sequential
composition with explicit measurable conditional couplings, while
`VCVio.ProgramLogic.Relational.KernelHandler` lifts local contracts through polynomial programs.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

universe u v w₁ w₂

namespace MeasureProgramLogic

variable {α : Type u} {β : Type v}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- A relation holds under some coupling of `μ` and `ν`, almost everywhere. -/
def CouplingPost (μ : Measure α) (ν : Measure β) (R : α → β → Prop) : Prop :=
  ∃ c : Measure.Coupling μ ν, ∀ᵐ z ∂c.joint, R z.1 z.2

/-- Measure-native relational weakest precondition for two denoted computations. -/
def RelWP {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (R : α → β → Prop) : Prop :=
  CouplingPost 𝒟[mx] 𝒟[my] R

/-- Quantitative relational WP: best coupled expectation of `g`. -/
noncomputable def eRelWP {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ c : Measure.Coupling 𝒟[mx] 𝒟[my], ∫⁻ z, g z.1 z.2 ∂c.joint

/-- Postcondition monotonicity for measure couplings. -/
theorem CouplingPost.mono {μ : Measure α} {ν : Measure β} {R S : α → β → Prop}
    (h : CouplingPost μ ν R) (hRS : ∀ a b, R a b → S a b) :
    CouplingPost μ ν S := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono fun z hz => hRS z.1 z.2 hz⟩

/-- Implication of relations preserves a measure-native relational judgment. -/
theorem relWP_mono {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    {mx : m₁ α} {my : m₂ β} {R S : α → β → Prop}
    (h : RelWP mx my R) (hRS : ∀ a b, R a b → S a b) : RelWP mx my S :=
  h.mono hRS

/-- Quantitative post-expectation monotonicity. -/
@[gcongr low]
theorem eRelWP_mono {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) {g h : α → β → ℝ≥0∞}
    (hgh : ∀ a b, g a b ≤ h a b) :
    eRelWP mx my g ≤ eRelWP mx my h := by
  refine iSup_mono fun c => ?_
  exact lintegral_mono fun z => hgh z.1 z.2

/-- A concrete measure coupling provides a falsifiable lower bound on the quantitative WP. -/
theorem le_eRelWP_of_isCoupling {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞)
    (c : Measure.Coupling 𝒟[mx] 𝒟[my]) :
    (∫⁻ z, g z.1 z.2 ∂c.joint) ≤ eRelWP mx my g :=
  le_iSup (fun c' : Measure.Coupling 𝒟[mx] 𝒟[my] ↦
    ∫⁻ z, g z.1 z.2 ∂c'.1) c

/-- The Dirac coupling gives the expected lower bound for two pure computations. -/
theorem le_eRelWP_pure_pure
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) (g : α → β → ℝ≥0∞)
    (hg : Measurable fun z : α × β => g z.1 z.2) :
    g a b ≤ eRelWP (pure a : m₁ α) (pure b : m₂ β) g := by
  rw [eRelWP, evalDist_pure, evalDist_pure]
  have h := le_iSup
    (fun c : Measure.Coupling (Measure.dirac a) (Measure.dirac b) ↦
      ∫⁻ z, g z.1 z.2 ∂c.joint)
    (Measure.Coupling.dirac a b)
  rw [Measure.Coupling.dirac_joint] at h
  rw [lintegral_dirac' (a, b) hg] at h
  exact h

/-- Pure computations satisfy every relation true of their returned pair. -/
theorem relWP_pure_pure
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) {R : α → β → Prop}
    (hMeasurable : MeasurableSet {z : α × β | R z.1 z.2}) (hR : R a b) :
    RelWP (pure a : m₁ α) (pure b : m₂ β) R := by
  simp only [RelWP, evalDist_pure]
  refine ⟨Measure.Coupling.dirac a b, ?_⟩
  exact (ae_dirac_iff hMeasurable).2 hR

/-- The diagonal measure witnesses reflexivity of coupling semantics. -/
theorem couplingPost_refl [MeasurableEq α] (μ : Measure α) : CouplingPost μ μ (· = ·) := by
  refine ⟨Measure.Coupling.refl μ, ?_⟩
  exact (ae_map_iff (μ := μ) (measurable_id.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_snd)).2
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Countable concentration suffices for reflexivity even when equality is not globally
measurable in the product space. -/
theorem couplingPost_refl_of_ae_mem_countable [MeasurableSingletonClass α]
    (μ : Measure α) {s : Set α} (hs : s.Countable) (hμ : ∀ᵐ a ∂μ, a ∈ s) :
    CouplingPost μ μ (· = ·) := by
  have hevent : MeasurableSet {z : α × α | (z.1 ∈ s ∧ z.2 ∈ s) ∧ z.1 = z.2} :=
    ((hs.prod hs).mono fun _ hz ↦ hz.1).measurableSet
  refine ⟨Measure.Coupling.refl μ, ?_⟩
  rw [Measure.Coupling.refl_joint]
  exact ((ae_map_iff (μ := μ) (measurable_id.prodMk measurable_id).aemeasurable
    hevent).2 (hμ.mono fun _ ha ↦ ⟨⟨ha, ha⟩, rfl⟩)).mono fun _ h ↦ h.2

/-- Every computation is related to itself by equality. -/
theorem relWP_refl {m : Type u → Type w₁} [EvalDistSemantics m] [MeasurableEq α] (mx : m α) :
    RelWP mx mx (· = ·) :=
  couplingPost_refl 𝒟[mx]

/-- A countably concentrated output law admits a reflexive relational witness. -/
theorem relWP_refl_of_ae_mem_countable {m : Type u → Type w₁}
    [EvalDistSemantics m] [MeasurableSingletonClass α]
    (mx : m α) {s : Set α} (hs : s.Countable) (h : ∀ᵐ a ∂𝒟[mx], a ∈ s) :
    RelWP mx mx (· = ·) := couplingPost_refl_of_ae_mem_countable 𝒟[mx] hs h

/-- A zero post-expectation has zero coupled expectation, including when no coupling exists. -/
@[simp]
theorem eRelWP_zero {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β) :
    eRelWP mx my (fun _ _ ↦ 0) = 0 := by
  simp [eRelWP]

/-- Coupling semantics cannot relate unequal successful-output masses. -/
theorem not_relWP_of_mass_ne {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β)
    (h : 𝒟[mx] Set.univ ≠ 𝒟[my] Set.univ) (R : α → β → Prop) : ¬RelWP mx my R := by
  rintro ⟨c, _⟩
  exact h c.isCoupling.apply_univ_eq

/-- The quantitative supremum is zero when unequal masses leave no coupling witnesses. -/
theorem eRelWP_eq_zero_of_mass_ne {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β)
    (h : 𝒟[mx] Set.univ ≠ 𝒟[my] Set.univ) (g : α → β → ℝ≥0∞) :
    eRelWP mx my g = 0 := by
  let : IsEmpty (Measure.Coupling 𝒟[mx] 𝒟[my]) := ⟨fun c ↦ h c.isCoupling.apply_univ_eq⟩
  simp [eRelWP]

/-- Coupled expectations respect any pointwise constant upper bound. -/
theorem eRelWP_le {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞) (bound : ℝ≥0∞)
    (h : ∀ a b, g a b ≤ bound) : eRelWP mx my g ≤ bound := by
  refine iSup_le fun c ↦ ?_
  calc
    (∫⁻ z, g z.1 z.2 ∂c.joint) ≤ ∫⁻ _ : α × β, bound ∂c.joint :=
      lintegral_mono fun z ↦ h z.1 z.2
    _ = bound * 𝒟[mx] Set.univ := by
      rw [lintegral_const, c.isCoupling.joint_apply_univ_eq_left]
    _ ≤ bound := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- Pure computations have their exact coupled post-expectation. -/
@[simp]
theorem eRelWP_pure_pure [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) (g : α → β → ℝ≥0∞) :
    eRelWP (pure a : m₁ α) (pure b : m₂ β) g = g a b := by
  rw [eRelWP, evalDist_pure, evalDist_pure]
  apply le_antisymm
  · refine iSup_le fun c ↦ ?_
    apply le_of_eq
    calc
      (∫⁻ z, g z.1 z.2 ∂c.joint) = ∫⁻ _ : α × β, g a b ∂c.joint :=
        lintegral_congr_ae ((c.isCoupling.ae_eq_pair_of_dirac a b).mono fun z hz ↦ by rw [hz])
      _ = g a b := by
        rw [lintegral_const, c.isCoupling.joint_apply_univ_eq_left, measure_univ, mul_one]
  · simpa only [Measure.Coupling.dirac_joint, lintegral_dirac] using le_iSup
      (fun c : Measure.Coupling (Measure.dirac a) (Measure.dirac b) ↦
        ∫⁻ z, g z.1 z.2 ∂c.joint) (Measure.Coupling.dirac a b)

/-- Pure computations satisfy exactly the relation on their returned values. -/
@[simp]
theorem relWP_pure_pure_iff [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) (R : α → β → Prop) :
    RelWP (pure a : m₁ α) (pure b : m₂ β) R ↔ R a b := by
  rw [RelWP, evalDist_pure, evalDist_pure, CouplingPost]
  constructor
  · rintro ⟨c, hc⟩
    have hpair := c.isCoupling.ae_eq_pair_of_dirac a b
    obtain ⟨z, hz, hR⟩ := (hpair.and hc).exists
    simpa [hz] using hR
  · intro hR
    exact ⟨Measure.Coupling.dirac a b, by simp [hR]⟩

end MeasureProgramLogic
