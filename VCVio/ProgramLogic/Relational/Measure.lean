/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.MeasureTheory.Measure.Coupling
public import VCVio.EvalDist.Defs.Measure

/-!
# Measure-native relational program logic

This module establishes the foundational relational semantics directly over couplings of Mathlib
measures. The postcondition holds almost everywhere under the joint measure, which is the
appropriate notion for continuous distributions: it does not mistake a zero-mass singleton for an
impossible output.

`eRelWP` is the quantitative counterpart. It takes a supremum over measure couplings and
integrates the post-expectation with `lintegral`. Neither definition depends on a finite
distribution, countable support, or point probabilities. This first layer intentionally provides
only witness constructors, reflexivity, and monotonicity; sequential bind/gluing rules require a
measurable family of conditional couplings and are deferred to a later relational-logic PR.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

universe u v w

namespace MeasureProgramLogic

variable {α : Type u} {β : Type v}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- A relation holds under some coupling of `μ` and `ν`, almost everywhere. -/
def CouplingPost (μ : Measure α) (ν : Measure β) (R : α → β → Prop) : Prop :=
  ∃ c : Measure.Coupling μ ν, ∀ᵐ z ∂c.1, R z.1 z.2

/-- Measure-native relational weakest precondition for two denoted computations. -/
def RelWP {m₁ : Type u → Type w} {m₂ : Type v → Type w}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (R : α → β → Prop) : Prop :=
  CouplingPost 𝒟[mx] 𝒟[my] R

/-- Quantitative relational WP: best coupled expectation of `g`. -/
noncomputable def eRelWP {m₁ : Type u → Type w} {m₂ : Type v → Type w}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ c : Measure.Coupling 𝒟[mx] 𝒟[my], ∫⁻ z, g z.1 z.2 ∂c.1

/-- Postcondition monotonicity for measure couplings. -/
theorem CouplingPost.mono {μ : Measure α} {ν : Measure β} {R S : α → β → Prop}
    (h : CouplingPost μ ν R) (hRS : ∀ a b, R a b → S a b) :
    CouplingPost μ ν S := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono fun z hz => hRS z.1 z.2 hz⟩

/-- Quantitative post-expectation monotonicity. -/
theorem eRelWP_mono {m₁ : Type u → Type w} {m₂ : Type v → Type w}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) {g h : α → β → ℝ≥0∞}
    (hgh : ∀ a b, g a b ≤ h a b) :
    eRelWP mx my g ≤ eRelWP mx my h := by
  refine iSup_mono fun c => ?_
  exact lintegral_mono fun z => hgh z.1 z.2

/-- Pure computations satisfy every relation true of their returned pair. -/
theorem relWP_pure_pure
    {m₁ : Type u → Type w} {m₂ : Type v → Type w}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulEvalDistSemantics m₁] [LawfulEvalDistSemantics m₂]
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

/-- Every computation is related to itself by equality. -/
theorem relWP_refl {m : Type u → Type w} [EvalDistSemantics m] [MeasurableEq α] (mx : m α) :
    RelWP mx mx (· = ·) :=
  couplingPost_refl 𝒟[mx]

end MeasureProgramLogic
