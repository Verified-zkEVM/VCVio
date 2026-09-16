/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.MeasureTheory.MeasurableSpace.Option
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Discarding the `none` part of an option-valued measure

`Measure.dropNone` turns a measure on `Option α` into the submeasure of successful values on
`α`. It is the effect-preserving boundary needed by `OptionT` and by finite observations of a
possibly nonterminating computation: the `none` mass is discarded instead of being confused with
an ordinary result.

The definition uses the Giry bind. The coproduct measurable structure makes the success/failure
case split measurable without requiring `α` itself to be discrete.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- Keep the mass at `some x` as mass at `x`, and discard the mass at `none`. -/
noncomputable def dropNone (μ : Measure (Option α)) : Measure α :=
  Measure.bind μ fun
    | none => 0
    | some x => Measure.dirac x

/-- The measure family used by `dropNone` is measurable for every measurable result space. -/
theorem measurable_dropNoneKernel : Measurable fun value : Option α =>
    match value with
    | none => 0
    | some x => Measure.dirac x :=
  Option.measurable_elim measurable_const Measure.measurable_dirac

/-- The optional measure kernel is measurable in its eliminator form. -/
@[fun_prop]
theorem measurable_dropNoneKernel_elim : Measurable fun value : Option α =>
    value.elim (0 : Measure α) Measure.dirac := by fun_prop

/-- Discarding the `none` branch varies measurably with the input measure. -/
@[fun_prop]
theorem measurable_dropNone :
    Measurable (dropNone : Measure (Option α) → Measure α) :=
  Measure.measurable_bind' measurable_dropNoneKernel

@[simp]
theorem dropNone_zero : dropNone (0 : Measure (Option α)) = 0 := by
  simp [dropNone, Measure.bind_zero_left]

@[simp]
theorem dropNone_dirac_none :
    dropNone (Measure.dirac (none : Option α)) = 0 := by
  rw [dropNone, Measure.dirac_bind measurable_dropNoneKernel]

@[simp]
theorem dropNone_dirac_some (x : α) :
    dropNone (Measure.dirac (some x)) = Measure.dirac x := by
  rw [dropNone, Measure.dirac_bind measurable_dropNoneKernel]

/-- The mass retained by `dropNone` on a measurable set is the mass of its image under `some`. -/
theorem dropNone_apply (μ : Measure (Option α)) {s : Set α} (hs : MeasurableSet s) :
    dropNone μ s = μ (some '' s) := by
  rw [dropNone, Measure.bind_apply hs measurable_dropNoneKernel.aemeasurable]
  refine (lintegral_congr fun value => ?_).trans
    (lintegral_indicator_one (Option.measurableSet_some_image.mpr hs))
  cases value with
  | none => simp [Set.indicator]
  | some x =>
      rw [Measure.dirac_apply' x hs]
      by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

/-- Discarding `none` is Mathlib's measure pullback along the measurable embedding `some`. -/
theorem dropNone_eq_comap_some (μ : Measure (Option α)) :
    dropNone μ = μ.comap some := by
  ext s hs
  rw [dropNone_apply μ hs, Option.measurableEmbedding_some.comap_apply]

/-- Discarding failure after an optional bind is the bind of the successful input mass with the
discarded successful mass of each continuation. -/
theorem dropNone_bind {β : Type*} [MeasurableSpace β]
    (μ : Measure (Option α)) (f : α → Measure (Option β)) (hf : Measurable f) :
    dropNone (μ.bind fun value => value.elim (Measure.dirac none) f) =
      (dropNone μ).bind fun x => dropNone (f x) := by
  have hOption : Measurable fun value : Option α =>
      value.elim (Measure.dirac none) f :=
    Option.measurable_elim' _ hf
  have hDropF : Measurable fun x => dropNone (f x) :=
    measurable_dropNone.comp hf
  simp only [dropNone] at hDropF ⊢
  rw [Measure.bind_bind hOption.aemeasurable measurable_dropNoneKernel.aemeasurable,
    Measure.bind_bind measurable_dropNoneKernel.aemeasurable hDropF.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards with value
  cases value with
  | none =>
      simp only [Option.elim_none]
      rw [Measure.dirac_bind measurable_dropNoneKernel, Measure.bind_zero_left]
  | some x =>
      simp only [Option.elim_some]
      rw [Measure.dirac_bind hDropF]

/-- The success mass at `x` is the original mass at `some x`.

This is the computation rule that carries a pointwise mass statement across `dropNone`. -/
theorem dropNone_apply_singleton [MeasurableSingletonClass α]
    (μ : Measure (Option α)) (x : α) :
    dropNone μ {x} = μ {some x} := by
  rw [dropNone, Measure.bind_apply (measurableSet_singleton x)
    measurable_dropNoneKernel.aemeasurable]
  refine Eq.trans (lintegral_congr (g := Set.indicator {some x} 1) ?_) ?_
  · rintro (_ | y)
    · simp
    · by_cases hy : y = x <;> simp [hy]
  · exact lintegral_indicator_one (measurableSet_singleton (some x))

/-- Discarding `none` cannot increase the total mass. -/
theorem dropNone_apply_univ_le (μ : Measure (Option α)) :
    dropNone μ Set.univ ≤ μ Set.univ := by
  rw [dropNone, Measure.bind_apply MeasurableSet.univ measurable_dropNoneKernel.aemeasurable,
    ← lintegral_one]
  apply lintegral_mono
  intro value
  cases value <;> simp

/-- Discarding the absent outcomes of a subprobability measure preserves its mass bound. -/
instance dropNone.instIsSubprobabilityMeasure (μ : Measure (Option α))
    [IsSubprobabilityMeasure μ] : IsSubprobabilityMeasure μ.dropNone :=
  ⟨(dropNone_apply_univ_le μ).trans (measure_univ_le μ)⟩

/-- Integrating against `dropNone μ` integrates against `μ` with the `none` outcome discarded. -/
theorem lintegral_dropNone (μ : Measure (Option α)) {g : α → ENNReal} (hg : Measurable g) :
    ∫⁻ x, g x ∂dropNone μ = ∫⁻ o, o.elim 0 g ∂μ := by
  rw [dropNone, Measure.lintegral_bind measurable_dropNoneKernel.aemeasurable hg.aemeasurable]
  refine lintegral_congr fun o => ?_
  cases o with
  | none => simp
  | some x => simp [lintegral_dirac' x hg]

/-- The total mass left after discarding `none` is the mass of the present outcomes. -/
theorem dropNone_apply_univ (μ : Measure (Option α)) :
    dropNone μ Set.univ = μ {value | value.isSome} := by
  rw [← lintegral_one, lintegral_dropNone μ measurable_const,
    ← lintegral_indicator_one Option.measurableSet_isSome]
  apply lintegral_congr
  intro value
  cases value <;> simp [Set.indicator]

/-! ## Completing a subprobability measure with an explicit failure outcome -/

/-- Turn a subprobability measure into a measure on `Option α` by mapping successful outcomes
through `some` and assigning all missing mass to `none`.

The definition is meaningful for every measure. Its probability-measure law requires the
subprobability bound `μ univ ≤ 1`, supplied explicitly or inferred from
`IsSubprobabilityMeasure μ`. -/
noncomputable def withFailure (μ : Measure α) : Measure (Option α) :=
  Measure.map some μ + (1 - μ Set.univ) • Measure.dirac none

/-- Completing a subprobability measure assigns total mass one. -/
@[simp]
theorem withFailure_apply_univ (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    withFailure μ Set.univ = 1 := by
  rw [withFailure, Measure.add_apply, Measure.map_apply Option.measurable_some MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply' none MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.indicator_of_mem (Set.mem_univ none), Pi.one_apply,
    smul_eq_mul, mul_one]
  simpa [add_comm] using tsub_add_cancel_of_le hμ

/-- The failure completion of a subprobability measure is a probability measure. -/
theorem withFailure_isProbabilityMeasure (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    IsProbabilityMeasure (withFailure μ) := by
  rw [isProbabilityMeasure_iff]
  exact withFailure_apply_univ μ hμ

/-- Completing a subprobability measure with its missing mass is a probability measure. -/
instance withFailure.instIsProbabilityMeasure (μ : Measure α) [IsSubprobabilityMeasure μ] :
    IsProbabilityMeasure μ.withFailure :=
  withFailure_isProbabilityMeasure μ (measure_univ_le μ)

/-- The mass of the explicit failure outcome is exactly the missing mass. -/
theorem withFailure_apply_none (μ : Measure α) :
    withFailure μ {none} = 1 - μ Set.univ := by
  rw [withFailure, Measure.add_apply,
    Measure.map_apply Option.measurable_some Option.measurableSet_none,
    Measure.smul_apply, Measure.dirac_apply' none Option.measurableSet_none]
  rw [show some ⁻¹' ({none} : Set (Option α)) = ∅ by ext y; simp]
  rw [Set.indicator_of_mem (Set.mem_singleton none)]
  simp only [measure_empty, Pi.one_apply, smul_eq_mul, zero_add, mul_one]

/-- Failure completion preserves the mass of every successful singleton. -/
theorem withFailure_apply_some [MeasurableSingletonClass α] (μ : Measure α) (x : α) :
    withFailure μ {some x} = μ {x} := by
  rw [withFailure, Measure.add_apply,
    Measure.map_apply Option.measurable_some (measurableSet_singleton (some x)),
    Measure.smul_apply, Measure.dirac_apply' none (measurableSet_singleton (some x))]
  rw [show some ⁻¹' ({some x} : Set (Option α)) = {x} by ext y; simp]
  rw [Set.indicator_of_notMem (by simp)]
  simp only [smul_zero, add_zero]

/-- Finite selector fibers of optional outputs have total mass at most the mass of present
outputs. Only the fibers need be measurable; the selector's target needs no measurable space. -/
lemma sum_apply_option_map_eq_some_le_isSome {γ : Type*} [Fintype γ]
    (μ : Measure (Option α)) (select : α → Option γ)
    (hselect : ∀ k, MeasurableSet {r : Option α | r.map select = some (some k)}) :
    ∑ k : γ, μ {r | r.map select = some (some k)} ≤ μ {r | r.isSome} := by
  classical
  have hdisjoint : Pairwise fun i j : γ ↦ Disjoint
      {r : Option α | r.map select = some (some i)}
      {r : Option α | r.map select = some (some j)} := by
    intro i j hij
    refine Set.disjoint_left.mpr fun r hi hj ↦ hij ?_
    simpa only [Option.some.injEq] using hi.symm.trans hj
  rw [← tsum_fintype (L := .unconditional _), ← measure_iUnion hdisjoint hselect]
  apply measure_mono
  intro r hr
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hr
  cases r <;> simp_all

end MeasureTheory.Measure
