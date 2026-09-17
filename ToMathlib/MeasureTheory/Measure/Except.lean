/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.MeasureTheory.MeasurableSpace.Except
public import ToMathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Pulling an exception-valued measure back to successful results

Mathlib's `Measure.comap` along the measurable embedding `Except.ok` retains exactly the
successful branch of an exception-valued measure. This file supplies its Giry-bind normal form
and composition laws, without introducing a second transformer-specific measure operation.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {ε α : Type*} [MeasurableSpace ε] [MeasurableSpace α]

/-- The measurable kernel that keeps successful exception values and discards errors. -/
theorem measurable_comap_ok_kernel : Measurable fun value : Except ε α =>
    match value with
    | .error _ => 0
    | .ok x => Measure.dirac x :=
  Except.measurable_elim measurable_const Measure.measurable_dirac

/-- Pullback along `Except.ok` is Giry bind with errors sent to the zero measure. -/
theorem comap_ok_eq_bind (μ : Measure (Except ε α)) :
    μ.comap Except.ok = μ.bind fun value =>
      match value with
      | .error _ => 0
      | .ok x => Measure.dirac x := by
  ext s hs
  rw [Except.measurableEmbedding_ok.comap_apply,
    Measure.bind_apply hs measurable_comap_ok_kernel.aemeasurable,
    ← lintegral_indicator_one (Except.measurableSet_ok_image.mpr hs)]
  apply lintegral_congr
  intro value
  cases value with
  | error error => simp [Set.indicator]
  | ok x =>
      rw [Measure.dirac_apply' x hs]
      by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

/-- Pullback along `Except.ok` varies measurably with the exception-valued measure. -/
@[fun_prop]
theorem measurable_comap_ok :
    Measurable (fun μ : Measure (Except ε α) => μ.comap Except.ok) := by
  have hfun : (fun μ : Measure (Except ε α) => μ.comap Except.ok) =
      fun μ => μ.bind fun value =>
        match value with
        | .error _ => 0
        | .ok x => Measure.dirac x := by
    funext μ
    exact comap_ok_eq_bind μ
  rw [hfun]
  exact Measure.measurable_bind' measurable_comap_ok_kernel

@[simp]
theorem comap_ok_dirac_error (error : ε) :
    (Measure.dirac (Except.error error : Except ε α)).comap Except.ok = 0 := by
  rw [comap_ok_eq_bind, Measure.dirac_bind measurable_comap_ok_kernel]

@[simp]
theorem comap_ok_dirac_ok (x : α) :
    (Measure.dirac (Except.ok x : Except ε α)).comap Except.ok = Measure.dirac x := by
  rw [comap_ok_eq_bind, Measure.dirac_bind measurable_comap_ok_kernel]

/-- Mapping successful exception values commutes with pulling back along `Except.ok`. -/
theorem comap_ok_map {β : Type*} [MeasurableSpace β]
    (μ : Measure (Except ε α)) (f : α → β) (hf : Measurable f) :
    (μ.map (Except.map f)).comap Except.ok = (μ.comap Except.ok).map f := by
  ext s hs
  rw [Except.measurableEmbedding_ok.comap_apply,
    Measure.map_apply (Except.measurable_map hf) (Except.measurableSet_ok_image.mpr hs),
    Measure.map_apply hf hs, Except.measurableEmbedding_ok.comap_apply]
  congr 1
  ext value
  cases value <;> simp [Except.map]

/-- Pulling back after exception bind is the bind of the successful input mass with the
successful mass of each continuation. -/
theorem comap_ok_bind {β : Type*} [MeasurableSpace β]
    (μ : Measure (Except ε α)) (f : α → Measure (Except ε β)) (hf : Measurable f) :
    (μ.bind fun value => match value with
      | .error error => Measure.dirac (Except.error error)
      | .ok x => f x).comap Except.ok =
      (μ.comap Except.ok).bind fun x => (f x).comap Except.ok := by
  have hExcept : Measurable fun value : Except ε α =>
      match value with
      | .error error => Measure.dirac (Except.error error)
      | .ok x => f x :=
    Except.measurable_elim
      (Measure.measurable_dirac.comp Except.measurable_error) hf
  have hComapF : Measurable fun x => (f x).comap Except.ok :=
    measurable_comap_ok.comp hf
  rw [comap_ok_eq_bind]
  simp only [comap_ok_eq_bind] at hComapF ⊢
  rw [Measure.bind_bind hExcept.aemeasurable measurable_comap_ok_kernel.aemeasurable,
    Measure.bind_bind measurable_comap_ok_kernel.aemeasurable hComapF.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards with value
  cases value with
  | error error =>
      simp only
      rw [Measure.dirac_bind measurable_comap_ok_kernel, Measure.bind_zero_left]
  | ok x =>
      simp only
      rw [Measure.dirac_bind hComapF]

end MeasureTheory.Measure
