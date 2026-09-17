/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.ProbabilityTheory.FinRatPMF.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import ToMathlib.Probability.UniformOn

/-!
# Measures of finite rational distributions

An executable rational distribution denotes a finite sum of weighted Dirac measures. Array
order, duplicate outcomes, and zero-weight entries do not affect the measure. Event masses
remain computable rational sums, and measurable bind agrees with Giry composition.
-/

public section

open MeasureTheory ENNReal NNReal

universe u

namespace FinRatPMF.Raw

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- The finite sum of weighted Dirac measures specified by the raw array. -/
@[expose]
noncomputable def toMeasure (p : Raw α) : Measure α :=
  (p.toList.map fun a ↦ ((a.2 : ℝ≥0) : ℝ≥0∞) • Measure.dirac a.1).sum

private lemma sum_smul_dirac_apply (l : List (α × ℚ≥0))
    {s : Set α} (hs : MeasurableSet s) [DecidablePred (· ∈ s)] :
    ((l.map fun a ↦ ((a.2 : ℝ≥0) : ℝ≥0∞) • Measure.dirac a.1).sum : Measure α) s =
      (((l.filter fun a ↦ a.1 ∈ s).map Prod.snd).sum : ℝ≥0) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hs, smul_eq_mul, ih]
    by_cases ha : a.1 ∈ s <;> simp [ha, NNRat.cast_add]

/-- The measure of a decidable event is the rational sum of the weights of its tickets. -/
theorem toMeasure_apply (p : Raw α) {s : Set α} (hs : MeasurableSet s)
    [DecidablePred (· ∈ s)] :
    p.toMeasure s = (((p.toList.filter fun a ↦ a.1 ∈ s).map Prod.snd).sum : ℝ≥0) :=
  sum_smul_dirac_apply p.toList hs

/-- The denotation of a raw distribution has total mass one. -/
theorem toMeasure_apply_univ (p : Raw α) : p.toMeasure Set.univ = 1 := by
  rw [toMeasure_apply p MeasurableSet.univ]
  simp [toList, p.sum_eq_one]

instance (p : Raw α) : IsProbabilityMeasure p.toMeasure := ⟨toMeasure_apply_univ p⟩

/-- Singleton mass is the executable rational probability. -/
@[simp]
theorem toMeasure_apply_singleton [MeasurableSingletonClass α] [DecidableEq α]
    (p : Raw α) (x : α) : p.toMeasure {x} = ((p.prob x : ℝ≥0) : ℝ≥0∞) := by
  rw [toMeasure_apply p (measurableSet_singleton x)]
  rfl

/-- Pure sampling denotes a Dirac measure on any measurable space. -/
@[simp]
theorem toMeasure_pure (a : α) : (pure a : Raw α).toMeasure = Measure.dirac a := by
  simp [toMeasure]

/-- Finite uniform rational sampling denotes the native uniform measure. -/
@[simp]
theorem toMeasure_uniform [MeasurableSingletonClass α] [FinEnum α] [Inhabited α] :
    (Raw.uniform (α := α)).toMeasure = ProbabilityTheory.uniformOn Set.univ := by
  apply Measure.ext_of_singleton
  intro x
  rw [toMeasure_apply_singleton, Raw.prob_eq_prob inferInstance FinEnum.decEq,
    Raw.prob_uniform, ProbabilityTheory.uniformOn_univ_apply_singleton,
    NNRat.cast_inv, ENNReal.coe_inv (by exact_mod_cast Fintype.card_ne_zero)]
  simp

private lemma lintegral_sum_smul_dirac (l : List (α × ℚ≥0))
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, g a ∂(l.map fun a ↦ ((a.2 : ℝ≥0) : ℝ≥0∞) • Measure.dirac a.1).sum =
      (l.map fun a ↦ ((a.2 : ℝ≥0) : ℝ≥0∞) * g a.1).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, lintegral_add_measure,
      lintegral_smul_measure, lintegral_dirac' a.1 hg, smul_eq_mul, ih]

/-- Integrating a measurable function against a raw distribution is a finite weighted sum. -/
theorem lintegral_toMeasure (p : Raw α) {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, g a ∂p.toMeasure =
      (p.toList.map fun a ↦ ((a.2 : ℝ≥0) : ℝ≥0∞) * g a.1).sum :=
  lintegral_sum_smul_dirac p.toList hg

omit [MeasurableSpace α] in
private lemma sum_smul_dirac_bind (l : List (α × ℚ≥0)) (f : α → Raw β) :
    ((l.flatMap fun a ↦ (f a.1).toList.map fun b ↦ (b.1, (a.2 * b.2 : ℚ≥0))).map
      fun b ↦ ((b.2 : ℝ≥0) : ℝ≥0∞) • Measure.dirac b.1).sum =
        (l.map fun a ↦ ((a.2 : ℝ≥0) : ℝ≥0∞) • (f a.1).toMeasure).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_map, Function.comp_def, ih]
    congr 1
    simp only [toMeasure, NNRat.cast_mul, ENNReal.coe_mul, mul_smul]
    rw [List.smul_sum]
    simp [List.map_map, Function.comp_def]

/-- The measure interpretation of bind agrees with Giry bind for measurable continuations. -/
theorem toMeasure_bind (p : Raw α) (f : α → Raw β)
    (hf : Measurable fun a ↦ (f a).toMeasure) :
    (p >>= f).toMeasure = p.toMeasure.bind fun a ↦ (f a).toMeasure := by
  ext s hs
  have hg : Measurable fun a ↦ (f a).toMeasure s := (Measure.measurable_coe hs).comp hf
  rw [Measure.bind_apply hs hf.aemeasurable, lintegral_toMeasure p hg]
  rw [toMeasure, bind_toList, sum_smul_dirac_bind]
  induction p.toList with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul, ih]

end FinRatPMF.Raw
