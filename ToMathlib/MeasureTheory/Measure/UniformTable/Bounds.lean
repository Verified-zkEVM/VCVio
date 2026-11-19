/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable
import Mathlib.Data.Fintype.Prod

/-!
# Uniform table resampling and collision bounds

Resampling any selected subset of two independent uniform tables preserves the uniform
average. Coordinate evaluation is uniform, and a union bound controls hitting a selected
set of coordinates or colliding at two coordinates. Finite-sum forms support direct
weighted-incidence estimates without introducing computation or oracle semantics.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

universe u v

variable {D : Type u} {R : Type v}

/-- Keep selected coordinates of the first table and take the remaining coordinates
from the second. -/
@[expose]
def resample (keep : D → Prop) [DecidablePred keep] (a b : D → R) : D → R :=
  fun i ↦ if keep i then a i else b i

/-- Exchange the unselected coordinates of two tables; this operation is an involution. -/
@[expose]
def resampleEquiv (keep : D → Prop) [DecidablePred keep] :
    ((D → R) × (D → R)) ≃ ((D → R) × (D → R)) where
  toFun p := (resample keep p.1 p.2, resample keep p.2 p.1)
  invFun p := (resample keep p.1 p.2, resample keep p.2 p.1)
  left_inv p := by ext i <;> by_cases h : keep i <;> simp [resample, h]
  right_inv p := by ext i <;> by_cases h : keep i <;> simp [resample, h]

variable [Nonempty R] [MeasurableSpace R] [MeasurableSingletonClass R]

/-- Resampling any subset of a uniform table preserves the uniform average.
The first table can be fixed while the second table supplies independent fresh coordinates. -/
theorem lintegral_resample [Finite D] [Finite R] (keep : D → Prop) [DecidablePred keep]
    (f : (D → R) → ENNReal) :
    (∫⁻ a, ∫⁻ b, f (resample keep a b) ∂(uniformOn Set.univ : Measure (D → R))
      ∂(uniformOn Set.univ : Measure (D → R))) =
    ∫⁻ a, f a ∂(uniformOn Set.univ : Measure (D → R)) := by
  have he := uniformOn_univ_map_equiv (resampleEquiv (R := R) keep)
  have hi := congrArg (fun μ : Measure ((D → R) × (D → R)) ↦ ∫⁻ p, f p.1 ∂μ) he
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete] at hi
  change (∫⁻ p : (D → R) × (D → R), f (resample keep p.1 p.2) ∂(uniformOn Set.univ)) =
    ∫⁻ p : (D → R) × (D → R), f p.1 ∂(uniformOn Set.univ) at hi
  rw [uniformOn_univ_prod, lintegral_prod _ Measurable.of_discrete.aemeasurable,
    lintegral_prod _ Measurable.of_discrete.aemeasurable] at hi
  simpa using hi

/-- A coordinate of a uniform table is uniform in its answer space. -/
theorem uniform_eval_eq [Finite D] [Fintype R] (i : D) (r : R) :
    (uniformOn Set.univ : Measure (D → R)) {a | a i = r} =
      (Fintype.card R : ENNReal)⁻¹ := by
  have he := uniformOn_univ_map_comp_injective (R := R)
    (e := fun _ : Unit ↦ i) (fun a b _ ↦ Subsingleton.elim a b)
  have hi := congrArg (fun μ : Measure (Unit → R) ↦ μ {fun _ ↦ r}) he
  rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _)] at hi
  have hpre : (fun g : D → R ↦ g ∘ (fun _ : Unit ↦ i)) ⁻¹' {fun _ ↦ r} =
      {a | a i = r} := by
    ext a
    constructor
    · intro h
      exact congrFun h ()
    · intro h
      exact funext fun _ ↦ h
  rw [hpre, uniformOn_univ_apply_singleton] at hi
  simpa using hi

/-- Distinct coordinates of a uniform table agree with probability `1 / |R|`. -/
theorem uniform_pair_eq [Finite D] [Fintype R] (i j : D) (hne : i ≠ j) :
    (uniformOn Set.univ : Measure (D → R)) {a | a i = a j} =
      (Fintype.card R : ENNReal)⁻¹ := by
  classical
  rw [← uniformOn_univ_bind_map_update (R := R) i,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  have hinner (r : R) :
      ((uniformOn Set.univ : Measure (D → R)).map (fun g ↦ Function.update g i r))
        {a | a i = a j} = (Fintype.card R : ENNReal)⁻¹ := by
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    have he : (fun g : D → R ↦ Function.update g i r) ⁻¹' {a | a i = a j} =
        {a | a j = r} := by
      ext a
      simp [hne.symm, eq_comm]
    rw [he, uniform_eval_eq]
  simp_rw [hinner]
  simp

/-- A fixed value occurs in a selected set of uniform coordinates with probability at most
the number of selected coordinates divided by the answer-space cardinality. -/
theorem uniform_hit_le [Finite D] [Fintype R] (s : Finset D) (z : R) :
    (uniformOn Set.univ : Measure (D → R)) {a | ∃ i ∈ s, a i = z} ≤
      (s.card : ENNReal) / Fintype.card R := by
  classical
  have he : {a : D → R | ∃ i ∈ s, a i = z} = ⋃ i ∈ s, {a | a i = z} := by
    ext a
    simp
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, (uniformOn Set.univ : Measure (D → R)) {a | a i = z} :=
      measure_biUnion_finset_le s _
    _ = _ := by simp [uniform_eval_eq, div_eq_mul_inv]

/-- The birthday union bound for independent uniform coordinates. -/
theorem uniform_collision_le [Fintype R] (n : ℕ) :
    (uniformOn Set.univ : Measure (Fin n → R)) {a | ¬ Function.Injective a} ≤
      ((n.choose 2 : ℕ) : ENNReal) / Fintype.card R := by
  classical
  let s : Finset (Fin n × Fin n) := Finset.univ.filter fun p ↦ p.1 < p.2
  have he : {a : Fin n → R | ¬ Function.Injective a} =
      ⋃ p ∈ s, {a | a p.1 = a p.2} := by
    ext a
    simp only [Set.mem_ofPred_eq, Function.not_injective_iff, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_univ, true_and, s]
    constructor
    · rintro ⟨i, j, hij, hne⟩
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ⟨(i,j), hlt, hij⟩
      · exact ⟨(j,i), hlt, hij.symm⟩
    · rintro ⟨p, hlt, hij⟩
      exact ⟨p.1, p.2, hij, ne_of_lt hlt⟩
  rw [he]
  calc
    _ ≤ ∑ p ∈ s, (uniformOn Set.univ : Measure (Fin n → R)) {a | a p.1 = a p.2} :=
      measure_biUnion_finset_le s _
    _ = ∑ _p ∈ s, (Fintype.card R : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact uniform_pair_eq p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)
    _ = _ := by simp [s, Fintype.card_product_filter_lt, div_eq_mul_inv]

open scoped Classical in
/-- The real weighted incidence bound for a selected set of uniform coordinates. -/
theorem uniform_hit_sum_le [Fintype D] [Fintype R] [DecidableEq D] (s : Finset D) (z : R) :
    (∑ a : D → R, if ∃ i ∈ s, a i = z then (Fintype.card (D → R) : ℝ)⁻¹ else 0) ≤
      (s.card : ℝ) / Fintype.card R := by
  let : DecidableEq R := Classical.decEq R
  have h := uniform_hit_le s z
  rw [uniformOn_univ_apply_setOf] at h
  have hr := ENNReal.toReal_mono
    (ENNReal.div_ne_top (by finiteness) (by simp [Fintype.card_ne_zero])) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hr
  convert hr using 1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- A finite-sum form of uniform subset resampling, retaining both complete tables. -/
theorem average_resample [Fintype D] [Fintype R] [DecidableEq D]
    (keep : D → Prop) [DecidablePred keep]
    (f : (D → R) → ENNReal) :
    (∑ a, (Fintype.card (D → R) : ENNReal)⁻¹ * f a) =
      ∑ a, (Fintype.card (D → R) : ENNReal)⁻¹ *
        ∑ b, (Fintype.card (D → R) : ENNReal)⁻¹ * f (resample keep a b) := by
  have h := (lintegral_resample keep f).symm
  simp_rw [lintegral_uniformOn_univ, div_eq_mul_inv, Finset.sum_mul] at h
  simpa only [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h

end ProbabilityTheory
