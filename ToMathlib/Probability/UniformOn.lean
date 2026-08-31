/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Probability.UniformOn

/-!
# Uniform measures on finite spaces

This file supplies measure-level facts for finite uniform sampling. It identifies the mass of a
point under the uniform measure on the whole space, characterizes independent uniform draws as
the uniform measure on a product, and shows that a measurable bijection preserves uniformity.

The measurable-space assumptions stay explicit: the results require measurable singletons but do
not install a discrete measurable-space instance.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Every point in a finite nonempty space has mass `1 / |α|` under its uniform measure. -/
@[simp] theorem uniformOn_univ_apply_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [Nonempty α]
    (a : α) :
    uniformOn (Set.univ : Set α) {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton]
  simp [div_eq_mul_inv]

/-- The uniform measure on a product of finite nonempty spaces is the product of their uniform
measures. Thus the two coordinates are independent uniform draws. -/
theorem uniformOn_univ_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Finite α] [Finite β] [Nonempty α] [Nonempty β] :
    uniformOn (Set.univ : Set (α × β)) =
      (uniformOn (Set.univ : Set α)).prod (uniformOn (Set.univ : Set β)) := by
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  calc
    uniformOn (Set.univ : Set (α × β)) {(a, b)} =
        (Fintype.card (α × β) : ℝ≥0∞)⁻¹ := uniformOn_univ_apply_singleton (a, b)
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card β : ℝ≥0∞)⁻¹ := by
      simp only [Fintype.card_prod, Nat.cast_mul]
      exact ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by finiteness))
    _ = ((uniformOn (Set.univ : Set α)).prod
        (uniformOn (Set.univ : Set β))) {(a, b)} := by
      rw [show ({(a, b)} : Set (α × β)) = {a} ×ˢ {b} by
        ext point
        simp]
      simp only [Measure.prod_prod, uniformOn_univ_apply_singleton]

/-- Pushing the uniform measure on a finite nonempty space through a measurable bijection gives
the uniform measure on its codomain. Only forward measurability is needed. -/
theorem map_uniformOn_univ_of_bijective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Finite α] [Finite β] [Nonempty α] [Nonempty β]
    {f : α → β} (hf : Measurable f) (hbij : Function.Bijective f) :
    Measure.map f (uniformOn (Set.univ : Set α)) = uniformOn (Set.univ : Set β) := by
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply hf (measurableSet_singleton b)]
  obtain ⟨a, rfl⟩ := hbij.surjective b
  rw [show f ⁻¹' ({f a} : Set β) = {a} by
    ext a'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hbij.injective.eq_iff]
  rw [uniformOn_univ_apply_singleton, uniformOn_univ_apply_singleton]
  rw [Fintype.card_congr (Equiv.ofBijective f hbij)]

end ProbabilityTheory
