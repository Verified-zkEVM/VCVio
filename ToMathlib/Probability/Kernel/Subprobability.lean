/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.MeasureTheory.Measure.Subprobability
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Subprobability kernels

`IsSubprobabilityKernel κ` states that every measure produced by `κ` has total mass at most one.
It is the kernel-level mass discipline for a parameterized computation that may fail or diverge.

Mathlib's `IsZeroOrMarkovKernel` is different: it allows only kernels that are identically zero or
have mass exactly one at every input. A subprobability kernel may lose a different, nontrivial
amount of mass at each input.

The class is closed under the standard kernel operations used by probabilistic semantics. In
particular, a subprobability kernel is finite and hence s-finite, so Mathlib's composition and
product APIs apply without additional finiteness assumptions.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A kernel whose value at every input is a subprobability measure. -/
class IsSubprobabilityKernel (κ : Kernel α β) : Prop where
  /-- Every kernel value has total mass at most one. -/
  measure_univ_le' : ∀ a, κ a Set.univ ≤ 1

namespace Kernel

variable (κ : Kernel α β) [IsSubprobabilityKernel κ]

/-- Every value of a subprobability kernel has total mass at most one. -/
theorem measure_univ_le (a : α) : κ a Set.univ ≤ 1 :=
  IsSubprobabilityKernel.measure_univ_le' a

/-- Every measurable event has mass at most one under a subprobability kernel. -/
theorem measure_le_one (a : α) (s : Set β) : κ a s ≤ 1 :=
  (measure_mono (Set.subset_univ s)).trans (κ.measure_univ_le a)

/-- Applying a subprobability kernel produces a subprobability measure. -/
instance apply.instIsSubprobabilityMeasure (a : α) : IsSubprobabilityMeasure (κ a) :=
  ⟨κ.measure_univ_le a⟩

/-- A subprobability kernel is uniformly finite, with bound one. -/
instance (priority := 100) IsSubprobabilityKernel.toIsFiniteKernel : IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, κ.measure_univ_le⟩⟩

end Kernel

/-- Every Markov kernel is a subprobability kernel. -/
instance (priority := 100) IsMarkovKernel.toIsSubprobabilityKernel (κ : Kernel α β)
    [IsMarkovKernel κ] : IsSubprobabilityKernel κ :=
  ⟨fun _ => le_of_eq measure_univ⟩

instance : IsSubprobabilityKernel (0 : Kernel α β) := ⟨by simp⟩

instance Kernel.const.instIsSubprobabilityKernel (μ : Measure β) [IsSubprobabilityMeasure μ] :
    IsSubprobabilityKernel (Kernel.const α μ) :=
  ⟨fun _ => by simpa using MeasureTheory.measure_univ_le μ⟩

instance Kernel.restrict.instIsSubprobabilityKernel (κ : Kernel α β)
    [IsSubprobabilityKernel κ] {s : Set β} (hs : MeasurableSet s) :
    IsSubprobabilityKernel (κ.restrict hs) := ⟨fun a => by
  rw [Kernel.restrict_apply' κ hs a MeasurableSet.univ]
  exact (measure_mono (Set.subset_univ _)).trans (κ.measure_univ_le a)⟩

instance Kernel.map.instIsSubprobabilityKernel (κ : Kernel α β)
    [IsSubprobabilityKernel κ] (f : β → γ) :
    IsSubprobabilityKernel (κ.map f) := ⟨fun a => by
  by_cases hf : Measurable f
  · rw [Kernel.map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ]
    exact κ.measure_univ_le a
  · simp [Kernel.map_of_not_measurable κ hf]⟩

instance Kernel.comap.instIsSubprobabilityKernel (κ : Kernel α β)
    [IsSubprobabilityKernel κ] {f : γ → α} (hf : Measurable f) :
    IsSubprobabilityKernel (κ.comap f hf) :=
  ⟨fun a => by simpa using κ.measure_univ_le (f a)⟩

instance Kernel.comp.instIsSubprobabilityKernel (η : Kernel β γ)
    [IsSubprobabilityKernel η] (κ : Kernel α β) [IsSubprobabilityKernel κ] :
    IsSubprobabilityKernel (η ∘ₖ κ) := ⟨fun a => by
  rw [Kernel.comp_apply]
  let _ : IsSubprobabilityMeasure ((κ a).bind η) :=
    isSubprobabilityMeasure_bind η.aemeasurable
  exact MeasureTheory.measure_univ_le ((κ a).bind η)⟩

instance Kernel.prod.instIsSubprobabilityKernel (κ : Kernel α β)
    [IsSubprobabilityKernel κ] (η : Kernel α γ) [IsSubprobabilityKernel η] :
    IsSubprobabilityKernel (κ ×ₖ η) := ⟨fun a => by
  rw [← Set.univ_prod_univ, Kernel.prod_apply_prod]
  calc
    κ a Set.univ * η a Set.univ ≤ 1 * 1 :=
      mul_le_mul' (κ.measure_univ_le a) (η.measure_univ_le a)
    _ = 1 := one_mul 1⟩

instance Kernel.pow.instIsSubprobabilityKernel (κ : Kernel α α)
    [IsSubprobabilityKernel κ] (n : ℕ) : IsSubprobabilityKernel (κ ^ n) := by
  induction n with
  | zero =>
      change IsSubprobabilityKernel (Kernel.id : Kernel α α)
      infer_instance
  | succ n ih =>
      let _ : IsSubprobabilityKernel (κ ^ n) := ih
      rw [Kernel.pow_add κ n 1, pow_one]
      infer_instance

end ProbabilityTheory
