/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Measures concentrated on a finite set

A measure whose complement of a finite set `F` is null gives each event the mass of its points
in `F`, and two such measures agree once they agree on the points of `F`. Unlike
`MeasureTheory.Measure.ext_of_singleton`, the space itself need not be countable.
-/

public section

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A measure concentrated on a finite set gives each event the mass of its points in that set. -/
theorem apply_eq_sum_indicator_of_compl_eq_zero {μ : Measure α} {F : Finset α}
    (hF : μ (↑F)ᶜ = 0) (s : Set α) : μ s = ∑ a ∈ F, s.indicator (fun a => μ {a}) a := by
  classical
  have hset : s ∩ ↑F = ↑(F.filter (· ∈ s)) := by
    ext x
    simp [and_comm]
  rw [← measure_inter_conull hF, hset, ← sum_measure_singleton, Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by simp [Set.indicator_apply]

/-- Measures concentrated on a common finite set agree when they agree on its points. -/
theorem ext_of_compl_eq_zero {μ ν : Measure α} {F : Finset α} (hμ : μ (↑F)ᶜ = 0)
    (hν : ν (↑F)ᶜ = 0) (h : ∀ a ∈ F, μ {a} = ν {a}) : μ = ν :=
  ext fun s _ => by
    rw [apply_eq_sum_indicator_of_compl_eq_zero hμ, apply_eq_sum_indicator_of_compl_eq_zero hν]
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases has : a ∈ s <;> simp [has, h a ha]

end MeasureTheory.Measure
