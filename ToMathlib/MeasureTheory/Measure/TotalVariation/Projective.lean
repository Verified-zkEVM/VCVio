/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Total variation from finite observations

A uniform discrepancy bound on a generating algebra extends to every measurable event.
Consequently a uniform total variation bound on all finite marginals bounds the full
infinite-product law, including events that are not decided by a fixed finite prefix.
The proof approximates events using cylinders under the finite measure `μ + ν`.
-/

public section

open MeasureTheory Finset
open scoped ENNReal symmDiff

namespace MeasureTheory.Measure

variable {X : Type*} [mX : MeasurableSpace X]

/-- Changing an event changes its mass by at most the mass of the symmetric difference. -/
theorem absDiff_apply_le_symmDiff (μ : Measure X) (s t : Set X) :
    ENNReal.absDiff (μ s) (μ t) ≤ μ (s ∆ t) := by
  rw [ENNReal.absDiff_eq_edist, ENNReal.edist_le_iff_le_add_right]
  constructor
  · simpa [add_comm] using (tsub_le_iff_right.mp
      (le_measure_symmDiff (μ := μ) (s₁ := s) (s₂ := t)))
  · simpa [add_comm, symmDiff_comm] using (tsub_le_iff_right.mp
      (le_measure_symmDiff (μ := μ) (s₁ := t) (s₂ := s)))

/-- A uniform event discrepancy bound on a generating algebra extends to its σ-algebra. -/
theorem etvDist_le_of_generateFrom (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : Set (Set X)} (hC : IsSetRing C) (huniv : Set.univ ∈ C)
    (hgen : mX = MeasurableSpace.generateFrom C) (ε : ℝ≥0∞)
    (hbound : ∀ s ∈ C, ENNReal.absDiff (μ s) (ν s) ≤ ε) : μ.etvDist ν ≤ ε := by
  apply iSup_le
  intro s
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  obtain ⟨t, ht, hclose⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ + ν) hC
    ⟨{Set.univ}, Set.countable_singleton _, Set.singleton_subset_iff.mpr huniv, by simp⟩
    hgen s.2 (ENNReal.coe_pos.mpr hδ)
  calc
    ENNReal.absDiff (μ s) (ν s) ≤
        ENNReal.absDiff (μ s) (μ t) +
          (ENNReal.absDiff (μ t) (ν t) + ENNReal.absDiff (ν t) (ν s)) :=
      (ENNReal.absDiff_triangle _ _ _).trans
        (add_le_add le_rfl (ENNReal.absDiff_triangle _ _ _))
    _ ≤ μ (s ∆ t) + (ε + ν (t ∆ s)) :=
      add_le_add (absDiff_apply_le_symmDiff μ _ _)
        (add_le_add (hbound t ht) (absDiff_apply_le_symmDiff ν _ _))
    _ = ε + (μ + ν) (t ∆ s) := by
      rw [Measure.add_apply, symmDiff_comm (s : Set X) t]
      ac_rfl
    _ ≤ ε + δ := add_le_add le_rfl hclose.le

/-- Uniform bounds on all finite marginals control the law on the full product σ-algebra. -/
theorem etvDist_le_of_finite_marginals {ι : Type*} {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] (μ ν : Measure (Π i, A i))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ε : ℝ≥0∞)
    (h : ∀ keys : Finset ι, (μ.map keys.restrict).etvDist (ν.map keys.restrict) ≤ ε) :
    μ.etvDist ν ≤ ε := by
  apply etvDist_le_of_generateFrom μ ν
    ⟨empty_mem_measurableCylinders A, fun _ _ => union_mem_measurableCylinders,
      fun _ _ => sdiff_mem_measurableCylinders⟩
    (univ_mem_measurableCylinders A) generateFrom_measurableCylinders.symm ε
  intro s hs
  obtain ⟨keys, event, hevent, rfl⟩ := (mem_measurableCylinders s).mp hs
  rw [cylinder, ← Measure.map_apply (measurable_restrict _) hevent,
    ← Measure.map_apply (measurable_restrict _) hevent]
  exact (absDiff_apply_le_etvDist _ _ hevent).trans (h keys)

end MeasureTheory.Measure
