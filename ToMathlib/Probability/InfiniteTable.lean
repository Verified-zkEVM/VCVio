/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Probability.Independence.InfinitePi
public import ToMathlib.Probability.UniformOn
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Laws of infinite random tables

An infinite table has the product σ-algebra and the product of its coordinate laws.
Every finite restriction is an ordinary finite product. Even a Boolean table on natural-number
keys has no atoms: no countable collection of complete tables can carry its probability law.
This concerns the ideal persistent state, while each finite interaction reveals only finitely
many coordinates.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {D A : Type*} [MeasurableSpace A]

/-- Independent uniform values at every key, observed through the product σ-algebra.
Finite nonempty answer types give a probability law. -/
noncomputable def uniformTable : Measure (D → A) :=
  infinitePi fun _ => uniformOn (Set.univ : Set A)

instance [Finite A] [Nonempty A] : IsProbabilityMeasure (uniformTable (D := D) (A := A)) := by
  unfold uniformTable
  infer_instance

/-- The ideal table restricted to any finite key set has the finite product law. -/
theorem uniformTable_map_restrict [Finite A] [Nonempty A] (keys : Finset D) :
    (uniformTable (A := A)).map keys.restrict =
      Measure.pi (fun _ : keys => uniformOn (Set.univ : Set A)) :=
  infinitePi_map_restrict _

/-- Every coordinate of a uniform table has the uniform answer law. -/
theorem uniformTable_map_eval [Finite A] [Nonempty A] (key : D) :
    (uniformTable (A := A)).map (fun table => table key) = uniformOn Set.univ :=
  infinitePi_map_eval _ key

/-- Coordinates from disjoint sets of keys are independent, including infinite sets. -/
theorem uniformTable_indepFun_restrict [Finite A] [Nonempty A]
    (left right : Set D) (h : Disjoint left right) :
    IndepFun left.domRestrict right.domRestrict (uniformTable (A := A)) := by
  exact (iIndepFun_infinitePi (P := fun _ : D => uniformOn (Set.univ : Set A))
    (X := fun _ x => x) (fun _ => measurable_id)).indepFun_set left right h
      (fun d => measurable_pi_apply d)

/-- A fixed infinite fair-bit table has zero probability. -/
theorem uniformTable_bool_singleton (table : ℕ → Bool) :
    uniformTable {table} = 0 := by
  apply le_antisymm _ bot_le
  apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (2 : ℝ≥0∞)⁻¹ < 1 by norm_num))
  apply Filter.Eventually.of_forall
  intro n
  calc
    uniformTable {table} ≤ uniformTable (Set.pi (Finset.range n) (fun i => {table i})) :=
      measure_mono (by intro f hf; rcases hf with rfl; simp)
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [uniformTable, infinitePi_pi _ (by intro i hi; exact measurableSet_singleton _)]
      simp only [uniformOn_univ_apply_singleton, Fintype.card_bool,
        Nat.cast_ofNat, Finset.prod_const, Finset.card_range]

/-- No countable family of complete fair-bit tables supports the ideal table law. -/
theorem uniformTable_bool_countable (tables : Set (ℕ → Bool)) (htables : tables.Countable) :
    uniformTable tables = 0 := by
  let : NullSingletonClass (uniformTable (D := ℕ) (A := Bool)) :=
    ⟨uniformTable_bool_singleton⟩
  exact htables.measure_zero _

end MeasureTheory.Measure
