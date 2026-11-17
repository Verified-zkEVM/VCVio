/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp.Basic
public import ToMathlib.Data.List.Count

/-!
# Expectations of independently sampled lists

Additive observations and predicate counts of a sampled list have expectations equal to the
sums of the corresponding expectations of its entries.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace OracleComp

/-- The expectation of an additive observation of an independently sampled finite table is
the sum of the expectations of its entries. -/
theorem lintegral_mapM_sum {C X : Type} [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (child : C → ProbComp X) (v : X → ℝ≥0∞) (pool : List C) :
    (letI : MeasurableSpace (List X) := ⊤
      ∫⁻ table, (table.map v).sum ∂𝒟[pool.mapM child]) =
        (pool.map fun c => ∫⁻ x, v x ∂𝒟[child c]).sum := by
  let : MeasurableSpace (List X) := ⊤
  induction pool with
  | nil => simp
  | cons c cs ih =>
      rw [List.mapM_cons, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
      simp_rw [lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
      simp only [evalDist_pure, lintegral_dirac' _ Measurable.of_discrete,
        List.map_cons, List.sum_cons]
      simp_rw [lintegral_add_left Measurable.of_discrete, lintegral_const,
        measure_univ, mul_one]
      rw [ih]

/-- The expected number of accepting entries in an independently sampled finite table is
the sum of the individual acceptance probabilities. -/
theorem lintegral_mapM_countP {C X : Type} [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (child : C → ProbComp X) (accept : X → Bool) (pool : List C) :
    (letI : MeasurableSpace (List X) := ⊤
      ∫⁻ table, (table.countP accept : ℝ≥0∞) ∂𝒟[pool.mapM child]) =
        (pool.map fun c => Pr{let x ← child c}[accept x = true]).sum := by
  let : MeasurableSpace (List X) := ⊤
  have hcount : ∀ table : List X, (table.countP accept : ℝ≥0∞) =
      (table.map fun x => if accept x then (1 : ℝ≥0∞) else 0).sum := by
    intro table
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
      congrArg (fun n : ℕ => (n : ℝ≥0∞)) (List.countP_eq_sum_map table accept)
  simp_rw [hcount]
  rw [lintegral_mapM_sum]
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [prEvent_eq_evalDist_of_discrete,
    ← lintegral_indicator_one (s := {x | accept x = true}) MeasurableSet.of_discrete]
  apply lintegral_congr
  intro x
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]

end OracleComp
