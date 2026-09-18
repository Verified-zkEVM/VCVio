/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ResumptionMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import ToMathlib.MeasureTheory.DiscreteInstances

/-! A continuing rejection sampler and its finite and limiting output laws. -/

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal BigOperators

public section

namespace ResumptionRejection

/-- A request for one of four equiprobable outcomes. -/
abbrev four : PFunctor.{0, 0} := ⟨Unit, fun _ => Fin 4⟩

noncomputable instance : four.IsMeasureSpec where
  toMeasure _ := uniformOn Set.univ
  isProbabilityMeasure _ := inferInstance

/-- Accept the first three outcomes and reject the fourth. -/
@[expose]
def accept (x : Fin 4) : Option (Fin 3) :=
  if h : x.val < 3 then some ⟨x.val, h⟩ else none

/-- Return an accepted value or request another uniform sample. -/
@[expose]
def step : Option (Fin 3) → Fin 3 ⊕ four.Obj (Option (Fin 3))
  | some x => .inl x
  | none => .inr ⟨(), accept⟩

/-- Repeat the four-outcome request until one of the three accepted values is drawn. -/
@[expose]
def sample : Resumption four (Fin 3) := Resumption.corec step none

theorem corec_some (x : Fin 3) :
    Resumption.corec step (some x) = Resumption.pure x := by
  apply Resumption.eq_of_dest_eq
  simp [step]

theorem sample_unfold : sample = Resumption.query () (fun x =>
    match accept x with
    | some y => Resumption.pure y
    | none => sample) := by
  apply Resumption.eq_of_dest_eq
  rw [sample, Resumption.dest_corec, Resumption.dest_query]
  change (Sum.inr (⟨(), fun x => Resumption.corec step (accept x)⟩ :
    four.Obj (Resumption four (Fin 3))) : Fin 3 ⊕ _) = _
  apply congrArg Sum.inr
  congr 1
  funext x
  cases h : accept x with
  | none => rfl
  | some y => exact corec_some y

theorem truncate_zero : Resumption.truncateMeasure 0 sample = Measure.dirac none := by
  rw [sample_unfold, Resumption.truncateMeasure_query_zero (P := four)]

theorem truncate_succ (k : ℕ) :
    Resumption.truncateMeasure (k + 1) sample =
      Measure.bind (uniformOn (Set.univ : Set (Fin 4))) (fun x =>
        match accept x with
        | some y => Measure.dirac (some y)
        | none => Resumption.truncateMeasure k sample) := by
  conv_lhs => rw [sample_unfold]
  unfold Resumption.truncateMeasure
  rw [Resumption.truncate_query_succ,
    FreeM.denote_liftBind (P := four) _ _ Measurable.of_discrete.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall fun x => by
    cases h : accept x <;> simp [h]

theorem truncate_succ_apply (k : ℕ) (E : Set (Option (Fin 3))) :
    Resumption.truncateMeasure (k + 1) sample E =
      (Measure.dirac (some (0 : Fin 3)) E + Measure.dirac (some (1 : Fin 3)) E +
        Measure.dirac (some (2 : Fin 3)) E + Resumption.truncateMeasure k sample E) *
        (4 : ℝ≥0∞)⁻¹ := by
  rw [truncate_succ, Measure.bind_apply (Set.to_countable E).measurableSet
    Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp [Fin.sum_univ_succ, accept, uniformOn_univ, ← add_mul, add_assoc]

theorem cutoff_mass (k : ℕ) :
    Resumption.truncateMeasure k sample {none} = (4 : ℝ≥0∞)⁻¹ ^ k := by
  induction k with
  | zero => simp [truncate_zero]
  | succ k ih => rw [truncate_succ_apply]; simp [ih, pow_succ]

theorem returned_singleton_succ (k : ℕ) (x : Fin 3) :
    Resumption.outputMeasure (k + 1) sample {x} =
      (1 + Resumption.outputMeasure k sample {x}) * (4 : ℝ≥0∞)⁻¹ := by
  simp only [Resumption.outputMeasure, Measure.dropNone_apply_singleton]
  rw [truncate_succ_apply]
  fin_cases x <;> simp

theorem returned_singleton_finite (k : ℕ) (x : Fin 3) :
    Resumption.outputMeasure k sample {x} =
      ∑ j ∈ Finset.range k, (4 : ℝ≥0∞)⁻¹ ^ (j + 1) := by
  induction k with
  | zero => simp [Resumption.outputMeasure, truncate_zero]
  | succ k ih =>
      rw [returned_singleton_succ, ih, add_mul, one_mul]
      rw [Finset.sum_range_succ']
      simp only [pow_succ, Finset.sum_mul, pow_zero, one_mul]
      exact add_comm _ _

theorem returned_uniform : Resumption.returnedMeasure sample =
    uniformOn (Set.univ : Set (Fin 3)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Resumption.returnedMeasure_apply (P := four) _ _ (measurableSet_singleton _)]
  simp_rw [returned_singleton_finite]
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric_add_one, uniformOn_univ]
  norm_num
  change ((4 : NNReal) : ℝ≥0∞)⁻¹ *
    ((1 : NNReal) - ((4 : NNReal) : ℝ≥0∞)⁻¹)⁻¹ = ((3 : NNReal) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv, ← ENNReal.coe_sub, ← ENNReal.coe_inv,
    ← ENNReal.coe_mul, ← ENNReal.coe_inv]
  · apply congrArg (fun r : NNReal => (r : ℝ≥0∞))
    apply NNReal.eq
    norm_num [NNReal.sub_def]
  all_goals norm_num [NNReal.sub_def]

theorem almost_sure_return : Resumption.returnedMeasure sample Set.univ = 1 := by
  rw [returned_uniform]
  exact measure_univ

end ResumptionRejection
