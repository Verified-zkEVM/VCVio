/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Categorical
public import VCVio.OracleComp.Coinductive.UniformThreshold.Approximation
public import VCVio.EvalDist.Defs.Measure.FinRatPMF

/-!
# Measure correctness of the rational categorical sampler

The cumulative rational thresholds partition an ideal uniform real into cells
whose lengths are the input ticket weights. Reconstruction transfers this law
to the persistent fair-bit service and the exact compiled machine. No distinctness
or positivity condition is imposed on individual tickets. A uniform bit cap
also gives a whole-client error bound through the shared approximation theorem.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal NNReal

namespace UniformThreshold.Categorical

section GeneralResults

universe u
variable {α : Type u} [MeasurableSpace α]

/-- The corresponding piecewise-constant observation of the ideal real. -/
@[expose] noncomputable def partition (fallback : α) : ℚ → List (α × ℚ≥0) → ℝ → α
  | _, [], _ => fallback
  | _, [(value, _)], _ => value
  | lower, (value, weight) :: ticket :: rest, u => by
      classical
      exact if u < ((lower + weight : ℚ) : ℝ) then value
        else partition fallback (lower + weight) (ticket :: rest) u

theorem measurable_partition (fallback : α) (lower : ℚ) (tickets : List (α × ℚ≥0)) :
    Measurable (partition fallback lower tickets) := by
  induction tickets generalizing lower with
  | nil => exact measurable_const
  | cons ticket rest ih =>
      cases rest with
      | nil => exact measurable_const
      | cons _ _ =>
          exact measurable_const.ite (measurableSet_lt measurable_id measurable_const) (ih _)

/-- Ideal execution of the client observes the partition and keeps the same real state. -/
theorem ideal_scan (fallback : α) (lower : ℚ) (tickets : List (α × ℚ≥0)) (u : ℝ) :
    FreeM.runKernel idealAnswer (scan fallback lower tickets) u =
      Measure.dirac (partition fallback lower tickets u, u) := by
  induction tickets generalizing lower with
  | nil => exact FreeM.runKernel_pure _ _ _
  | cons ticket rest ih =>
      cases rest with
      | nil => exact FreeM.runKernel_pure _ _ _
      | cons next rest =>
          rcases ticket with ⟨value, weight⟩
          rw [scan, runKernel_ideal_liftBind]
          by_cases h : u < ((lower + weight : ℚ) : ℝ)
          · simp only [readReal_eq, partition, h, ↓reduceIte]
            exact FreeM.runKernel_pure _ _ _
          · simp only [readReal_eq, partition, h, ↓reduceIte, Bool.false_eq_true]
            exact ih _

/-- Splitting a real interval at a threshold splits the pushforward into the two branches. -/
private theorem map_restrict_Ico_ite {l c r : ℝ} (hl : l ≤ c) (hr : c ≤ r)
    {f g : ℝ → α} (hf : Measurable f) (hg : Measurable g) :
    (volume.restrict (Set.Ico l r)).map (fun u => if u < c then f u else g u) =
      (volume.restrict (Set.Ico l c)).map f + (volume.restrict (Set.Ico c r)).map g := by
  have hm : Measurable (fun u : ℝ => if u < c then f u else g u) :=
    hf.ite (measurableSet_lt measurable_id measurable_const) hg
  rw [← Set.Ico_union_Ico_eq_Ico hl hr, Measure.restrict_union Set.Ico_disjoint_Ico_same
    measurableSet_Ico, Measure.map_add _ _ hm]
  congr 1
  · apply Measure.map_congr
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    exact ite_eq_left hu.2
  · apply Measure.map_congr
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    exact ite_eq_right (not_lt.mpr hu.1)

private theorem volume_weight_interval (lower : ℚ) (weight : ℚ≥0) :
    volume (Set.Ico (lower : ℝ) ((lower + weight : ℚ) : ℝ)) = (weight : ℝ≥0∞) := by
  rw [Real.volume_Ico, Rat.cast_add, add_sub_cancel_left, Rat.cast_nnratCast]
  rw [show (weight : ℝ) = ((weight : ℝ≥0) : ℝ) from by norm_cast,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_nnratCast]

/-- Cumulative threshold cells have exactly the supplied rational weights.
Zero weights and repeated outcomes require no separate cases. -/
theorem partition_measure (fallback : α) (lower : ℚ) (tickets : List (α × ℚ≥0)) :
    (volume.restrict (Set.Ico (lower : ℝ)
      ((lower + ((tickets.map Prod.snd).sum : ℚ) : ℚ) : ℝ))).map
        (partition fallback lower tickets) =
      (tickets.map fun ticket => (ticket.2 : ℝ≥0∞) • Measure.dirac ticket.1).sum := by
  induction tickets generalizing lower with
  | nil => simp [partition]
  | cons ticket rest ih =>
      cases rest with
      | nil =>
          rcases ticket with ⟨value, weight⟩
          simp only [partition, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [Measure.map_const, Measure.restrict_apply_univ, volume_weight_interval]
      | cons next rest =>
          rcases ticket with ⟨value, weight⟩
          have hl : (lower : ℝ) ≤ ((lower + weight : ℚ) : ℝ) := by
            simp only [Rat.cast_add]
            exact le_add_of_nonneg_right (by positivity)
          have hr : ((lower + weight : ℚ) : ℝ) ≤
              ((lower + ((weight + ((next :: rest).map Prod.snd).sum : ℚ≥0) : ℚ) : ℚ) : ℝ) := by
            simp only [NNRat.cast_add, Rat.cast_add]
            have : (0 : ℝ) ≤ ((((next :: rest).map Prod.snd).sum : ℚ) : ℝ) := by positivity
            linarith
          simp only [List.map_cons, List.sum_cons]
          have hsplit := map_restrict_Ico_ite (f := fun _ => value)
            (g := partition fallback (lower + weight) (next :: rest)) hl hr
            measurable_const (measurable_partition _ _ _)
          simp only [List.map_cons, List.sum_cons] at hsplit
          rw [show partition fallback lower ((value, weight) :: (next :: rest)) =
            (fun u => if u < ((lower + weight : ℚ) : ℝ) then value
              else partition fallback (lower + weight) (next :: rest) u) from rfl,
            hsplit]
          have hend : (lower + ((weight + ((next :: rest).map Prod.snd).sum : ℚ≥0) : ℚ) : ℚ) =
              (lower + weight) + (((next :: rest).map Prod.snd).sum : ℚ) := by
            simp only [NNRat.cast_add, add_assoc]
          simp only [List.map_cons, List.sum_cons] at hend ih
          rw [hend, ih, Measure.map_const, Measure.restrict_apply_univ, volume_weight_interval]

/-- The persistent fair-bit service samples exactly the input distribution's measure. -/
theorem concrete_law (distribution : FinRatPMF.Raw α) :
    (FreeM.runKernel answerKernel (client distribution) Prefix.empty).map Prod.fst =
      distribution.toMeasure := by
  rw [← adaptive_output_law]
  have hideal : ⇑(FreeM.runKernel idealAnswer (client distribution)) =
      (fun u => Measure.dirac (partition (fallback distribution) 0 distribution.toList u, u)) :=
    funext (ideal_scan _ _ _)
  have hm : Measurable (fun u : ℝ =>
      (partition (fallback distribution) 0 distribution.toList u, u)) :=
    (measurable_partition _ _ _).prodMk measurable_id
  rw [hideal, Measure.bind_dirac_eq_map _ hm, Measure.map_map measurable_fst hm]
  have h := partition_measure (fallback distribution) 0 distribution.toList
  have hsum : (distribution.toList.map Prod.snd).sum = 1 := distribution.sum_eq_one
  rw [hsum] at h
  simp only [NNRat.cast_one, zero_add, Rat.cast_one, Rat.cast_zero] at h
  rw [cellLaw_empty]
  exact h

end GeneralResults

variable {α : Type} [MeasurableSpace α]

/-- The theorem refers to the returned law of that exact executable machine. -/
theorem compiled_law (distribution : FinRatPMF.Raw α) :
    (𝒟[ITree.ofResumptionWithTau ((compiled distribution).denote ((), Prefix.empty))]).map
      Prod.fst = distribution.toMeasure := by
  rw [compiled, machineHandler.evalDist_compile answerKernel machineHandler_realizes]
  exact concrete_law distribution

/-- Under independent fair-bit answers, the compiled sampler returns almost surely. -/
theorem compiled_apply_univ (distribution : FinRatPMF.Raw α) :
    𝒟[ITree.ofResumptionWithTau ((compiled distribution).denote ((), Prefix.empty))]
      Set.univ = 1 := by
  have h := congrArg (fun law : Measure α => law Set.univ) (compiled_law distribution)
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa only [Set.preimage_univ, FinRatPMF.Raw.toMeasure_apply_univ] using h

/-- A bit cap bounds the whole sampler's error, including all timeout mass. -/
theorem capped_error_le (distribution : FinRatPMF.Raw α) (fuel : ℕ) :
    distribution.toMeasure.etvDist
      (𝒟[cappedClient (fun _ _ => fuel) (client distribution) Prefix.empty].map Prod.fst) ≤
        (distribution.toList.length - 1 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  rw [evalDist_cappedClient]
  have h := capped_output_law_le (fun _ _ => fuel) (client distribution) Prefix.empty
  rw [adaptive_output_law, concrete_law] at h
  exact h.trans (KernelHandler.expectedCharge_le_of_totalRollBound
    (cappedAnswer (fun _ _ => fuel)) (fun _ _ => (2 : ℝ≥0∞)⁻¹ ^ fuel)
    ((2 : ℝ≥0∞)⁻¹ ^ fuel) (fun _ _ => le_rfl) (client distribution)
    (distribution.toList.length - 1) (client_query_bound distribution) Prefix.empty)

end UniformThreshold.Categorical
