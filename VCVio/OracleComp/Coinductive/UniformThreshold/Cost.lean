/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold
public import VCVio.EvalDist.ResumptionCost
public import ToMathlib.Probability.UniformOn
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite execution and bit-cost tails of the persistent threshold sampler

The cost counts new bits, so previously retained prefixes are free. At every unresolved
query at most one child interval remains unresolved. This gives the uniform geometric
tail bound from every starting prefix, even after adaptively chosen earlier queries.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace UniformThreshold

/-- Fair-bit answers carry their discrete measurable space. -/
local instance coinAnswerMeasurableSpace :
    (a : coinSpec.toPFunctor.A) → MeasurableSpace (coinSpec.toPFunctor.B a) :=
  fun _ => ⊤

/-- The law of a query capped after `fuel` new bits, with cutoff represented by `none`. -/
noncomputable def boundedLaw (q : ℚ) (p : Prefix) (fuel : ℕ) :
    Measure (Option (Bool × Prefix)) := FreeM.denote ((machine q).unroll fuel p)

instance (q : ℚ) (p : Prefix) (fuel : ℕ) : IsProbabilityMeasure (boundedLaw q p fuel) :=
  FreeM.isProbabilityMeasure_denote _

/-- A resolved query returns immediately, for every budget including zero. -/
theorem boundedLaw_of_resolved (q : ℚ) (p : Prefix) (fuel : ℕ) {b : Bool}
    (h : classify q p = some b) : boundedLaw q p fuel = Measure.dirac (some (b, p)) := by
  rw [boundedLaw, DynSystem.DynComputation.unroll_return _ _ _ (b, p)
    (by rw [machine_view, h])]
  exact FreeM.denote_pure _

/-- An unresolved query with zero budget records a cutoff. -/
theorem boundedLaw_zero_of_unresolved (q : ℚ) (p : Prefix) (h : classify q p = none) :
    boundedLaw q p 0 = Measure.dirac none := by
  rw [boundedLaw, DynSystem.DynComputation.unroll_query_zero _ _ () p.push
    (by rw [machine_view, h])]
  exact FreeM.denote_pure _

/-- An unresolved query reads a fair bit and continues at the selected child prefix. -/
theorem boundedLaw_succ (q : ℚ) (p : Prefix) (fuel : ℕ) (h : classify q p = none) :
    boundedLaw q p (fuel + 1) = (uniformOn (Set.univ : Set Bool)).bind
      (fun b => boundedLaw q (p.push b) fuel) := by
  rw [boundedLaw, DynSystem.DynComputation.unroll_query_succ _ _ _ () p.push
    (by rw [machine_view, h]), FreeM.denote_liftBind (P := coinSpec.toPFunctor)
      _ _ Measurable.of_discrete.aemeasurable]
  rw [show PFunctor.AnswerMeasure.toMeasure (P := coinSpec.toPFunctor) () =
    uniformOn (Set.univ : Set Bool) from
      OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn (spec := coinSpec) ()]
  rfl

/-- One unresolved step averages the two refined-prefix laws. -/
theorem boundedLaw_succ_apply (q : ℚ) (p : Prefix) (fuel : ℕ)
    (h : classify q p = none) (event : Set (Option (Bool × Prefix))) :
    boundedLaw q p (fuel + 1) event =
      (boundedLaw q (p.push false) fuel event + boundedLaw q (p.push true) fuel event) *
        (2 : ℝ≥0∞)⁻¹ := by
  rw [boundedLaw_succ q p fuel h]
  rw [Measure.bind_apply (Set.to_countable event).measurableSet
    Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp only [uniformOn_univ_apply_singleton, Fintype.card_bool, Nat.cast_ofNat,
    Fintype.sum_bool]
  ring

/-- The probability of requiring more than `fuel` additional bits is at most `2⁻fuel`. -/
theorem cutoff_le (q : ℚ) (p : Prefix) (fuel : ℕ) :
    boundedLaw q p fuel {none} ≤ (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  induction fuel generalizing p with
  | zero => simpa using (measure_le_one (μ := boundedLaw q p 0) (s := {none}))
  | succ fuel ih =>
      cases hc : classify q p with
      | some b => simp [boundedLaw_of_resolved q p (fuel + 1) hc]
      | none =>
          rw [boundedLaw_succ_apply q p fuel hc, pow_succ]
          gcongr
          rcases child_resolves q p with hl | hr
          · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hl
            rw [boundedLaw_of_resolved q (p.push false) fuel hb]
            simpa using ih (p.push true)
          · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hr
            rw [boundedLaw_of_resolved q (p.push true) fuel hb]
            simpa using ih (p.push false)

/-- The executable cutoff law is the coinductive truncation law from the same prefix. -/
theorem boundedLaw_eq_truncateMeasure (q : ℚ) (p : Prefix) (fuel : ℕ) :
    boundedLaw q p fuel = Resumption.truncateMeasure fuel ((machine q).denote p) :=
  DynSystem.DynComputation.denote_unroll (machine q) fuel p

/-- The threshold query returns almost surely from every retained prefix. -/
theorem returnedMeasure_univ (q : ℚ) (p : Prefix) :
    Resumption.returnedMeasure ((machine q).denote p) Set.univ = 1 := by
  apply Resumption.returnedMeasure_univ_eq_one_of_cutoff_tendsto
  simp_rw [← boundedLaw_eq_truncateMeasure]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))
    (fun _ => zero_le) (cutoff_le q p)

/-- Every threshold query needs at most two new bits in expectation, uniformly in its history. -/
theorem expectedQueries_le_two (q : ℚ) (p : Prefix) :
    Resumption.expectedQueries ((machine q).denote p) ≤ 2 := by
  rw [Resumption.expectedQueries_eq_tsum (P := coinSpec.toPFunctor)]
  simp_rw [← boundedLaw_eq_truncateMeasure]
  calc
    _ ≤ ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k := ENNReal.tsum_le_tsum (cutoff_le q p)
    _ = 2 := by rw [ENNReal.tsum_geometric]; norm_num

/-- Averaging over an adaptively chosen threshold and prefix preserves the cutoff bound. -/
theorem lintegral_cutoff_le (μ : Measure (ℚ × Prefix)) [IsProbabilityMeasure μ] (fuel : ℕ) :
    ∫⁻ input, boundedLaw input.1 input.2 fuel {none} ∂μ ≤ (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  calc
    _ ≤ ∫⁻ _ : ℚ × Prefix, (2 : ℝ≥0∞)⁻¹ ^ fuel ∂μ :=
      lintegral_mono fun input => cutoff_le input.1 input.2 fuel
    _ = _ := by simp

/-- Increasing query caps give a session-wide failure bound without assuming independence
or a fixed number of adaptive queries. Events can include the condition that a query is reached. -/
theorem ever_timeout_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (events : ℕ → Set Ω) (security : ℕ)
    (h : ∀ i, μ (events i) ≤ (2 : ℝ≥0∞)⁻¹ ^ (security + i + 1)) :
    μ (⋃ i, events i) ≤ (2 : ℝ≥0∞)⁻¹ ^ security := by
  calc
    _ ≤ ∑' i, μ (events i) := measure_iUnion_le _
    _ ≤ ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (security + i + 1) := ENNReal.tsum_le_tsum h
    _ = (2 : ℝ≥0∞)⁻¹ ^ security := by
      simp_rw [show ∀ i, security + i + 1 = security + (i + 1) from fun _ => by omega,
        pow_add]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      norm_num
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

end UniformThreshold
