/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module

public import ToMathlib.Probability.Moments.IndependentPowers
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentration
import Mathlib.Tactic.NormNum

/-!
# Independent moment API and concrete FORS clients

Private compatibility witnesses relate the generic moments to the FORS moment polynomials.
The product-Poisson client proves the exact all-bin FORS moment formula using the generic API.
-/

public section

open MeasureTheory ProbabilityTheory

open SLHDSA.SHAKE128s.ForsConcentration

namespace SLHDSA.Refactor.IndependentPowersRecovery

/-- The finite polynomial agrees at every order, including its zero fallback above six. -/
private theorem sumMoment_eq_centeredSumMomentUpToSix
    (m : Nat → ℝ) (count order : Nat) :
    sumMoment m count order =
      ProbabilityTheory.centeredSumMomentUpToSix m count order := by
  rfl

section IndependentPowers

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

private lemma independent_integrable_add_power (hi : IndepFun X Y μ) (order : Nat)
    (hX : ∀ k ≤ order, Integrable (fun ω => X ω ^ k) μ)
    (hY : ∀ k ≤ order, Integrable (fun ω => Y ω ^ k) μ) :
    Integrable (fun ω => (X ω + Y ω) ^ order) μ := by
  exact IndepFun.integrable_add_pow hi order hX hY

private lemma independent_integral_add_power (hi : IndepFun X Y μ) (order : Nat)
    (hX : ∀ k ≤ order, Integrable (fun ω => X ω ^ k) μ)
    (hY : ∀ k ≤ order, Integrable (fun ω => Y ω ^ k) μ) :
    (∫ ω, (X ω + Y ω) ^ order ∂μ) =
      ∑ k ∈ Finset.range (order + 1),
        (∫ ω, X ω ^ k ∂μ) * (∫ ω, Y ω ^ (order - k) ∂μ) * order.choose k := by
  exact IndepFun.integral_add_pow hi order hX hY

private lemma sumMoment_zero (m : Nat → ℝ) (order : Nat) (hk : order ≤ 6) :
    sumMoment m 0 order = if order = 0 then 1 else 0 := by
  simpa only [sumMoment_eq_centeredSumMomentUpToSix] using
    ProbabilityTheory.centeredSumMomentUpToSix_zero m order hk

private lemma sumMoment_succ (m : Nat → ℝ) (hm0 : m 0 = 1) (hm1 : m 1 = 0)
    (count order : Nat) (hk : order ≤ 6) :
    sumMoment m (count + 1) order =
      ∑ k ∈ Finset.range (order + 1),
        sumMoment m count k * m (order - k) * order.choose k := by
  simpa only [sumMoment_eq_centeredSumMomentUpToSix] using
    ProbabilityTheory.centeredSumMomentUpToSix_succ m hm0 hm1 count order hk

private lemma independent_sum_moments {ι : Type*} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hi : iIndepFun X μ) (hX : ∀ i, Measurable (X i))
    (m : Nat → ℝ) (hm0 : m 0 = 1) (hm1 : m 1 = 0)
    (hInt : ∀ i k, k ≤ 6 → Integrable (fun ω => X i ω ^ k) μ)
    (hMom : ∀ i k, k ≤ 6 → (∫ ω, X i ω ^ k ∂μ) = m k)
    (s : Finset ι) :
    ∀ k, k ≤ 6 → Integrable (fun ω => (∑ i ∈ s, X i ω) ^ k) μ ∧
      (∫ ω, (∑ i ∈ s, X i ω) ^ k ∂μ) = sumMoment m s.card k := by
  simpa only [sumMoment_eq_centeredSumMomentUpToSix] using
    ProbabilityTheory.iIndepFun.integrable_pow_finsetSum_and_integral_eq
      X hi hX m hm0 hm1 hInt hMom s

end IndependentPowers

/-- The centered fourteenth-power FORS loads have exact moments through six under the
rate-three product-Poisson law, for every number of bins. -/
theorem poisson_centered_sum_moments (bins : Nat) :
    ∀ k, k ≤ 6 → Integrable (fun loads => centeredLoadSum loads ^ k) (poissonLoads bins) ∧
      (∫ loads, centeredLoadSum loads ^ k ∂poissonLoads bins) =
        sumMoment (fun j => (centeredMoment j : ℝ)) bins k := by
  let X : Fin bins → (Fin bins → Nat) → ℝ := fun i loads => centeredLoad (loads i)
  have hi : iIndepFun X (poissonLoads bins) := by
    exact iIndepFun_pi (fun _ => Measurable.aemeasurable .of_discrete)
  have hX (i : Fin bins) : Measurable (X i) :=
    Measurable.comp (show Measurable centeredLoad from .of_discrete) (measurable_pi_apply i)
  have hInt (i : Fin bins) (k : Nat) (_ : k ≤ 6) :
      Integrable (fun loads => X i loads ^ k) (poissonLoads bins) := by
    exact integrable_comp_eval (μ := fun _ : Fin bins => poissonMeasure 3) (i := i)
      (f := fun n => centeredLoad n ^ k) (poisson_integrable_centered_power 3 14 k _)
  have hMom (i : Fin bins) (k : Nat) (_ : k ≤ 6) :
      (∫ loads, X i loads ^ k ∂poissonLoads bins) = (centeredMoment k : ℝ) := by
    rw [show (fun loads => X i loads ^ k) =
      (fun loads => (centeredLoad (loads i)) ^ k) from rfl]
    exact (integral_comp_eval (μ := fun _ : Fin bins => poissonMeasure 3) (i := i)
      (f := fun n => centeredLoad n ^ k)
      (Measurable.aestronglyMeasurable .of_discrete)).trans (poisson_integral_centered_power k)
  have hm0 : (centeredMoment 0 : ℝ) = 1 := by exact_mod_cast centeredMoment_bounds.1
  have hm1 : (centeredMoment 1 : ℝ) = 0 := by exact_mod_cast centeredMoment_bounds.2.1
  simpa only [Finset.card_univ, Fintype.card_fin, X, centeredLoadSum] using
    independent_sum_moments X hi hX (fun j => (centeredMoment j : ℝ)) hm0 hm1 hInt hMom Finset.univ

example : @independent_integrable_add_power =
    @SLHDSA.SHAKE128s.ForsConcentration.independent_integrable_add_power := rfl

example : @independent_integral_add_power =
    @SLHDSA.SHAKE128s.ForsConcentration.independent_integral_add_power := rfl

example : @sumMoment_zero =
    @SLHDSA.SHAKE128s.ForsConcentration.sumMoment_zero := rfl

example : @sumMoment_succ =
    @SLHDSA.SHAKE128s.ForsConcentration.sumMoment_succ := rfl

example : @independent_sum_moments =
    @SLHDSA.SHAKE128s.ForsConcentration.independent_sum_moments := rfl

example (m : Nat → ℝ) : centeredSumMomentUpToSix m 0 0 = 1 := rfl

example (m : Nat → ℝ) : centeredSumMomentUpToSix m 0 6 = 0 := by
  norm_num [centeredSumMomentUpToSix]

example (m : Nat → ℝ) : centeredSumMomentUpToSix m 1 6 = m 6 := by
  norm_num [centeredSumMomentUpToSix]

example (m : Nat → ℝ) : centeredSumMomentUpToSix m 2 6 =
    2 * m 6 + 30 * m 4 * m 2 + 20 * m 3 ^ 2 := by
  norm_num [centeredSumMomentUpToSix]

example (m : Nat → ℝ) (count : Nat) : centeredSumMomentUpToSix m count 7 = 0 := rfl

end SLHDSA.Refactor.IndependentPowersRecovery
