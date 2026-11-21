/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentrationPoisson
public import ToMathlib.Probability.Moments.IndependentPowers
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Tactic.IntervalCases

/-!
# Concentration of independent Poisson FORS loads

Moments of the potential `loadPotential`, the sum of fourteenth powers of `2^63` independent
rate-three Poisson loads (`poissonLoads`). `independent_sum_moments` computes the moments up to
order six of a sum of independent identically distributed variables (`sumMoment`);
`poisson_centered_sum_moments` specialises it to the centered loads `centeredLoad`, establishing
all needed integrability from the concrete product measure, and `poisson_sixth_sum_bound` bounds
the sixth centered moment of the potential, the input to a Markov-type tail bound.

This module concerns independent Poisson loads only: it does not compare them with uniform
@[expose]
instance selections, does not claim that adaptively generated signing transcripts have this law,
and does not prove SLH-DSA security.
-/

public section

open MeasureTheory ProbabilityTheory

namespace SLHDSA.SHAKE128s.ForsConcentration

section IndependentPowers

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

/-- The `order`-th power of a sum of two independent variables is integrable when all powers of
the summands up to `order` are. -/
lemma independent_integrable_add_power (hi : IndepFun X Y μ) (order : Nat)
    (hX : ∀ k ≤ order, Integrable (fun ω => X ω ^ k) μ)
    (hY : ∀ k ≤ order, Integrable (fun ω => Y ω ^ k) μ) :
    Integrable (fun ω => (X ω + Y ω) ^ order) μ := by
  exact ProbabilityTheory.IndepFun.integrable_add_pow hi order hX hY

/-- Binomial expansion of the `order`-th moment of a sum of two independent variables. -/
lemma independent_integral_add_power (hi : IndepFun X Y μ) (order : Nat)
    (hX : ∀ k ≤ order, Integrable (fun ω => X ω ^ k) μ)
    (hY : ∀ k ≤ order, Integrable (fun ω => Y ω ^ k) μ) :
    (∫ ω, (X ω + Y ω) ^ order ∂μ) =
      ∑ k ∈ Finset.range (order + 1),
        (∫ ω, X ω ^ k ∂μ) * (∫ ω, Y ω ^ (order - k) ∂μ) * order.choose k := by
  exact ProbabilityTheory.IndepFun.integral_add_pow hi order hX hY

/-- Moments through order six of a sum of `count` independent centered identically distributed
random variables with moments `m`, as polynomials in `count` (valid also for `count = 0, 1`). -/
@[expose] def sumMoment (m : Nat → ℝ) (count order : Nat) : ℝ :=
  ProbabilityTheory.centeredSumMomentUpToSix m count order

/-- The empty sum has the moments of the constant zero. -/
lemma sumMoment_zero (m : Nat → ℝ) (order : Nat) (hk : order ≤ 6) :
    sumMoment m 0 order = if order = 0 then 1 else 0 := by
  exact ProbabilityTheory.centeredSumMomentUpToSix_zero m order hk

/-- `sumMoment` satisfies the binomial recurrence for adding one more independent summand. -/
lemma sumMoment_succ (m : Nat → ℝ) (hm0 : m 0 = 1) (hm1 : m 1 = 0)
    (count order : Nat) (hk : order ≤ 6) :
    sumMoment m (count + 1) order =
      ∑ k ∈ Finset.range (order + 1),
        sumMoment m count k * m (order - k) * order.choose k := by
  exact ProbabilityTheory.centeredSumMomentUpToSix_succ m hm0 hm1 count order hk

/-- The moments up to order six of a finite sum of independent variables with common moments
`m` are given by `sumMoment`, and the corresponding powers of the sum are integrable. -/
lemma independent_sum_moments {ι : Type*} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hi : iIndepFun X μ) (hX : ∀ i, Measurable (X i))
    (m : Nat → ℝ) (hm0 : m 0 = 1) (hm1 : m 1 = 0)
    (hInt : ∀ i k, k ≤ 6 → Integrable (fun ω => X i ω ^ k) μ)
    (hMom : ∀ i k, k ≤ 6 → (∫ ω, X i ω ^ k ∂μ) = m k)
    (s : Finset ι) :
    ∀ k, k ≤ 6 → Integrable (fun ω => (∑ i ∈ s, X i ω) ^ k) μ ∧
      (∫ ω, (∑ i ∈ s, X i ω) ^ k ∂μ) = sumMoment m s.card k := by
  exact ProbabilityTheory.iIndepFun.integrable_pow_finsetSum_and_integral_eq
    X hi hX m hm0 hm1 hInt hMom s

end IndependentPowers

/-- Independent rate-three Poisson loads, before any coupling to fixed-size sampling. -/
@[expose] noncomputable def poissonLoads (bins : Nat) : Measure (Fin bins → Nat) :=
  Measure.pi (fun _ => poissonMeasure 3)

/-- The independent Poisson loads form a probability measure. -/
@[expose] instance (bins : Nat) : IsProbabilityMeasure (poissonLoads bins) := by
  unfold poissonLoads
  infer_instance

/-- The fourteenth power of a load, centered by its mean under a rate-three Poisson law. -/
@[expose] noncomputable def centeredLoad (n : Nat) : ℝ :=
  (n : ℝ) ^ 14 - (ForsMoments.touchard 14 3 : ℝ)

/-- The sum of the centered loads over all bins. -/
@[expose] noncomputable def centeredLoadSum {bins : Nat} (loads : Fin bins → Nat) : ℝ :=
  ∑ i, centeredLoad (loads i)

/-- The moments up to order six of `centeredLoadSum` under `poissonLoads` are `sumMoment` of the
centered moments `centeredMoment`, and the corresponding powers are integrable. -/
lemma poisson_centered_sum_moments (bins : Nat) :
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

set_option exponentiation.threshold 1024 in
/-- An explicit upper bound on the sixth moment of `centeredLoadSum` for `2^63` bins. -/
lemma poisson_sixth_sum_bound :
    (∫ loads, centeredLoadSum loads ^ 6 ∂poissonLoads (2 ^ 63)) ≤
      (2 ^ 63 : ℝ) * 2 ^ 359 +
        15 * (2 ^ 63) ^ 2 * 2 ^ 219 * 2 ^ 92 +
        10 * (2 ^ 63) ^ 2 * 2 ^ 308 +
        15 * (2 ^ 63) ^ 3 * (2 ^ 92) ^ 3 := by
  rw [(poisson_centered_sum_moments (2 ^ 63) 6 (by decide)).2]
  have hm := centeredMoment_bounds
  have h2 : 0 ≤ (centeredMoment 2 : ℝ) ∧ (centeredMoment 2 : ℝ) ≤ 2 ^ 92 := by
    exact_mod_cast And.intro hm.2.2.1 hm.2.2.2.1.le
  have h3 : 0 ≤ (centeredMoment 3 : ℝ) ∧ (centeredMoment 3 : ℝ) ≤ 2 ^ 154 := by
    exact_mod_cast And.intro hm.2.2.2.2.1 hm.2.2.2.2.2.1.le
  have h4 : 0 ≤ (centeredMoment 4 : ℝ) ∧ (centeredMoment 4 : ℝ) ≤ 2 ^ 219 := by
    exact_mod_cast And.intro hm.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.2.1.le
  have h6 : (centeredMoment 6 : ℝ) ≤ 2 ^ 359 := by
    exact_mod_cast hm.2.2.2.2.2.2.2.2.2.le
  simp only [sumMoment, ProbabilityTheory.centeredSumMomentUpToSix, Nat.cast_pow, Nat.cast_ofNat]
  have hb : (0 : ℝ) ≤ 2 ^ 63 - 2 := by norm_num
  have h23 : 0 ≤ (centeredMoment 2 : ℝ) ^ 3 := pow_nonneg h2.1 3
  calc
    _ ≤ (2 ^ 63 : ℝ) * 2 ^ 359 +
        15 * (2 ^ 63) * (2 ^ 63) * 2 ^ 219 * 2 ^ 92 +
        10 * (2 ^ 63) * (2 ^ 63) * (2 ^ 154) ^ 2 +
        15 * (2 ^ 63) * (2 ^ 63) * (2 ^ 63) * (2 ^ 92) ^ 3 := by
      gcongr <;> linarith only [h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h6, hb, h23]
    _ = _ := by norm_num

/-- The load potential: the sum of the fourteenth powers of all loads. -/
@[expose] noncomputable def loadPotential {bins : Nat} (loads : Fin bins → Nat) : ℝ :=
  ∑ i, (loads i : ℝ) ^ 14

/-- The centered load sum is the potential minus its mean. -/
lemma centeredLoadSum_eq {bins : Nat} (loads : Fin bins → Nat) :
    centeredLoadSum loads = loadPotential loads -
      (bins : ℝ) * (ForsMoments.touchard 14 3 : ℝ) := by
  simp [centeredLoadSum, centeredLoad, loadPotential, Finset.sum_sub_distrib]

end SLHDSA.SHAKE128s.ForsConcentration
