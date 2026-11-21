/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module

public import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite independent power moments

Exact binomial moments and centered common-moment finite sums through order six are derived
from Mathlib independence and integrability. Independent centered signs give the exact sixth
moment of a simple symmetric random walk, including empty and singleton index sets.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

section IndependentPowers

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

/-- The `order`-th power of a sum of two independent variables is integrable when all powers of
the summands up to `order` are. -/
lemma IndepFun.integrable_add_pow (hi : IndepFun X Y μ) (order : Nat)
    (hX : ∀ k ≤ order, Integrable (fun ω => X ω ^ k) μ)
    (hY : ∀ k ≤ order, Integrable (fun ω => Y ω ^ k) μ) :
    Integrable (fun ω => (X ω + Y ω) ^ order) μ := by
  simp only [add_pow]
  apply integrable_finsetSum
  intro k hk
  have hk' : k ≤ order := by have := Finset.mem_range.mp hk; omega
  have hi' : IndepFun (fun ω => X ω ^ k) (fun ω => Y ω ^ (order - k)) μ :=
    hi.comp (measurable_id.pow_const k) (measurable_id.pow_const (order - k))
  exact (hi'.integrable_mul (hX k hk') (hY _ (by omega))).mul_const _

/-- Binomial expansion of the `order`-th moment of a sum of two independent variables. -/
lemma IndepFun.integral_add_pow (hi : IndepFun X Y μ) (order : Nat)
    (hX : ∀ k ≤ order, Integrable (fun ω => X ω ^ k) μ)
    (hY : ∀ k ≤ order, Integrable (fun ω => Y ω ^ k) μ) :
    (∫ ω, (X ω + Y ω) ^ order ∂μ) =
      ∑ k ∈ Finset.range (order + 1),
        (∫ ω, X ω ^ k ∂μ) * (∫ ω, Y ω ^ (order - k) ∂μ) * order.choose k := by
  simp only [add_pow]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ order := by have := Finset.mem_range.mp hk; omega
    rw [integral_mul_const]
    congr 1
    have hi' : IndepFun (fun ω => X ω ^ k) (fun ω => Y ω ^ (order - k)) μ :=
      hi.comp (measurable_id.pow_const k) (measurable_id.pow_const (order - k))
    exact hi'.integral_fun_mul_eq_mul_integral
      (hX k hk').aestronglyMeasurable (hY _ (by omega)).aestronglyMeasurable
  · intro k hk
    have hk' : k ≤ order := by have := Finset.mem_range.mp hk; omega
    have hi' : IndepFun (fun ω => X ω ^ k) (fun ω => Y ω ^ (order - k)) μ :=
      hi.comp (measurable_id.pow_const k) (measurable_id.pow_const (order - k))
    exact (hi'.integrable_mul (hX k hk') (hY _ (by omega))).mul_const _

/-- Polynomials for moments through order six of sums of `count` independent centered variables
with common moments through six given by `m`, valid also for `count = 0, 1`. -/
@[expose] def centeredSumMomentUpToSix (m : Nat → ℝ) (count order : Nat) : ℝ :=
  let n : ℝ := count
  match order with
  | 0 => 1
  | 1 => 0
  | 2 => n * m 2
  | 3 => n * m 3
  | 4 => n * m 4 + 3 * n * (n - 1) * (m 2) ^ 2
  | 5 => n * m 5 + 10 * n * (n - 1) * m 3 * m 2
  | 6 => n * m 6 + 15 * n * (n - 1) * m 4 * m 2 +
      10 * n * (n - 1) * (m 3) ^ 2 +
      15 * n * (n - 1) * (n - 2) * (m 2) ^ 3
  | _ => 0

/-- The empty sum has the moments of the constant zero. -/
lemma centeredSumMomentUpToSix_zero (m : Nat → ℝ) (order : Nat) (hk : order ≤ 6) :
    centeredSumMomentUpToSix m 0 order = if order = 0 then 1 else 0 := by
  interval_cases order <;> norm_num [centeredSumMomentUpToSix]

/-- `centeredSumMomentUpToSix` satisfies the binomial recurrence for adding one more
independent summand. -/
lemma centeredSumMomentUpToSix_succ (m : Nat → ℝ) (hm0 : m 0 = 1) (hm1 : m 1 = 0)
    (count order : Nat) (hk : order ≤ 6) :
    centeredSumMomentUpToSix m (count + 1) order =
      ∑ k ∈ Finset.range (order + 1),
        centeredSumMomentUpToSix m count k * m (order - k) * order.choose k := by
  interval_cases order <;>
    norm_num [centeredSumMomentUpToSix, Finset.sum_range_succ, hm0, hm1, Nat.choose] <;> ring

/-- The moments up to order six of a finite sum of independent variables with common moments
`m` are given by `centeredSumMomentUpToSix`. The corresponding powers of the sum are
integrable. -/
lemma iIndepFun.integrable_pow_finsetSum_and_integral_eq {ι : Type*} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hi : iIndepFun X μ) (hX : ∀ i, Measurable (X i))
    (m : Nat → ℝ) (hm0 : m 0 = 1) (hm1 : m 1 = 0)
    (hInt : ∀ i k, k ≤ 6 → Integrable (fun ω => X i ω ^ k) μ)
    (hMom : ∀ i k, k ≤ 6 → (∫ ω, X i ω ^ k ∂μ) = m k)
    (s : Finset ι) :
    ∀ k, k ≤ 6 → Integrable (fun ω => (∑ i ∈ s, X i ω) ^ k) μ ∧
      (∫ ω, (∑ i ∈ s, X i ω) ^ k ∂μ) = centeredSumMomentUpToSix m s.card k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro k hk
      simp only [Finset.sum_empty, Finset.card_empty, centeredSumMomentUpToSix_zero m k hk]
      constructor
      · exact integrable_const _
      · by_cases hk0 : k = 0 <;> simp [hk0]
  | @insert i s his ih =>
      intro k hk
      have hsum (ω : Ω) : (∑ j ∈ insert i s, X j ω) =
          (∑ j ∈ s, X j ω) + X i ω := by
        simp [his, add_comm]
      simp_rw [hsum]
      have hInd : IndepFun (fun ω => ∑ j ∈ s, X j ω) (X i) μ :=
        by simpa only [← Finset.sum_apply] using hi.indepFun_finsetSum_of_notMem hX his
      have hLeft : ∀ j ≤ k, Integrable (fun ω => (∑ i ∈ s, X i ω) ^ j) μ :=
        fun j hj => (ih j (hj.trans hk)).1
      have hRight : ∀ j ≤ k, Integrable (fun ω => X i ω ^ j) μ :=
        fun j hj => hInt i j (hj.trans hk)
      refine ⟨IndepFun.integrable_add_pow hInd k hLeft hRight, ?_⟩
      rw [IndepFun.integral_add_pow hInd k hLeft hRight, Finset.card_insert_of_notMem his,
        centeredSumMomentUpToSix_succ m hm0 hm1 _ _ hk]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
      rw [(ih j (hj'.trans hk)).2, hMom i (k - j) (by omega)]

end IndependentPowers

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Independent centered real signs have the exact simple-random-walk sixth moment. -/
theorem iIndepFun.integral_pow_six_finsetSum_of_signs
    (X : ι → Ω → ℝ) (hi : iIndepFun X μ) (hX : ∀ i, Measurable (X i))
    (hSquare : ∀ i, ∀ᵐ ω ∂μ, X i ω ^ 2 = 1)
    (hCenter : ∀ i, (∫ ω, X i ω ∂μ) = 0) (s : Finset ι) :
    Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 6) μ ∧
      (∫ ω, (∑ i ∈ s, X i ω) ^ 6 ∂μ) =
        15 * (s.card : ℝ) ^ 3 - 30 * (s.card : ℝ) ^ 2 + 16 * (s.card : ℝ) := by
  classical
  let m : Nat → ℝ := fun k => if Even k then 1 else 0
  have hSign (i : ι) : ∀ᵐ ω ∂μ, X i ω = 1 ∨ X i ω = -1 :=
    (hSquare i).mono fun _ h => sq_eq_one_iff.mp h
  have hInt (i : ι) (k : Nat) : Integrable (fun ω => X i ω ^ k) μ := by
    apply (integrable_const (1 : ℝ)).mono' ((hX i).pow_const k).aestronglyMeasurable
    filter_upwards [hSign i] with ω h
    rcases h with h | h <;> simp [h]
  have hReduce (i : ι) (k : Nat) (hk : k ≤ 6) :
      (fun ω => X i ω ^ k) =ᵐ[μ] (fun ω => if Even k then 1 else X i ω) := by
    filter_upwards [hSign i] with ω h
    rcases h with h | h
    · simp [h]
    · interval_cases k <;> norm_num [h] <;> decide
  have hMom (i : ι) (k : Nat) (hk : k ≤ 6) : (∫ ω, X i ω ^ k ∂μ) = m k := by
    rw [integral_congr_ae (hReduce i k hk)]
    by_cases even : Even k
    · simp [even, m]
    · simp [even, m, hCenter]
  have h := iIndepFun.integrable_pow_finsetSum_and_integral_eq X hi hX m
    (by norm_num [m]) (by norm_num [m]) (fun i k _ => hInt i k) hMom s 6 (by decide)
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [centeredSumMomentUpToSix, m, even_iff_two_dvd]
  ring

end ProbabilityTheory
