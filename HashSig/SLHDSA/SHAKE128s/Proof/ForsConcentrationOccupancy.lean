/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentration
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Probability.Distributions.Uniform

/-!
# Fixed-count FORS load occupancy

The occupancy law `uniformLoads bins requests` of the loads produced by `requests` independent
uniform choices among `bins` instances, and its relation to the independent Poisson loads
`poissonLoads`:

* `wordCounts_fiber_card` and `uniformLoads_singleton` give the exact, correlated multinomial
  law, computed from coefficients of a multinomial expansion;
* `poissonLoads_eq_mixture` writes the product-Poisson law as a Poisson-weighted mixture of the
  occupancy laws;
* `uniformLoads_monotone` shows that increasing events become more likely as choices are added;
* `uniformLoads_mul_poisson_tail_le` combines the two into a de-Poissonization inequality, and
  `poisson_integral_square_sub` gives the Poisson variance used to control its denominator.

These facts concern independent uniform choices only; connecting adaptive random-oracle signing
transcripts to this experiment is a separate obligation.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SlhDsaSecurity.ForsConcentration

/-- The full vector of instance multiplicities in a word of uniformly sampled indices. -/
@[expose] noncomputable def wordCounts {bins requests : Nat} (word : Fin requests → Fin bins) :
    Fin bins →₀ Nat :=
  ∑ j, Finsupp.single (word j) 1

/-- The monomial of a word is the monomial of its multiplicity vector. -/
lemma wordCounts_polynomial {bins requests : Nat} (word : Fin requests → Fin bins) :
    (∏ j, MvPolynomial.X (word j) : MvPolynomial (Fin bins) Nat) =
      MvPolynomial.monomial (wordCounts word) 1 := by
  rw [wordCounts, MvPolynomial.monomial_sum_one]
  rfl

/-- Exact occupancy count for arbitrary numbers of bins and requests. The proof takes
coefficients in the multinomial expansion, so it preserves correlations between bins. -/
theorem wordCounts_fiber_card (bins requests : Nat) (counts : Fin bins →₀ Nat) :
    (Finset.univ.filter (fun word : Fin requests → Fin bins => wordCounts word = counts)).card =
      if counts.sum (fun _ n => n) = requests then counts.multinomial else 0 := by
  classical
  have hg : ((∑ i : Fin bins, MvPolynomial.X i : MvPolynomial (Fin bins) Nat)) ^ requests =
      ∑ word : Fin requests → Fin bins, MvPolynomial.monomial (wordCounts word) 1 := by
    rw [Fintype.sum_pow]
    exact Finset.sum_congr rfl (fun word _ => wordCounts_polynomial word)
  have hc := congrArg (fun p : MvPolynomial (Fin bins) Nat => p.coeff counts) hg
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype] at hc
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, eq_comm, Nat.cast_id] using hc.symm

/-- The multiplicity vector of a word, as a plain function. -/
@[expose] noncomputable def wordLoads {bins requests : Nat} (word : Fin requests → Fin bins) :
    Fin bins → Nat := wordCounts word

/-- `wordCounts_fiber_card` for plain load functions: the number of words with given loads is
the multinomial coefficient when the loads sum to the word length, and zero otherwise. -/
lemma wordLoads_fiber_card (bins requests : Nat) (counts : Fin bins → Nat) :
    (Finset.univ.filter (fun word : Fin requests → Fin bins => wordLoads word = counts)).card =
      if (∑ i, counts i) = requests then Nat.multinomial Finset.univ counts else 0 := by
  classical
  have hc := wordCounts_fiber_card bins requests (Finsupp.equivFunOnFinite.symm counts)
  have he (word : Fin requests → Fin bins) :
      wordCounts word = Finsupp.equivFunOnFinite.symm counts ↔ wordLoads word = counts := by
    constructor
    · intro h
      exact congrArg (fun f : Fin bins →₀ Nat => (f : Fin bins → Nat)) h
    · intro h
      apply Finsupp.ext
      intro i
      exact congrFun h i
  simp_rw [he] at hc
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl),
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at hc
  exact hc

/-- The concrete multinomial occupancy measure obtained from independent uniform choices. -/
@[expose] noncomputable def uniformLoads (bins requests : Nat) : Measure (Fin bins → Nat) :=
  (uniformOn (Set.univ : Set (Fin requests → Fin bins))).map wordLoads

/-- The occupancy law is a probability measure. -/
@[expose] instance (bins requests : Nat) [NeZero bins] :
    IsProbabilityMeasure (uniformLoads bins requests) := by
  unfold uniformLoads
  exact (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable .of_discrete)).mpr
    inferInstance

/-- The occupancy law is the multinomial law. -/
lemma uniformLoads_singleton (bins requests : Nat) (counts : Fin bins → Nat) :
    uniformLoads bins requests {counts} =
      (if (∑ i, counts i) = requests then
        (Nat.multinomial Finset.univ counts : ENNReal) / (bins : ENNReal) ^ requests else 0) := by
  classical
  rw [uniformLoads, Measure.map_apply .of_discrete (measurableSet_singleton _), uniformOn_univ]
  have hpre : (wordLoads ⁻¹' {counts} : Set (Fin requests → Fin bins)) =
      ((Finset.univ.filter (fun word : Fin requests → Fin bins => wordLoads word = counts) :
        Finset (Fin requests → Fin bins)) : Set (Fin requests → Fin bins)) := by
    ext word
    simp
  rw [hpre, Measure.count_apply_finset]
  rw [wordLoads_fiber_card]
  split_ifs <;> simp_all [Fintype.card_fin]

/-- The probability of a load vector under independent rate-three Poisson loads. -/
lemma poissonLoads_real_singleton (bins : Nat) (counts : Fin bins → Nat) :
    (poissonLoads bins).real {counts} =
      Real.exp (-(3 * (bins : ℝ))) * 3 ^ (∑ i, counts i) /
        ∏ i, (counts i).factorial := by
  rw [measureReal_def, poissonLoads, Measure.pi_singleton, ENNReal.toReal_prod]
  change (∏ i, (poissonMeasure 3).real {counts i}) = _
  simp_rw [poissonMeasure_real_singleton]
  norm_num only [NNReal.coe_ofNat]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum, ← Real.exp_nat_mul]
  simp only [Nat.cast_prod]
  congr 2
  ring_nf

/-- `uniformLoads_singleton` for real-valued probabilities. -/
lemma uniformLoads_real_singleton (bins requests : Nat) (counts : Fin bins → Nat) :
    (uniformLoads bins requests).real {counts} =
      (if (∑ i, counts i) = requests then
        (Nat.multinomial Finset.univ counts : ℝ) / (bins : ℝ) ^ requests else 0) := by
  rw [measureReal_def, uniformLoads_singleton]
  split_ifs <;> simp

/-- The Poisson probability of a load vector factors as the probability of its total under the
total Poisson count times its occupancy probability given that total. -/
lemma poissonLoads_singleton_factor (bins : Nat) [NeZero bins] (counts : Fin bins → Nat) :
    poissonLoads bins {counts} =
      poissonMeasure (3 * (bins : ℝ≥0)) {∑ i, counts i} *
        uniformLoads bins (∑ i, counts i) {counts} := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  change (poissonLoads bins).real {counts} =
    (poissonMeasure (3 * (bins : ℝ≥0))).real {∑ i, counts i} *
      (uniformLoads bins (∑ i, counts i)).real {counts}
  rw [poissonLoads_real_singleton, poissonMeasure_real_singleton, uniformLoads_real_singleton,
    ite_eq_left rfl]
  simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, mul_pow, Nat.cast_prod]
  have hb : (bins : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne bins)
  have hf : (∏ i, ((counts i).factorial : ℝ)) * (Nat.multinomial Finset.univ counts : ℝ) =
      ((∑ i, counts i).factorial : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hp : (∏ i, ((counts i).factorial : ℝ)) ≠ 0 := by positivity
  have hm : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos Finset.univ counts).ne'
  rw [← hf]
  field_simp

/-- Poissonization identity for the full correlated occupancy experiment. -/
theorem poissonLoads_eq_mixture (bins : Nat) [NeZero bins] :
    poissonLoads bins = Measure.sum (fun requests : Nat =>
      poissonMeasure (3 * (bins : ℝ≥0)) {requests} • uniformLoads bins requests) := by
  apply Measure.ext_of_singleton
  intro counts
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, smul_eq_mul, uniformLoads_singleton, mul_ite, mul_zero]
  rw [tsum_eq_single (∑ i, counts i)]
  · simpa [uniformLoads_singleton] using poissonLoads_singleton_factor bins counts
  · intro requests hne
    simp [Ne.symm hne]

/-- Prepending a choice to a word adds one to the load of the chosen instance. -/
lemma wordLoads_cons {bins requests : Nat} (head : Fin bins) (word : Fin requests → Fin bins) :
    wordLoads (Fin.cons head word) = fun i => (if head = i then 1 else 0) + wordLoads word i := by
  classical
  funext i
  simp [wordLoads, wordCounts, Fin.sum_univ_succ, Finsupp.single_apply]

open scoped Classical in
/-- The occupancy probability of an event is the fraction of words whose loads lie in it. -/
lemma uniformLoads_real_apply (bins requests : Nat) (event : Set (Fin bins → Nat)) :
    (uniformLoads bins requests).real event =
      (Fintype.card {word : Fin requests → Fin bins // wordLoads word ∈ event} : ℝ) /
        (bins : ℝ) ^ requests := by
  classical
  rw [measureReal_def, uniformLoads, Measure.map_apply .of_discrete .of_discrete, uniformOn_univ,
    Measure.count_apply_finite' (Set.toFinite _) .of_discrete]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]
  rw [Set.Finite.card_toFinset, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rfl

/-- Monotone events become more likely as independent uniform choices are appended. -/
theorem uniformLoads_monotone (bins : Nat) [NeZero bins] (event : Set (Fin bins → Nat))
    (hup : ∀ {a b : Fin bins → Nat}, a ≤ b → a ∈ event → b ∈ event) :
    Monotone (fun requests => uniformLoads bins requests event) := by
  classical
  apply monotone_nat_of_le_succ
  intro requests
  let embed : (Fin bins) × {word : Fin requests → Fin bins // wordLoads word ∈ event} →
      {word : Fin (requests + 1) → Fin bins // wordLoads word ∈ event} :=
    fun pair => ⟨Fin.cons pair.1 pair.2.val, hup
      (by intro i; rw [wordLoads_cons]; exact Nat.le_add_left _ _) pair.2.property⟩
  have hinj : Function.Injective embed := by
    intro a b h
    have heq : (Fin.cons a.1 a.2.val : Fin (requests + 1) → Fin bins) =
        (Fin.cons b.1 b.2.val : Fin (requests + 1) → Fin bins) := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := Fin.cons_inj.mp heq
    exact Prod.ext h1 (Subtype.ext h2)
  have hcard := Fintype.card_le_of_injective embed hinj
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  change (uniformLoads bins requests).real event ≤ (uniformLoads bins (requests + 1)).real event
  rw [uniformLoads_real_apply, uniformLoads_real_apply]
  have hb : (0 : ℝ) < bins := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne bins)
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  have hc : (bins : ℝ) *
      (Fintype.card {word : Fin requests → Fin bins // wordLoads word ∈ event} : ℝ) ≤
      Fintype.card {word : Fin (requests + 1) → Fin bins // wordLoads word ∈ event} := by
    exact_mod_cast hcard
  calc
    _ = ((bins : ℝ) * Fintype.card {word : Fin requests → Fin bins // wordLoads word ∈ event}) *
        (bins : ℝ) ^ requests := by ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- De-Poissonization for any increasing load event, with the exact denominator
left as a probability rather than an asymptotic approximation. -/
theorem uniformLoads_mul_poisson_tail_le (bins requests : Nat) [NeZero bins]
    (event : Set (Fin bins → Nat))
    (hup : ∀ {a b : Fin bins → Nat}, a ≤ b → a ∈ event → b ∈ event) :
    uniformLoads bins requests event *
      poissonMeasure (3 * (bins : ℝ≥0)) {n | requests ≤ n} ≤ poissonLoads bins event := by
  rw [poissonLoads_eq_mixture, Measure.sum_apply _ .of_discrete]
  rw [← Measure.tsum_indicator_apply_singleton
    (poissonMeasure (3 * (bins : ℝ≥0))) {n | requests ≤ n} .of_discrete,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Measure.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [mul_comm]
    exact mul_le_mul_right (uniformLoads_monotone bins event hup h) _
  · simp

/-- The variance of a Poisson variable with integer rate `rate` is `rate`. -/
lemma poisson_integral_square_sub (rate : Nat) :
    (∫ n : Nat, ((n : ℝ) - rate) ^ 2 ∂poissonMeasure (rate : ℝ≥0)) = rate := by
  have h1 : Integrable (fun n : Nat => (n : ℝ)) (poissonMeasure (rate : ℝ≥0)) := by
    simpa using poisson_integrable_power (rate : ℝ≥0) 1
  have h2 := poisson_integrable_power (rate : ℝ≥0) 2
  have hpoly (n : Nat) : ((n : ℝ) - rate) ^ 2 =
      (n : ℝ) ^ 2 - (2 * (rate : ℝ)) * n + (rate : ℝ) ^ 2 := by ring_nf
  simp_rw [hpoly]
  rw [integral_add (f := fun n : Nat => (n : ℝ) ^ 2 - (2 * (rate : ℝ)) * n)
    (g := fun _ => (rate : ℝ) ^ 2) (h2.sub (h1.const_mul (2 * rate))) (integrable_const _),
    integral_sub h2 (h1.const_mul (2 * rate)), integral_const_mul, integral_const]
  have hmean : (∫ n : Nat, (n : ℝ) ∂poissonMeasure (rate : ℝ≥0)) = rate := by
    simpa [ForsMoments.touchard, Finset.sum_range_succ, Nat.stirlingSecond] using
      poisson_integral_power_nat rate 1
  rw [hmean, poisson_integral_power_nat]
  norm_num [ForsMoments.touchard, Finset.sum_range_succ, Nat.stirlingSecond]
  ring_nf

end SlhDsaSecurity.ForsConcentration
