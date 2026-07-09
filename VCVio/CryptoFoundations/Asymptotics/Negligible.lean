/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Negligible Functions

This file defines a simple wrapper around `SuperpolynomialDecay` for functions `ℕ → ℝ≥0∞`,
as this is usually the situation for cryptographic reductions.

## Main Results

- `negligible_zero`, `negligible_of_zero`: The zero function is negligible.
- `negligible_of_le`: Monotonicity — bounded by negligible is negligible.
- `negligible_add`: Sum of negligible functions is negligible.
- `negligible_sum`: Finite sum of negligible functions is negligible.
- `negligible_const_mul`: Constant multiple of negligible is negligible.
- `negligible_of_eventually_zero`, `negligible_of_eventually_le`: Only the behavior at
  sufficiently large parameters matters.
- `negligible_iff_forall_eventually_le_inv_pow`,
  `negligible_iff_forall_polynomial_eventually_le`: The classical characterizations of
  negligibility as eventual domination by every inverse monomial resp. every inverse
  polynomial.
-/

open ENNReal Asymptotics Filter

/-- A function `f` is negligible if it decays faster than any polynomial function. -/
def negligible (f : ℕ → ℝ≥0∞) : Prop :=
  SuperpolynomialDecay atTop (fun x => ↑x) f

@[simp] def negligible_iff (f : ℕ → ℝ≥0∞) :
    negligible f ↔ SuperpolynomialDecay atTop (fun x => ↑x) f := Iff.rfl

lemma negligible_zero : negligible 0 := superpolynomialDecay_zero _ _

lemma negligible_of_zero {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n = 0) : negligible f :=
  funext hf ▸ negligible_zero

/-- Negligibility is monotone: if `f ≤ g` pointwise and `g` is negligible, then `f` is. -/
theorem negligible_of_le {f g : ℕ → ℝ≥0∞} (hfg : ∀ n, f n ≤ g n) (hg : negligible g) :
    negligible f := fun p =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg p)
    (fun _ => zero_le) (fun n => mul_le_mul_of_nonneg_left (hfg n) zero_le)

/-- Sum of two negligible functions is negligible. -/
theorem negligible_add {f g : ℕ → ℝ≥0∞} (hf : negligible f) (hg : negligible g) :
    negligible (f + g) :=
  hf.add hg

/-- Constant multiple of a negligible function is negligible (requires `c ≠ ⊤`
because multiplication by `⊤` is discontinuous at `0` in `ℝ≥0∞`). -/
theorem negligible_const_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    negligible (fun n => c * f n) := by
  intro p
  simpa only [mul_zero] using
    (ENNReal.Tendsto.const_mul (hf p) (.inr hc)).congr (fun n => by rw [mul_left_comm])

/-- A finite sum of negligible functions is negligible. -/
theorem negligible_sum {ι : Type*} {s : Finset ι} {f : ι → ℕ → ℝ≥0∞}
    (h : ∀ i ∈ s, negligible (f i)) :
    negligible (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty => exact negligible_zero
  | insert _ _ hnotin ih =>
    simp_rw [Finset.sum_insert hnotin]
    exact negligible_add
      (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `f` is negligible, then `fun n => (↑n)^d * f n` is negligible for any fixed `d`.
Absorbs polynomial powers of the parameter into the superpolynomial decay. -/
theorem negligible_pow_mul {f : ℕ → ℝ≥0∞} (hf : negligible f) (d : ℕ) :
    negligible (fun n => (↑n : ℝ≥0∞) ^ d * f n) :=
  hf.param_pow_mul d

/-- If `f` is negligible, then `fun n => ↑(p.eval n) * f n` is negligible for any polynomial `p`.
This is the key lemma for handling polynomial-loss security reductions. -/
theorem negligible_polynomial_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    (p : Polynomial ℕ) :
    negligible (fun n => ↑(p.eval n) * f n) := by
  have heq : ∀ n, (↑(p.eval n) : ℝ≥0∞) * f n =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        ↑(p.coeff i) * ((↑n : ℝ≥0∞) ^ i * f n) := by
    intro n
    simp [Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
  simp_rw [heq]
  exact negligible_sum fun i _ =>
    negligible_const_mul (negligible_pow_mul hf i) (ENNReal.natCast_ne_top _)

/-- A function that is eventually zero is negligible: negligibility only constrains
sufficiently large parameters, so finitely many exceptional values are irrelevant. -/
theorem negligible_of_eventually_zero {f : ℕ → ℝ≥0∞} (hf : ∀ᶠ n in atTop, f n = 0) :
    negligible f :=
  negligible_zero.congr' (hf.mono fun _ h => h.symm)

/-- Negligibility is monotone up to finitely many exceptions: eventually bounded by a
negligible function is negligible. -/
theorem negligible_of_eventually_le {f g : ℕ → ℝ≥0∞} (hfg : ∀ᶠ n in atTop, f n ≤ g n)
    (hg : negligible g) : negligible f := fun p =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hg p)
    (Eventually.of_forall fun _ => zero_le)
    (hfg.mono fun _ hn => mul_le_mul_of_nonneg_left hn zero_le)

/-- Monomial characterization of negligibility: `f` is negligible iff it is eventually
below `1 / n ^ c` for every exponent `c`. -/
theorem negligible_iff_forall_eventually_le_inv_pow {f : ℕ → ℝ≥0∞} :
    negligible f ↔ ∀ c : ℕ, ∀ᶠ n in atTop, f n ≤ ((n : ℝ≥0∞) ^ c)⁻¹ := by
  constructor
  · intro hf c
    filter_upwards [(hf c).eventually_lt_const zero_lt_one] with n hn
    exact ENNReal.le_inv_iff_mul_le.mpr (mul_comm (f n) _ ▸ hn.le)
  · intro h c
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [h (c + 1), eventually_ge_atTop 1] with n hfn hn1
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hn1
    have hnt : (n : ℝ≥0∞) ^ c ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)
    calc (n : ℝ≥0∞) ^ c * f n
        ≤ (n : ℝ≥0∞) ^ c * ((n : ℝ≥0∞) ^ (c + 1))⁻¹ := by gcongr
      _ = (n : ℝ≥0∞)⁻¹ := by
        rw [pow_succ, ENNReal.mul_inv (.inl (pow_ne_zero c hn0)) (.inl hnt),
          ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero c hn0) hnt, one_mul]

/-- Polynomial characterization of negligibility (the classical textbook definition):
`f` is negligible iff it is eventually below `1 / p n` for every polynomial `p`. -/
theorem negligible_iff_forall_polynomial_eventually_le {f : ℕ → ℝ≥0∞} :
    negligible f ↔ ∀ p : Polynomial ℕ, ∀ᶠ n in atTop, f n ≤ (↑(p.eval n) : ℝ≥0∞)⁻¹ := by
  refine ⟨fun hf p => ?_,
    fun h => negligible_iff_forall_eventually_le_inv_pow.mpr fun c => ?_⟩
  · have h0 := negligible_polynomial_mul hf p 0
    simp only [pow_zero, one_mul] at h0
    filter_upwards [h0.eventually_lt_const zero_lt_one] with n hn
    exact ENNReal.le_inv_iff_mul_le.mpr (mul_comm (f n) _ ▸ hn.le)
  · filter_upwards [h (Polynomial.X ^ c)] with n hn
    simpa [Nat.cast_pow] using hn
