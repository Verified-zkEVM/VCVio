/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.CryptoFoundations.Asymptotics.Negligible
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Negligible-function bridge canaries

Checks that `negligible` connects to Mathlib's real-valued `SuperpolynomialDecay`: a concrete
geometric family is shown negligible from Mathlib's `tendsto_pow_const_mul_const_pow_of_lt_one`,
its little-`o` form is read off the bridge, and eventual domination suffices.

The closure lemmas are checked at their edges. A constant is negligible only at `0`, however
small it is otherwise. A list sum may repeat an entry, and one entry that is not negligible makes
the sum not negligible. Geometric decay needs a ratio below `1`, and `2 ^ (-c n)` a positive `c`:
at ratio `1`, or at `c = 0`, the family is the constant `1`.
-/

public section

open ENNReal Asymptotics Filter

namespace VCVioTest.Negligible

/-- `(1/2)^n` decays superpolynomially in `ℝ`, by Mathlib. -/
theorem superpolynomialDecay_half_pow :
    SuperpolynomialDecay atTop (Nat.cast : ℕ → ℝ) fun n => (1 / 2 : ℝ) ^ n := fun k =>
  tendsto_pow_const_mul_const_pow_of_lt_one k (by norm_num) (by norm_num)

example : negligible fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
  (negligible_ofReal_iff fun n => by positivity).2 superpolynomialDecay_half_pow

example : ∀ z : ℤ, (fun n : ℕ => (ENNReal.ofReal ((1 / 2 : ℝ) ^ n)).toReal) =o[atTop]
    fun n : ℕ => (n : ℝ) ^ z :=
  (negligible_iff_isLittleO_toReal fun _ => ENNReal.ofReal_ne_top).1 <|
    (negligible_ofReal_iff fun n => by positivity).2 superpolynomialDecay_half_pow

example {f g : ℕ → ℝ≥0∞} (hg : negligible g) (h : ∀ n ≥ 5, f n ≤ g n) : negligible f :=
  negligible_of_eventuallyLE (Filter.eventually_atTop.2 ⟨5, h⟩) hg

example : negligible fun _ : ℕ => (0 : ℝ≥0∞) := negligible_const_iff.2 rfl

example : ¬ negligible fun _ : ℕ => ((2 : ℝ≥0∞) ^ 100)⁻¹ := fun h =>
  ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ofNat_ne_top) (negligible_const_iff.1 h)

example : ¬ negligible fun _ : ℕ => (1 : ℝ≥0∞) := not_negligible_one

example : negligible fun n =>
    ([fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n, fun n => (2⁻¹ : ℝ≥0∞) ^ n].map fun f => f n).sum :=
  negligible_list_sum (by simpa using negligible_pow_of_lt_one (ENNReal.inv_lt_one.2 one_lt_two))

example : ¬ negligible fun n =>
    ([fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n, fun _ => 1].map fun f => f n).sum := fun h =>
  not_negligible_one (negligible_of_le (fun n => by simp) h)

example : negligible fun n => (2⁻¹ : ℝ≥0∞) ^ n :=
  negligible_pow_of_lt_one (ENNReal.inv_lt_one.2 one_lt_two)

example : ¬ negligible fun n => (1 : ℝ≥0∞) ^ n := by
  simpa using not_negligible_one

example : negligible fun n : ℕ => (2 : ℝ≥0∞) ^ (-((1 / 2 : ℝ) * n)) :=
  negligible_two_rpow_neg_mul (by norm_num)

example : ¬ negligible fun n : ℕ => (2 : ℝ≥0∞) ^ (-((0 : ℝ) * n)) := by
  simpa using not_negligible_one

/-- Infinity at the first parameter does not affect decay. -/
example : negligible (fun n : ℕ => if n = 0 then ⊤ else 0) := by
  apply (negligible_iff_eventually_ne_top_and_toNNReal _).mpr
  refine ⟨(eventually_ge_atTop 1).mono fun n hn => ?_, ?_⟩
  · simp [Nat.ne_of_gt hn]
  · simpa only [apply_ite ENNReal.toNNReal, ENNReal.toNNReal_top, ENNReal.toNNReal_zero, ite_self]
      using Cslib.Crypto.negligible_zero

/-- Projecting a constantly infinite loss to zero loses the finiteness requirement. -/
example : ¬ negligible (fun _ : ℕ => ⊤) := by
  intro h
  obtain ⟨_, hn⟩ := ((negligible_iff_eventually_ne_top_and_toNNReal _).mp h).1.exists
  exact hn rfl

end VCVioTest.Negligible
