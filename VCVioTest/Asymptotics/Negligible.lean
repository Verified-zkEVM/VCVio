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
