/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The second moment of a sub-Gaussian observable

A real observable whose moment generating function is at most `K exp(s² V / 2)` for every `s`
has second moment at most `V (1 + η)`, with the slack `η = K - 1 + (1 + K) √(K - 1)` vanishing
as `K → 1`.
-/

public section

namespace MeasureTheory

/-- `2 + y² ≤ exp y + exp (-y)`: `cosh y - 1 = 2 sinh² (y / 2)` and `|sinh x| ≥ |x|`. -/
private theorem two_add_sq_le_exp_add_exp (y : ℝ) :
    2 + y ^ 2 ≤ Real.exp y + Real.exp (-y) := by
  have hc : Real.exp y + Real.exp (-y) = 2 + 4 * Real.sinh (y / 2) ^ 2 := by
    have h1 := Real.cosh_two_mul (y / 2)
    have h2 := Real.cosh_sq (y / 2)
    rw [mul_div_cancel₀ y two_ne_zero, Real.cosh_eq] at h1
    linarith
  have hs : (y / 2) ^ 2 ≤ Real.sinh (y / 2) ^ 2 := by
    rcases le_total 0 (y / 2) with h | h
    · exact pow_le_pow_left₀ h (Real.self_le_sinh_iff.2 h) 2
    · have h' := Real.sinh_le_self_iff.2 h
      nlinarith
  rw [hc]
  nlinarith

/-- The real form of the second-moment bound: if `u² I + 2 ≤ 2K exp(u² V / 2)` for every
`u > 0`, then `I ≤ V (1 + (K - 1) + (1 + K) √(K - 1))`. -/
private theorem le_of_forall_sq_mul_add_two_le {I K V : ℝ} (hK : 1 ≤ K) (hV : 0 ≤ V)
    (h : ∀ u : ℝ, 0 < u → u ^ 2 * I + 2 ≤ 2 * K * Real.exp (u ^ 2 * V / 2)) :
    I ≤ V * (1 + (K - 1 + (1 + K) * Real.sqrt (K - 1))) := by
  set r := Real.sqrt (K - 1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = K - 1 := Real.sq_sqrt (by linarith)
  rcases hV.eq_or_lt with hV0 | hVpos
  · subst hV0
    rw [zero_mul]
    by_contra hI
    push Not at hI
    have hpos : 0 < 2 * K / I := div_pos (by linarith) hI
    have hu := h (Real.sqrt (2 * K / I)) (Real.sqrt_pos.2 hpos)
    rw [Real.sq_sqrt hpos.le, div_mul_cancel₀ _ hI.ne'] at hu
    simp only [mul_zero, zero_div, Real.exp_zero, mul_one] at hu
    linarith
  have key : ∀ v : ℝ, 0 < v → v ≤ 1 → I * v ≤ V * (K * (1 + v + v ^ 2) - 1) := by
    intro v hv hv1
    have hw : 0 < 2 * v / V := by positivity
    have hu := h (Real.sqrt (2 * v / V)) (Real.sqrt_pos.2 hw)
    rw [Real.sq_sqrt hw.le, show 2 * v / V * V / 2 = v by field_simp] at hu
    have he : Real.exp v ≤ 1 + v + v ^ 2 := by
      have := Real.abs_exp_sub_one_sub_id_le (x := v) (by rw [abs_of_pos hv]; exact hv1)
      linarith [le_abs_self (Real.exp v - 1 - v)]
    have h2 : 2 * v / V * I ≤ 2 * K * (1 + v + v ^ 2) - 2 := by
      nlinarith [mul_le_mul_of_nonneg_left he (by linarith : (0 : ℝ) ≤ 2 * K)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hVpos] at h2
    linarith
  rcases hr0.eq_or_lt with hr00 | hrpos
  · have hK1 : K = 1 := by nlinarith
    rw [← hr00, hK1]
    norm_num
    refine le_of_forall_sub_le fun ε hε => ?_
    set v := min 1 (ε / (2 * V)) with hv_def
    have hv : 0 < v := lt_min one_pos (by positivity)
    have hv1 : v ≤ 1 := min_le_left _ _
    have hvε : v ≤ ε / (2 * V) := min_le_right _ _
    have h1 := key v hv hv1
    rw [hK1] at h1
    have hIv : I ≤ V * (1 + v) := le_of_mul_le_mul_right (by nlinarith) hv
    have hVv : V * v ≤ ε / 2 := by
      calc V * v ≤ V * (ε / (2 * V)) := mul_le_mul_of_nonneg_left hvε hV
        _ = ε / 2 := by field_simp
    linarith
  rcases le_or_gt r 1 with hr1 | hr1
  · have h1 := key r hrpos hr1
    have e : V * (K * (1 + r + r ^ 2) - 1) = V * (1 + (K - 1 + (1 + K) * r)) * r := by
      linear_combination (-V) * hr2
    rw [e] at h1
    exact le_of_mul_le_mul_right h1 hrpos
  · have h1 := key 1 one_pos le_rfl
    have hK3 : 3 * K - 1 ≤ 1 + (K - 1 + (1 + K) * r) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hr1.le) (by nlinarith : (0 : ℝ) ≤ r ^ 2 - r + 1)]
    calc I ≤ V * (3 * K - 1) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hK3 hV

/-- **Second moment from a sub-Gaussian moment generating function**: if
`E exp(sX) ≤ K exp(s² V / 2)` for every `s`, with `K ≥ 1` and `V ≥ 0`, then
`E X² ≤ V (1 + (K - 1) + (1 + K) √(K - 1))`. -/
theorem lintegral_sq_le_of_mgf {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (X : α → ℝ) (hX : Measurable X) {K V : ℝ} (hK : 1 ≤ K)
    (hV : 0 ≤ V)
    (hmgf : ∀ s : ℝ, ∫⁻ a, ENNReal.ofReal (Real.exp (s * X a)) ∂μ ≤
      ENNReal.ofReal (K * Real.exp (s ^ 2 * V / 2))) :
    ∫⁻ a, ENNReal.ofReal (X a ^ 2) ∂μ ≤
      ENNReal.ofReal (V * (1 + (K - 1 + (1 + K) * Real.sqrt (K - 1)))) := by
  have hX2 : Measurable fun a => ENNReal.ofReal (X a ^ 2) :=
    ENNReal.measurable_ofReal.comp (hX.pow_const 2)
  have hexp : ∀ s : ℝ, Measurable fun a => ENNReal.ofReal (Real.exp (s * X a)) := fun s =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul s))
  have hK0 : 0 ≤ K := by linarith
  have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
  have hstep : ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (u ^ 2) * ∫⁻ a, ENNReal.ofReal (X a ^ 2) ∂μ + 2 ≤
        ENNReal.ofReal (2 * K * Real.exp (u ^ 2 * V / 2)) := by
    intro u hu
    calc _ = ∫⁻ a, (ENNReal.ofReal (u ^ 2 * X a ^ 2) + 2) ∂μ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            ← lintegral_const_mul _ hX2]
          congr 1
          exact lintegral_congr fun a => (ENNReal.ofReal_mul (sq_nonneg u)).symm
      _ ≤ ∫⁻ a, (ENNReal.ofReal (Real.exp (u * X a)) +
            ENNReal.ofReal (Real.exp (-u * X a))) ∂μ := lintegral_mono fun a => by
          have := two_add_sq_le_exp_add_exp (u * X a)
          rw [h2, ← ENNReal.ofReal_add (by positivity) (by norm_num),
            ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, neg_mul]
          exact ENNReal.ofReal_le_ofReal (by rw [mul_pow] at this; linarith)
      _ = _ + _ := lintegral_add_left (hexp u) _
      _ ≤ ENNReal.ofReal (K * Real.exp (u ^ 2 * V / 2)) +
            ENNReal.ofReal (K * Real.exp ((-u) ^ 2 * V / 2)) := add_le_add (hmgf u) (hmgf (-u))
      _ = _ := by
          rw [neg_sq, ← ENNReal.ofReal_add (mul_nonneg hK0 (Real.exp_pos _).le)
            (mul_nonneg hK0 (Real.exp_pos _).le)]
          congr 1
          ring
  set J := ∫⁻ a, ENNReal.ofReal (X a ^ 2) ∂μ
  have hJ : J ≠ ⊤ := by
    intro h
    have := hstep 1 one_pos
    rw [h] at this
    simp at this
  have hreal : ∀ u : ℝ, 0 < u → u ^ 2 * J.toReal + 2 ≤ 2 * K * Real.exp (u ^ 2 * V / 2) := by
    intro u hu
    have h := hstep u hu
    rw [← ENNReal.ofReal_toReal hJ, ← ENNReal.ofReal_mul (sq_nonneg u), h2,
      ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg u) ENNReal.toReal_nonneg) (by norm_num)] at h
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg zero_le_two hK0) (Real.exp_pos _).le)).1 h
  rw [← ENNReal.ofReal_toReal hJ]
  exact ENNReal.ofReal_le_ofReal (le_of_forall_sq_mul_add_two_le hK hV hreal)

end MeasureTheory
