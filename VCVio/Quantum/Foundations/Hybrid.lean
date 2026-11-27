/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import QuantumFoundations.MatrixMap.Norm

/-!
# Square-root estimates for hybrid bounds

Cauchy–Schwarz bounds the sum of square roots of a sequence supported below a finite cutoff.
Combined with the square-root Minkowski inequality, it aggregates families of challenge-indexed
hybrid estimates before charging their common cutoff. The weights may be extended nonnegative
reals, and no separate summability hypotheses are required.
-/

public section

open scoped ENNReal

namespace Quantum

/-- Aggregate pointwise square-root comparisons with arbitrary nonnegative extended-real
weights. The weights need not sum to one, and no summability assumption is required. -/
theorem rpow_inv_two_tsum_mul_le_of_le_add {Ω : Type*} (w p a e : Ω → ℝ≥0∞)
    (h : ∀ ω, p ω ^ (2⁻¹ : ℝ) ≤ a ω ^ (2⁻¹ : ℝ) + e ω ^ (2⁻¹ : ℝ)) :
    (∑' ω, w ω * p ω) ^ (2⁻¹ : ℝ) ≤
      (∑' ω, w ω * a ω) ^ (2⁻¹ : ℝ) + (∑' ω, w ω * e ω) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_tsum_le_of_le_add
  intro ω
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  rw [← mul_add]
  exact mul_le_mul le_rfl (h ω) bot_le bot_le

/-- Cauchy–Schwarz for the square roots of a sequence supported below a finite cutoff. -/
theorem tsum_rpow_inv_two_le_of_cutoff (f : ℕ → ℝ≥0∞) (n : ℕ)
    (hcut : ∀ j, n ≤ j → f j = 0) :
    ∑' j, f j ^ (2⁻¹ : ℝ) ≤ ((n : ℝ≥0∞) * ∑' j, f j) ^ (2⁻¹ : ℝ) := by
  have hz : ∀ j ∉ Finset.range n, f j ^ (2⁻¹ : ℝ) = 0 :=
    fun j hj ↦ by
      rw [hcut j (by simpa using hj), ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz, ENNReal.le_rpow_inv_iff (by norm_num)]
  calc (∑ j ∈ Finset.range n, f j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
      ≤ ((Finset.range n).card : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ∑ j ∈ Finset.range n, (f j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ (by norm_num)
    _ = (n : ℝ≥0∞) * ∑ j ∈ Finset.range n, f j := by
        simp only [Finset.card_range, rpow_inv_two_rpow_two]
        norm_num
    _ ≤ _ := by
        gcongr
        exact sum_le_tsum _

/-- Aggregate square-root hybrid bounds over a family of challenges before applying
Cauchy–Schwarz to their common call cutoff. No finiteness assumption on the challenge type
or summability assumption on the weights is needed. -/
theorem rpow_inv_two_tsum_le_of_le_add_tsum_of_cutoff {Y : Type*}
    (p a : Y → ℝ≥0∞) (m : ℕ → Y → ℝ≥0∞) (n : ℕ)
    (hcut : ∀ j, n ≤ j → ∀ y, m j y = 0)
    (h : ∀ y, p y ^ (2⁻¹ : ℝ) ≤ a y ^ (2⁻¹ : ℝ) +
      ∑' j, m j y ^ (2⁻¹ : ℝ)) :
    (∑' y, p y) ^ (2⁻¹ : ℝ) ≤ (∑' y, a y) ^ (2⁻¹ : ℝ) +
      ((n : ℝ≥0∞) * ∑' j, ∑' y, m j y) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_tsum_le_of_le_add_tsum h).trans (add_le_add le_rfl ?_)
  exact tsum_rpow_inv_two_le_of_cutoff _ n fun j hj ↦ by simp [hcut j hj]

/-- The uniform average of square roots is at most the square root of the uniform
average. Values may be infinite; the finite averaging space is nonempty. -/
theorem average_rpow_inv_two_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ≥0∞) :
    (Fintype.card Ω : ℝ≥0∞)⁻¹ * ∑ ω, f ω ^ (2⁻¹ : ℝ) ≤
      ((Fintype.card Ω : ℝ≥0∞)⁻¹ * ∑ ω, f ω) ^ (2⁻¹ : ℝ) := by
  have hn0 : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hnt : (Fintype.card Ω : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : (∑ ω, f ω ^ (2⁻¹ : ℝ)) ^ (2 : ℕ) ≤
      (Fintype.card Ω : ℝ≥0∞) * ∑ ω, f ω := by
    have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset Ω)
      (fun ω ↦ f ω ^ (2⁻¹ : ℝ)) (show (1 : ℝ) ≤ 2 by norm_num)
    simp only [rpow_inv_two_rpow_two] at h
    simpa only [ENNReal.rpow_two, Finset.card_univ,
      show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] using h
  rw [ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two, mul_pow]
  calc
    _ ≤ (Fintype.card Ω : ℝ≥0∞)⁻¹ ^ (2 : ℕ) *
        ((Fintype.card Ω : ℝ≥0∞) * ∑ ω, f ω) := mul_le_mul le_rfl hsum bot_le bot_le
    _ = ((Fintype.card Ω : ℝ≥0∞)⁻¹ * (Fintype.card Ω : ℝ≥0∞)) *
        ((Fintype.card Ω : ℝ≥0∞)⁻¹ * ∑ ω, f ω) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hn0 hnt, one_mul]

/-- For event weights at most one, an additive square-root error gives at most twice
that error in the event probability. The error itself may be infinite. -/
theorem le_add_two_mul_of_rpow_inv_two_le {p a e : ℝ≥0∞} (hp : p ≤ 1) (ha : a ≤ 1)
    (h : p ^ (2⁻¹ : ℝ) ≤ a ^ (2⁻¹ : ℝ) + e) : p ≤ a + 2 * e := by
  by_cases he : e = ⊤
  · simp [he]
  have hp' : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have ht : a + 2 * e ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha', ENNReal.mul_ne_top (by norm_num) he⟩
  apply (ENNReal.toReal_le_toReal hp' ht).mp
  rw [ENNReal.toReal_add ha' (ENNReal.mul_ne_top (by norm_num) he), ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofNat]
  have hr := (ENNReal.toReal_le_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hp')
    (ENNReal.add_ne_top.mpr ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) ha', he⟩)).mpr h
  rw [ENNReal.toReal_add (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ha') he,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hr
  have hsqrt (z : ℝ) : z ^ (2⁻¹ : ℝ) = Real.sqrt z := by
    simpa only [one_div] using (Real.sqrt_eq_rpow z).symm
  rw [hsqrt, hsqrt] at hr
  have hpp : p.toReal ≤ 1 := by simpa using (ENNReal.toReal_le_toReal hp' ENNReal.one_ne_top).mpr hp
  have haa : a.toReal ≤ 1 := by simpa using (ENNReal.toReal_le_toReal ha' ENNReal.one_ne_top).mpr ha
  have hsp : Real.sqrt p.toReal ≤ 1 := (Real.sqrt_le_one).mpr hpp
  have hsa : Real.sqrt a.toReal ≤ 1 := (Real.sqrt_le_one).mpr haa
  have hps := Real.sq_sqrt (ENNReal.toReal_nonneg (a := p))
  have has := Real.sq_sqrt (ENNReal.toReal_nonneg (a := a))
  by_cases hpa : p.toReal ≤ a.toReal
  · exact hpa.trans (le_add_of_nonneg_right (by positivity))
  · have hsap : Real.sqrt a.toReal ≤ Real.sqrt p.toReal := Real.sqrt_le_sqrt (by linarith)
    have hm := mul_le_mul (show Real.sqrt p.toReal - Real.sqrt a.toReal ≤ e.toReal by linarith)
      (show Real.sqrt p.toReal + Real.sqrt a.toReal ≤ 2 by linarith)
      (by positivity : 0 ≤ Real.sqrt p.toReal + Real.sqrt a.toReal)
      (ENNReal.toReal_nonneg (a := e))
    nlinarith

end Quantum
