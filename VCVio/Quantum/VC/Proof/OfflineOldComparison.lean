/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldAssembly

/-!
# Outcome-sensitive comparison of the old offline checker

The comparison keeps a separate finishing instrument for each extraction outcome. All
square-root weights are extended nonnegative reals, and inputs may be subnormalized and
entangled with arbitrary finite reference registers.
-/

public section

open Matrix
open scoped ComplexOrder ENNReal Kronecker Matrix.Norms.L2Operator

namespace Quantum.MatrixMap

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- A completely positive trace-nonincreasing finishing map preserves the square-root triangle
inequality for two preceding Kraus operators. -/
theorem IsCP.finish_triangle {Φ : MatrixMap B C} (hΦ : Φ.IsCP) (hT : Φ.IsTNI)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) (K L : Matrix B A ℂ) :
    ENNReal.ofReal (Φ (conj (K + L) ρ)).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (Φ (conj K ρ)).trace.re ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (Φ (conj L ρ)).trace.re ^ (2⁻¹ : ℝ) := by
  classical
  obtain ⟨S, rfl, _⟩ := hΦ.exists_stinespring_of_isTNI hT
  simp only [LinearMap.comp_apply, trace_traceRight]
  simp only [← LinearMap.comp_apply, ← conj_mul]
  rw [Matrix.mul_add]
  exact ofReal_trace_conj_add_rpow_le hρ _ _

/-- Replacing preceding Kraus operators adds their difference before taking the final square.
The finishing map can depend on the measured classical outcome. -/
theorem finish_comparison {ι : Type*} (Φ : ι → MatrixMap B C)
    (hΦ : ∀ i, (Φ i).IsCP) (hT : ∀ i, (Φ i).IsTNI)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) (K L : ι → Matrix B A ℂ) :
    (∑' i, ENNReal.ofReal (Φ i (conj (K i) ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' i, ENNReal.ofReal (Φ i (conj (L i) ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        (∑' i, ENNReal.ofReal (conj (K i - L i) ρ).trace.re) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_tsum_le_of_le_add
  intro i
  have hh := (hΦ i).finish_triangle (hT i) hρ (L i) (K i - L i)
  rw [show L i + (K i - L i) = K i by abel] at hh
  apply hh.trans
  apply add_le_add le_rfl
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
    (hT i _ ((isCP_conj (K i - L i)).posSemidef hρ))) (by norm_num)

/-- A finishing branch that vanishes on a subspace is bounded by its action on the
complement. This retains coherent cross terms until the square-root triangle inequality. -/
theorem IsCP.finish_le_complement [DecidableEq A] {Φ : MatrixMap B C}
    (hΦ : Φ.IsCP) (hT : Φ.IsTNI) (K : Matrix B A ℂ) (G : Matrix A A ℂ)
    (hzero : Φ ∘ₗ conj (K * G) = 0) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (Φ (conj K ρ)).trace.re ≤
      ENNReal.ofReal (Φ (conj K (conj (1 - G) ρ))).trace.re := by
  have h := hΦ.finish_triangle hT hρ (K * (1 - G)) (K * G)
  have he : K * (1 - G) + K * G = K := by
    simp only [Matrix.mul_sub, Matrix.mul_one, sub_add_cancel]
  rw [he] at h
  have hz := LinearMap.congr_fun hzero ρ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), add_zero] at h
  rw [conj_mul, LinearMap.comp_apply] at h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2⁻¹)).mp h

/-- An outcome-dependent family of finishing branches supported on the bad subspace has total
weight bounded by the original bad-subspace weight. No post-check population bound is used. -/
theorem finish_sum_le_complement [DecidableEq A] {ι : Type*}
    (Φ : ι → MatrixMap B C) (hΦ : ∀ i, (Φ i).IsCP) (hT : ∀ i, (Φ i).IsTNI)
    (K : ι → Matrix B A ℂ) (hK : IsCPTNIFamily (fun i ↦ conj (K i)))
    (G : Matrix A A ℂ) (hzero : ∀ i, Φ i ∘ₗ conj (K i * G) = 0)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, ENNReal.ofReal (Φ i (conj (K i) ρ)).trace.re ≤
      ENNReal.ofReal (conj (1 - G) ρ).trace.re := by
  calc _ ≤ ∑' i, ENNReal.ofReal (Φ i (conj (K i) (conj (1 - G) ρ))).trace.re :=
          ENNReal.tsum_le_tsum fun i ↦ (hΦ i).finish_le_complement
            (hT i) (K i) G (hzero i) hρ
    _ ≤ ∑' i, ENNReal.ofReal (conj (K i) (conj (1 - G) ρ)).trace.re := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact ENNReal.ofReal_le_ofReal
        (hT i _ ((isCP_conj _).posSemidef ((isCP_conj _).posSemidef hρ)))
    _ ≤ _ := hK.tsum_ofReal_trace_re_le ((isCP_conj _).posSemidef hρ)

/-- A classical predicate followed by a label measurement is a trace-nonincreasing family. -/
theorem accepted_label_isCPTNIFamily [DecidableEq A] {ι : Type*}
    [DecidableEq ι] (p : A → Prop) [DecidablePred p] (β : A → ι) :
    IsCPTNIFamily (fun i ↦ conj (diagonal fun a ↦
      if p a ∧ β a = i then (1 : ℂ) else 0)) := by
  classical
  let K (i : ι) : Matrix A A ℂ := diagonal fun a ↦ if p a ∧ β a = i then 1 else 0
  refine ⟨fun _ ↦ isCP_conj _, fun s ρ hρ ↦ ?_⟩
  have hg : ∑ i ∈ s, (K i)ᴴ * K i =
      diagonal (fun a ↦ if p a ∧ β a ∈ s then (1 : ℂ) else 0) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp only [K, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal,
        diagonal_apply_eq]
      by_cases hp : p a <;> simp [hp]
    · simp [K, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal, hab]
  have ht : (1 - ∑ i ∈ s, (K i)ᴴ * K i).PosSemidef := by
    rw [hg, ← diagonal_one, diagonal_sub]
    apply PosSemidef.diagonal
    intro a
    by_cases hp : p a ∧ β a ∈ s <;> simp [hp]
  have hh := ht.trace_mul_re_nonneg hρ
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, ← trace_conj_apply] at hh
  exact sub_nonneg.mp hh

/-- Tensoring on the left with a reference identity does not increase the operator norm. -/
theorem norm_one_kronecker_le [DecidableEq A] [DecidableEq B] (M : Matrix A A ℂ) :
    ‖(1 : Matrix B B ℂ) ⊗ₖ M‖ ≤ ‖M‖ := by
  have he : (1 : Matrix B B ℂ) ⊗ₖ M = (M ⊗ₖ (1 : Matrix B B ℂ)).submatrix
      (Equiv.prodComm B A) (Equiv.prodComm B A) := by
    ext a b
    simp only [kroneckerMap_apply, submatrix_apply, Equiv.prodComm_apply]
    exact mul_comm _ _
  rw [he, l2_opNorm_submatrix_equiv]
  exact l2_opNorm_kronecker_one_le M

/-- Operator norm bounds for a family measured between two operators. The middle family's
trace bound is used once, so the estimate does not multiply by its number of outcomes. -/
theorem measured_sandwich_weight_le [DecidableEq A] {ι : Type*}
    (P : ι → Matrix A A ℂ) (hP : IsCPTNIFamily (fun i ↦ conj (P i)))
    (L R : Matrix A A ℂ) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (∑' i, ENNReal.ofReal (conj (L * P i * R) ρ).trace.re) ≤
      ENNReal.ofReal (‖L‖ ^ 2) * ENNReal.ofReal (conj R ρ).trace.re := by
  calc _ ≤ ∑' i, ENNReal.ofReal (‖L‖ ^ 2) *
      ENNReal.ofReal (conj (P i) (conj R ρ)).trace.re := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [Matrix.mul_assoc, conj_mul, LinearMap.comp_apply, conj_mul,
          LinearMap.comp_apply, ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (re_trace_conj_le L
          ((isCP_conj _).posSemidef ((isCP_conj _).posSemidef hρ)))
    _ = ENNReal.ofReal (‖L‖ ^ 2) *
        ∑' i, ENNReal.ofReal (conj (P i) (conj R ρ)).trace.re := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_right (hP.tsum_ofReal_trace_re_le ((isCP_conj _).posSemidef hρ)) _

/-- The two checker replacements are compared while every intermediate measurement outcome
is retained. Their amplitudes add, with the input trace retained for subsequent leaf sums. -/
theorem measured_two_batches_distance_le [DecidableEq A] {ι : Type*}
    (P : ι → Matrix A A ℂ) (hP : IsCPTNIFamily (fun i ↦ conj (P i)))
    (Qa Qb Pa Pb : Matrix A A ℂ) (hQb : ‖Qb‖ ≤ 1) (hPa : ‖Pa‖ ≤ 1)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (∑' i, ENNReal.ofReal (conj (Qb * P i * Qa - Pb * P i * Pa) ρ).trace.re) ^
        (2⁻¹ : ℝ) ≤
      (ENNReal.ofReal (‖Qa - Pa‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Qb - Pb‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  have htrace (M : Matrix A A ℂ) : ENNReal.ofReal (conj M ρ).trace.re ≤
      ENNReal.ofReal (‖M‖ ^ 2) * ENNReal.ofReal ρ.trace.re := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (re_trace_conj_le M hρ)
  have hsq {M : Matrix A A ℂ} (hM : ‖M‖ ≤ 1) : ENNReal.ofReal (‖M‖ ^ 2) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    nlinarith [norm_nonneg M]
  have htriangle := rpow_inv_two_tsum_le_of_le_add (t := fun i ↦
    ENNReal.ofReal (conj (Qb * P i * Qa - Pb * P i * Pa) ρ).trace.re)
    (a := fun i ↦ ENNReal.ofReal (conj (Qb * P i * (Qa - Pa)) ρ).trace.re)
    (b := fun i ↦ ENNReal.ofReal (conj ((Qb - Pb) * P i * Pa) ρ).trace.re) (fun i ↦ ?_)
  · apply htriangle.trans
    apply add_le_add <;> apply ENNReal.rpow_le_rpow _ (by norm_num)
    · exact (measured_sandwich_weight_le P hP Qb (Qa - Pa) hρ).trans
        ((mul_le_of_le_one_left (by positivity) (hsq hQb)).trans (htrace _))
    · exact (measured_sandwich_weight_le P hP (Qb - Pb) Pa hρ).trans
        (mul_le_mul_right ((htrace Pa).trans
          (mul_le_of_le_one_left (by positivity) (hsq hPa))) _)
  · have he : Qb * P i * Qa - Pb * P i * Pa =
        Qb * P i * (Qa - Pa) + (Qb - Pb) * P i * Pa := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [he]
    exact ofReal_trace_conj_add_rpow_le hρ _ _

/-- Two checker replacements across a coherent contraction add their operator errors.
The intermediate response register is retained, so the estimate precedes its measurement. -/
theorem two_batches_distance_le [DecidableEq A]
    (Qa Qb Pa Pb U : Matrix A A ℂ) (hQ : ‖Qb‖ ≤ 1) (hP : ‖Pa‖ ≤ 1) (hU : ‖U‖ ≤ 1) :
    ‖Qb * U * Qa - Pb * U * Pa‖ ≤ ‖Qa - Pa‖ + ‖Qb - Pb‖ := by
  have he : Qb * U * Qa - Pb * U * Pa =
      Qb * U * (Qa - Pa) + (Qb - Pb) * U * Pa := by
    simp only [mul_sub, sub_mul]
    abel
  rw [he]
  calc _ ≤ ‖Qb * U * (Qa - Pa)‖ + ‖(Qb - Pb) * U * Pa‖ := norm_add_le _ _
    _ ≤ (‖Qb‖ * ‖U‖) * ‖Qa - Pa‖ + (‖Qb - Pb‖ * ‖U‖) * ‖Pa‖ := by
      apply add_le_add
      · exact (l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
      · exact (l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * 1) * ‖Qa - Pa‖ + (‖Qb - Pb‖ * 1) * 1 := by gcongr
    _ = _ := by simp

end Quantum.MatrixMap
