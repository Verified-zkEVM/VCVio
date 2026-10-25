/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.MeanInequalities
public import VCVio.Quantum.MatrixMap
public import VCVio.Quantum.MatrixMap.OpNorm

/-!
# Norms of matrices and square roots of weights

Square-root hybrid bounds on quantum runs (ePrint 2025/2166, Lemma 5.7) rest on three analytic
facts, collected here so that they depend on Mathlib and `Quantum.MatrixMap` only.

* **The trace seminorm.** For a positive semidefinite `Y`, the map `X ↦ √(re tr (X Y Xᴴ))` on
  rectangular matrices is a seminorm: writing `Y = Bᴴ B`, it is the Frobenius norm of `X Bᴴ`.
  Its triangle inequality, in the `ℝ≥0∞` form used for weights of runs, is
  `Quantum.MatrixMap.ofReal_trace_conj_add_rpow_le`. In the pure-state language of the paper
  this is the triangle inequality `‖(X₁ + X₂) ψ‖ ≤ ‖X₁ ψ‖ + ‖X₂ ψ‖`.
* **The operator norm.** Mathlib's `ℓ²` operator norm on matrices (scoped to
  `Matrix.Norms.L2Operator`) controls Kraus maps: `Xᴴ X ≤ ‖X‖² • 1`, so
  `re tr (X Y Xᴴ) ≤ ‖X‖² re tr Y` for positive semidefinite `Y`
  (`Quantum.MatrixMap.re_trace_conj_le`). The identity and isometries have norm at most one
  (`Matrix.l2_opNorm_one_le`, `Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self`, in
  `VCVio.Quantum.MatrixMap.OpNorm`). The norm is invariant under isometries
  (`Quantum.MatrixMap.l2_opNorm_isometry_mul`, `Quantum.MatrixMap.l2_opNorm_mul_coisometry`),
  orthogonal projections have norm at most one (`Quantum.MatrixMap.l2_opNorm_le_one_of_proj`),
  and the deviation of a conjugate from the original is a commutator
  (`Quantum.MatrixMap.l2_opNorm_conj_sub_self`). An operator that sends the blocks of an
  orthogonal decomposition of its input into mutually orthogonal blocks of its output is
  controlled block by block (`Quantum.MatrixMap.re_trace_conj_le_sum_of_blocks`).
  Submultiplicativity is Mathlib's `Matrix.l2_opNorm_mul`.
* **Square roots of series.** The `ℓ²` Minkowski inequality for series in `ℝ≥0∞`, in the form
  that a recursion on a program tree consumes: if each term is controlled by a sum of square
  roots, so is the series (`Quantum.rpow_inv_two_tsum_le_of_le_add` and
  `Quantum.rpow_inv_two_tsum_le_of_le_add_tsum`). Index types are arbitrary: a series in `ℝ≥0∞`
  is the supremum of its finite partial sums.
-/

public section

open scoped ComplexOrder Kronecker ENNReal
open Matrix

namespace Quantum

/-! ## Square roots of series in `ℝ≥0∞` -/

section Minkowski

variable {K : Type*}

/-- Squaring undoes the square root in `ℝ≥0∞`. -/
theorem rpow_inv_two_rpow_two (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x :=
  ENNReal.rpow_inv_rpow two_ne_zero x

/-- Finite `ℓ²` Minkowski inequality for a sum of `n + 1` families over a finite set. -/
theorem rpow_inv_two_sum_add_sum_le (s : Finset K) (c : K → ℝ≥0∞) (d : ℕ → K → ℝ≥0∞) (n : ℕ) :
    (∑ k ∈ s, (c k + ∑ j ∈ Finset.range n, d j k) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) ≤
      (∑ k ∈ s, c k ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) +
        ∑ j ∈ Finset.range n, (∑ k ∈ s, d j k ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Finset.sum_range_succ, ← add_assoc]
    have h := ENNReal.Lp_add_le s (fun k ↦ c k + ∑ j ∈ Finset.range n, d j k) (d n)
      (p := 2) (by norm_num)
    rw [one_div] at h
    exact h.trans (add_le_add_left ih _)

/-- **`ℓ²` Minkowski inequality for two series.** If every term satisfies
`√(t k) ≤ √(a k) + √(b k)`, then `√(∑ t) ≤ √(∑ a) + √(∑ b)`. -/
theorem rpow_inv_two_tsum_le_of_le_add {t a b : K → ℝ≥0∞}
    (h : ∀ k, t k ^ (2⁻¹ : ℝ) ≤ a k ^ (2⁻¹ : ℝ) + b k ^ (2⁻¹ : ℝ)) :
    (∑' k, t k) ^ (2⁻¹ : ℝ) ≤ (∑' k, a k) ^ (2⁻¹ : ℝ) + (∑' k, b k) ^ (2⁻¹ : ℝ) := by
  rw [ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2), ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  rw [← ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)]
  have hab := ENNReal.Lp_add_le s (fun k ↦ a k ^ (2⁻¹ : ℝ)) (fun k ↦ b k ^ (2⁻¹ : ℝ))
    (p := 2) (by norm_num)
  simp only [rpow_inv_two_rpow_two, one_div] at hab
  calc (∑ k ∈ s, t k) ^ (2⁻¹ : ℝ)
      ≤ (∑ k ∈ s, (a k ^ (2⁻¹ : ℝ) + b k ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
        gcongr with k
        rw [← rpow_inv_two_rpow_two (t k)]
        gcongr
        exact h k
    _ ≤ (∑ k ∈ s, a k) ^ (2⁻¹ : ℝ) + (∑ k ∈ s, b k) ^ (2⁻¹ : ℝ) := hab
    _ ≤ (∑' k, a k) ^ (2⁻¹ : ℝ) + (∑' k, b k) ^ (2⁻¹ : ℝ) := by
        gcongr <;> exact ENNReal.sum_le_tsum s

/-- **`ℓ²` Minkowski inequality for countably many series.** If every term satisfies
`√(L k) ≤ √(t k) + ∑' j, √(m j k)`, then `√(∑ L) ≤ √(∑ t) + ∑' j, √(∑' k, m j k)`. -/
theorem rpow_inv_two_tsum_le_of_le_add_tsum {L t : K → ℝ≥0∞} {m : ℕ → K → ℝ≥0∞}
    (h : ∀ k, L k ^ (2⁻¹ : ℝ) ≤ t k ^ (2⁻¹ : ℝ) + ∑' j, m j k ^ (2⁻¹ : ℝ)) :
    (∑' k, L k) ^ (2⁻¹ : ℝ) ≤
      (∑' k, t k) ^ (2⁻¹ : ℝ) + ∑' j, (∑' k, m j k) ^ (2⁻¹ : ℝ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [ENNReal.rpow_inv_le_iff h2, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  let S : ℕ → K → ℝ≥0∞ := fun n k ↦ ∑ j ∈ Finset.range n, m j k ^ (2⁻¹ : ℝ)
  have hS : ∀ k, Monotone fun n ↦ S n k := fun k _ _ hnn ↦
    Finset.sum_le_sum_of_subset (Finset.range_mono hnn)
  have hL : ∀ k, L k ≤ ⨆ n, (t k ^ (2⁻¹ : ℝ) + S n k) ^ (2 : ℝ) := fun k ↦ by
    have hk := h k
    rw [ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup] at hk
    rw [← rpow_inv_two_rpow_two (L k)]
    calc (L k ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) ≤ (⨆ n, t k ^ (2⁻¹ : ℝ) + S n k) ^ (2 : ℝ) := by
          gcongr
      _ = ⨆ n, (t k ^ (2⁻¹ : ℝ) + S n k) ^ (2 : ℝ) := by
          simpa only [ENNReal.orderIsoRpow_apply] using
            (ENNReal.orderIsoRpow 2 h2).map_iSup fun n ↦ t k ^ (2⁻¹ : ℝ) + S n k
  calc ∑ k ∈ s, L k ≤ ∑ k ∈ s, ⨆ n, (t k ^ (2⁻¹ : ℝ) + S n k) ^ (2 : ℝ) :=
        Finset.sum_le_sum fun k _ ↦ hL k
    _ = ⨆ n, ∑ k ∈ s, (t k ^ (2⁻¹ : ℝ) + S n k) ^ (2 : ℝ) :=
        ENNReal.finsetSum_iSup_of_monotone fun k _ _ hnn ↦ by
          gcongr
          exact hS k hnn
    _ ≤ _ := iSup_le fun n ↦ by
        rw [← ENNReal.rpow_inv_le_iff h2]
        refine (rpow_inv_two_sum_add_sum_le s _ (fun j k ↦ m j k ^ (2⁻¹ : ℝ)) n).trans ?_
        simp only [rpow_inv_two_rpow_two]
        gcongr
        · exact ENNReal.sum_le_tsum s
        · refine (Finset.sum_le_sum fun j _ ↦ ?_).trans (ENNReal.sum_le_tsum _)
          gcongr
          exact ENNReal.sum_le_tsum s

end Minkowski

namespace MatrixMap

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-! ## The trace seminorm -/

/-- The trace of `M * Mᴴ` is the sum of the squared norms of the entries of `M`. -/
theorem re_trace_mul_conjTranspose (M : Matrix m n ℂ) :
    (M * Mᴴ).trace.re = ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    Real.rpow_two]

/-- **Triangle inequality for the trace seminorm.** For a positive semidefinite `Y`,
`√(re tr ((X₁ + X₂) Y (X₁ + X₂)ᴴ)) ≤ √(re tr (X₁ Y X₁ᴴ)) + √(re tr (X₂ Y X₂ᴴ))`. -/
theorem sqrt_re_trace_conj_add_le {Y : Matrix n n ℂ} (hY : Y.PosSemidef) (X₁ X₂ : Matrix m n ℂ) :
    √(conj (X₁ + X₂) Y).trace.re ≤ √(conj X₁ Y).trace.re + √(conj X₂ Y).trace.re := by
  classical
  open scoped MatrixOrder in
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  let : NormedAddCommGroup (Matrix m n ℂ) := Matrix.frobeniusNormedAddCommGroup
  have key : ∀ X : Matrix m n ℂ, √(conj X (star B * B)).trace.re = ‖X * Bᴴ‖ := fun X ↦ by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, conj_apply, star_eq_conjTranspose]
    have hX : X * (Bᴴ * B) * Xᴴ = X * Bᴴ * (X * Bᴴ)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hX, re_trace_mul_conjTranspose]
  rw [key, key, key, Matrix.add_mul]
  exact norm_add_le _ _

/-- The square root of `ENNReal.ofReal t` is `ENNReal.ofReal √t`. -/
theorem _root_.ENNReal.ofReal_rpow_inv_two (t : ℝ) :
    ENNReal.ofReal t ^ (2⁻¹ : ℝ) = ENNReal.ofReal √t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num), Real.sqrt_eq_rpow, one_div]
  · rw [ENNReal.ofReal_of_nonpos ht.le, Real.sqrt_eq_zero'.mpr ht.le, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-- **Triangle inequality for the trace seminorm**, in `ℝ≥0∞`. -/
theorem ofReal_trace_conj_add_rpow_le {Y : Matrix n n ℂ} (hY : Y.PosSemidef)
    (X₁ X₂ : Matrix m n ℂ) :
    ENNReal.ofReal (conj (X₁ + X₂) Y).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (conj X₁ Y).trace.re ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (conj X₂ Y).trace.re ^ (2⁻¹ : ℝ) := by
  simp only [ENNReal.ofReal_rpow_inv_two]
  rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (sqrt_re_trace_conj_add_le hY X₁ X₂)

/-- **Triangle inequality for the trace seminorm**, for a difference, in `ℝ≥0∞`. -/
theorem ofReal_trace_conj_sub_rpow_le {Y : Matrix n n ℂ} (hY : Y.PosSemidef)
    (X₁ X₂ : Matrix m n ℂ) :
    ENNReal.ofReal (conj (X₁ - X₂) Y).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (conj X₁ Y).trace.re ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (conj X₂ Y).trace.re ^ (2⁻¹ : ℝ) := by
  have h := ofReal_trace_conj_add_rpow_le hY X₁ (-X₂)
  have hneg : conj (-X₂) Y = conj X₂ Y := by
    simp only [conj_apply, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rwa [← sub_eq_add_neg, hneg] at h

/-! ## The operator norm -/

section L2Operator

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- **Operator-norm bound on `Xᴴ X`.** In the Loewner order, `Xᴴ X ≤ ‖X‖² • 1` for the `ℓ²`
operator norm. -/
theorem posSemidef_l2_opNorm_sq_smul_one_sub [DecidableEq n] (X : Matrix m n ℂ) :
    ((‖X‖ ^ 2) • (1 : Matrix n n ℂ) - Xᴴ * X).PosSemidef := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self (A := Matrix n n ℂ) (Xᴴ * X)
    (Matrix.isHermitian_conjTranspose_mul_self X)
  rwa [Matrix.le_iff, Matrix.l2_opNorm_conjTranspose_mul_self, Algebra.algebraMap_eq_smul_one,
    ← pow_two] at h

/-- **Operator-norm bound on a Kraus map.** On a positive semidefinite `Y`,
`re tr (X Y Xᴴ) ≤ ‖X‖² re tr Y`. -/
theorem re_trace_conj_le [DecidableEq n] (X : Matrix m n ℂ) {Y : Matrix n n ℂ}
    (hY : Y.PosSemidef) :
    (conj X Y).trace.re ≤ ‖X‖ ^ 2 * Y.trace.re := by
  classical
  have h := (posSemidef_l2_opNorm_sq_smul_one_sub X).trace_mul_re_nonneg hY
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at h
  rw [trace_conj_apply]
  linarith

/-- **Operator-norm bound on a finite Kraus family.** On a positive semidefinite `Y`,
`∑ r ∈ s, re tr (F r Y (F r)ᴴ) ≤ (∑ r ∈ s, ‖F r‖²) re tr Y`. -/
theorem sum_re_trace_conj_le [DecidableEq n] {ι : Type*} (s : Finset ι) (F : ι → Matrix m n ℂ)
    {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    ∑ r ∈ s, (conj (F r) Y).trace.re ≤ (∑ r ∈ s, ‖F r‖ ^ 2) * Y.trace.re := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun r _ ↦ re_trace_conj_le (F r) hY

/-- **Operator-norm bound block by block** (the blockwise estimate behind the coherent-index
masses of ePrint 2025/2166, §4.2 and Lemma 5.7). Let `B k` be idempotents on the input of `F`
that add up to the identity, let `B' k` be operators on its output with `(B' b)ᴴ B' a = 0` for
`a ≠ b`, and let `F` send the block `B k` into the block `B' k`: `B' k F B k = F B k`. Then on a
positive semidefinite `Y`, `re tr (F Y Fᴴ) ≤ ∑ₖ ‖F B k‖² re tr (B k Y (B k)ᴴ)`.

Orthogonal projections onto the values of a coherent index register, `|k⟩⟨k| ⊗ 1`, satisfy the
hypotheses with `B' = B`, and an operator `∑ₖ |k⟩⟨k| ⊗ Fₖ` that is block diagonal in the index
sends each block into itself. -/
theorem re_trace_conj_le_sum_of_blocks [DecidableEq n] {κ : Type*} [Fintype κ]
    (F : Matrix m n ℂ) {B : κ → Matrix n n ℂ} {B' : κ → Matrix m m ℂ} (hB : ∑ k, B k = 1)
    (hBB : ∀ k, B k * B k = B k) (hB' : ∀ a b, a ≠ b → (B' b)ᴴ * B' a = 0)
    (hF : ∀ k, B' k * F * B k = F * B k) {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    (conj F Y).trace.re ≤ ∑ k, ‖F * B k‖ ^ 2 * (conj (B k) Y).trace.re := by
  classical
  have hG : ∀ k, F * B k = B' k * (F * B k) := fun k ↦ by rw [← Matrix.mul_assoc, hF k]
  have hsum : F = ∑ k, F * B k := by rw [← Matrix.mul_sum, hB, Matrix.mul_one]
  have hcross : ∀ a b, a ≠ b → (F * B a * Y * (F * B b)ᴴ).trace = 0 := by
    intro a b hab
    have e : (F * B a * Y * (F * B b)ᴴ).trace =
        (B' a * ((F * B a) * (Y * ((F * B b)ᴴ * (B' b)ᴴ)))).trace := by
      conv_lhs => rw [hG a, hG b]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, hB' a b hab, Matrix.mul_zero, Matrix.trace_zero]
  have hdiag : ∀ a, (conj (F * B a) Y).trace.re ≤ ‖F * B a‖ ^ 2 * (conj (B a) Y).trace.re := by
    intro a
    have e : conj (F * B a) (conj (B a) Y) = conj (F * B a) Y := by
      rw [← LinearMap.comp_apply (conj (F * B a)), ← conj_mul, Matrix.mul_assoc, hBB]
    rw [← e]
    exact re_trace_conj_le _ (hY.mul_mul_conjTranspose_same _)
  have htr : (conj F Y).trace = ∑ a, (conj (F * B a) Y).trace := by
    conv_lhs => rw [hsum]
    simp only [conj_apply, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_eq_single a (fun b _ hba ↦ hcross b a hba) (by simp)]
  rw [htr, Complex.re_sum]
  exact Finset.sum_le_sum fun a _ ↦ hdiag a

/-- **Operator-norm bound block by block**, in `ℝ≥0∞`. -/
theorem ofReal_trace_conj_le_sum_of_blocks [DecidableEq n] {κ : Type*} [Fintype κ]
    (F : Matrix m n ℂ) {B : κ → Matrix n n ℂ} {B' : κ → Matrix m m ℂ} (hB : ∑ k, B k = 1)
    (hBB : ∀ k, B k * B k = B k) (hB' : ∀ a b, a ≠ b → (B' b)ᴴ * B' a = 0)
    (hF : ∀ k, B' k * F * B k = F * B k) {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    ENNReal.ofReal (conj F Y).trace.re ≤
      ∑ k, ENNReal.ofReal (‖F * B k‖ ^ 2) * ENNReal.ofReal (conj (B k) Y).trace.re := by
  refine (ENNReal.ofReal_le_ofReal
    (re_trace_conj_le_sum_of_blocks F hB hBB hB' hF hY)).trans_eq ?_
  have hnn : ∀ k, 0 ≤ (conj (B k) Y).trace.re := fun k ↦
    (hY.mul_mul_conjTranspose_same (B k)).trace_re_nonneg
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ ↦ mul_nonneg (sq_nonneg _) (hnn k)]
  exact Finset.sum_congr rfl fun k _ ↦ ENNReal.ofReal_mul (sq_nonneg _)

/-- An orthogonal projection has operator norm at most one. -/
theorem l2_opNorm_le_one_of_proj [DecidableEq n] {P : Matrix n n ℂ} (hP : Pᴴ = P)
    (hPP : P * P = P) :
    ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP, hPP] at h
  nlinarith [norm_nonneg P]

/-- **Unitary invariance, on the left.** Multiplying by an isometry on the left preserves the
operator norm. -/
theorem l2_opNorm_isometry_mul [DecidableEq m] [DecidableEq n] {U : Matrix l m ℂ}
    (hU : Uᴴ * U = 1) (X : Matrix m n ℂ) : ‖U * X‖ = ‖X‖ := by
  classical
  refine le_antisymm ?_ ?_
  · calc ‖U * X‖ ≤ ‖U‖ * ‖X‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖X‖ := by gcongr; exact Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self hU
      _ = ‖X‖ := one_mul _
  · calc ‖X‖ = ‖Uᴴ * (U * X)‖ := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
      _ ≤ ‖Uᴴ‖ * ‖U * X‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖U * X‖ := by
          gcongr
          rw [Matrix.l2_opNorm_conjTranspose]
          exact Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self hU
      _ = ‖U * X‖ := one_mul _

/-- **Unitary invariance, on the right.** Multiplying by a coisometry on the right preserves the
operator norm. -/
theorem l2_opNorm_mul_coisometry [DecidableEq n] [DecidableEq l] {V : Matrix n l ℂ}
    (hV : V * Vᴴ = 1) (X : Matrix m n ℂ) : ‖X * V‖ = ‖X‖ := by
  classical
  rw [← Matrix.l2_opNorm_conjTranspose (X * V), Matrix.conjTranspose_mul,
    l2_opNorm_isometry_mul (by rwa [Matrix.conjTranspose_conjTranspose]),
    Matrix.l2_opNorm_conjTranspose]

/-- **Conjugation and commutators.** For a unitary `V`, the deviation of the conjugate
`W X Vᴴ` from `X` has the operator norm of `W X - X V`. With `W = V` this is the norm of the
commutator `[X, V]`. -/
theorem l2_opNorm_conj_sub_self [DecidableEq n] (W : Matrix m m ℂ) {V : Matrix n n ℂ}
    (hV : Vᴴ * V = 1) (X : Matrix m n ℂ) :
    ‖W * X * Vᴴ - X‖ = ‖W * X - X * V‖ := by
  have hV' : V * Vᴴ = 1 := _root_.mul_eq_one_comm.mp hV
  have h : W * X * Vᴴ - X = (W * X - X * V) * Vᴴ := by
    rw [Matrix.sub_mul, Matrix.mul_assoc X V, hV', Matrix.mul_one]
  rw [h, l2_opNorm_mul_coisometry (by rwa [Matrix.conjTranspose_conjTranspose])]

end L2Operator

end MatrixMap

end Quantum
