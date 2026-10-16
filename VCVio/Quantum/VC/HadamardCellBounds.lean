/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Hadamard
public import VCVio.Quantum.MatrixMap.Completion

/-!
# Cell residual estimates for empty-sector extensions

The residual-row identity in equation (13) of the repair note uses involutive translations.
The answer-group hypothesis is explicit wherever that identity is used. The entry formulas
are valid over every finite additive answer group and for arbitrary empty-sector matrices.
-/

public section

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Quantum

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A compressed cell entry is a sum over the decompressed cell label only. -/
theorem compressedCell_apply (W : Matrix Y Y ℂ) (r s : Y) (a b : Option Y) :
    compressedCell W (r, a) (s, b) =
      ∑ c, cellCompress Y a c * emptyExtensionBlock W c r s * cellCompress Y c b := by
  simp only [compressedCell, Matrix.mul_apply, Fintype.sum_prod_type,
    kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    decompressedCell, blockDiagonal_apply, Finset.sum_mul]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- The response average of all translations has every entry equal to one. -/
theorem sum_xorShift_apply (r s : Y) : ∑ y, xorShift Y y r s = 1 := by
  simp only [xorShift_apply]
  have h : ∀ y, r = s + y ↔ y = r - s := fun y ↦ by
    constructor
    · intro h; rw [h]; abel
    · intro h; rw [h]; abel
  simp_rw [h]
  simp

/-- The filled-to-filled entry formula before imposing any involution hypothesis. -/
theorem compressedCell_some_some (W : Matrix Y Y ℂ) (r s y z : Y) :
    compressedCell W (r, some y) (s, some z) =
      (if y = z then xorShift Y y r s else 0) -
        (Fintype.card Y : ℂ)⁻¹ * (xorShift Y y r s + xorShift Y z r s) +
        (Fintype.card Y : ℂ)⁻¹ ^ 2 + (Fintype.card Y : ℂ)⁻¹ * W r s := by
  rw [compressedCell_apply, Fintype.sum_option]
  simp only [cellCompress_some_none, cellCompress_none_some, emptyExtensionBlock,
    cellCompress_some_some]
  have hm : cellAmp Y * W r s * cellAmp Y = (Fintype.card Y : ℂ)⁻¹ * W r s := by
    rw [mul_right_comm, cellAmp_mul_self]
  rw [hm]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite,
    one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.sum_mul, ← Finset.mul_sum, sum_xorShift_apply]
  by_cases h : y = z
  · subst z; simp only [ite_true]; ring
  · simp only [h, ite_false]; ring

/-- A compressed cell has a Hermitian matrix when its unitary blocks are involutions. -/
theorem conjTranspose_compressedCell (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1) :
    (compressedCell W)ᴴ = compressedCell W := by
  have hu := mem_unitaryGroup_iff'.mp (compressedCell_mem_unitaryGroup hW)
  rw [star_eq_conjTranspose] at hu
  calc
    _ = (compressedCell W)ᴴ * (compressedCell W * compressedCell W) := by
      rw [compressedCell_mul_self hY hWW, Matrix.mul_one]
    _ = compressedCell W := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

end Quantum

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]


/-- The algebraic residual identity underlying equation (13) of the repair note.
The assumptions record precisely the involutions and commuting factors used in the identity. -/
theorem emptyExtension_residual_identity (D K W P : Matrix n n ℂ) (a : ℂ)
    (hD : D * D = 1) (hW : W * W = 1) (hK : K * K = K)
    (hKW : K * W = W * K) (hKP : K * P = P * K)
    (hDP : D * P = P) (hPD : P * D = P) :
    2 • (1 : Matrix n n ℂ) -
        (D - a • (K * D + D * K) + a • (K * (W + P))) * D -
        D * (D - a • (K * D + D * K) + a • (K * (W + P))) =
      a • (K + D * K * D + (D * K - W * K) * (K * D - K * W) - 2 • (K * P)) := by
  have hWK : W * K * W = K := by
    rw [← hKW, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hDKP : D * K * P = K * P := by
    rw [Matrix.mul_assoc, hKP, ← Matrix.mul_assoc, hDP, ← hKP]
  simp only [add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
    Matrix.mul_assoc, hD, Matrix.mul_one]
  simp only [← Matrix.mul_assoc, hWK, hDKP, hK, hPD, hD, Matrix.one_mul]
  rw [← hKW]
  module

/-- The residual-row estimate of the repair note from its algebraic identity. The three
contractions are the filled translation, the bad-cell projection, and the empty response.
Positivity of `K * P` is the only property of the uniform-response projection needed here. -/
theorem emptyExtension_residual_norm_sq_le {m : Type*} [Fintype m] [DecidableEq m]
    (R : Matrix n m ℂ) (D K W P : Matrix n n ℂ) {a : ℝ}
    (ha : 0 ≤ a) (hD : ‖D‖ ≤ 1) (hK : ‖K‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (hDs : Dᴴ = D) (hKs : Kᴴ = K) (hWs : Wᴴ = W)
    (hKP : (K * P).PosSemidef)
    (hR : R * Rᴴ = (a : ℂ) •
      (K + D * K * D + (D * K - W * K) * (K * D - K * W) - 2 • (K * P))) :
    ‖R‖ ^ 2 ≤ 6 * a := by
  let T := D * K - W * K
  let A := K + D * K * D + T * Tᴴ
  have hT : ‖T‖ ≤ 2 := by
    calc
      ‖T‖ ≤ ‖D * K‖ + ‖W * K‖ := norm_sub_le _ _
      _ ≤ ‖D‖ * ‖K‖ + ‖W‖ * ‖K‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num
  have hA : ‖A‖ ≤ 6 := by
    calc
      ‖A‖ ≤ ‖K‖ + ‖D * K * D‖ + ‖T * Tᴴ‖ := norm_add₃_le
      _ ≤ ‖K‖ + ‖D‖ * ‖K‖ * ‖D‖ + ‖T‖ * ‖T‖ := by
        gcongr
        · exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        · rw [← star_eq_conjTranspose, CStarRing.norm_self_mul_star]
      _ ≤ 1 + 1 * 1 * 1 + 2 * 2 := by gcongr
      _ = 6 := by norm_num
  have hle : R * Rᴴ ≤ (a : ℂ) • A := by
    rw [hR, Matrix.le_iff]
    have he : (a : ℂ) • A - (a : ℂ) •
        (K + D * K * D + (D * K - W * K) * (K * D - K * W) - 2 • (K * P)) =
        (2 * (a : ℂ)) • (K * P) := by
      simp only [A, T, conjTranspose_sub, conjTranspose_mul, hDs, hKs, hWs]
      module
    rw [he]
    exact hKP.smul (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha))
  calc
    ‖R‖ ^ 2 = ‖R * Rᴴ‖ := by
      simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose, pow_two] using
        (l2_opNorm_conjTranspose_mul_self Rᴴ).symm
    _ ≤ ‖(a : ℂ) • A‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
      (Matrix.posSemidef_self_mul_conjTranspose R).nonneg
    _ = a * ‖A‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a * 6 := mul_le_mul_of_nonneg_left hA ha
    _ = 6 * a := mul_comm _ _

end Matrix
