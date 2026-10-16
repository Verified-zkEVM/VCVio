/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardCellBounds

/-!
# Filled-cell residual rows

The singleton specialization of the repair note's equation (13) bounds a whole response row
block by `6 / |Y|`. The response register remains an operator block throughout this estimate.
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Quantum

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The response projector onto the positive uniform vector. -/
@[expose]
noncomputable def uniformResponseProjector : Matrix Y Y ℂ :=
  fun _ _ ↦ (Fintype.card Y : ℂ)⁻¹

omit [DecidableEq Y] [AddCommGroup Y] in
/-- The uniform-response matrix is positive semidefinite. -/
theorem uniformResponseProjector_posSemidef :
    (uniformResponseProjector (Y := Y)).PosSemidef := by
  have he : uniformResponseProjector (Y := Y) =
      vecMulVec (fun _ : Y ↦ cellAmp Y) (star fun _ : Y ↦ cellAmp Y) := by
    ext r s
    simp [uniformResponseProjector, vecMulVec_apply, cellAmp_mul_self]
  rw [he]
  exact posSemidef_vecMulVec_self_star _

/-- Translations fix the uniform-response projector on the left. -/
theorem xorShift_mul_uniformResponseProjector (y : Y) :
    xorShift Y y * uniformResponseProjector = uniformResponseProjector := by
  ext r s
  have he : ∀ x, r = x + y ↔ x = r - y := fun x ↦ by
    constructor
    · intro h; rw [h]; abel
    · intro h; rw [h]; abel
  simp [Matrix.mul_apply, xorShift_apply, uniformResponseProjector, he]

/-- Translations fix the uniform-response projector on the right. -/
theorem uniformResponseProjector_mul_xorShift (y : Y) :
    uniformResponseProjector * xorShift Y y = uniformResponseProjector := by
  ext r s
  simp [Matrix.mul_apply, xorShift_apply, uniformResponseProjector]

/-- The diagonal filled-cell block has the form used in the residual identity. -/
theorem submatrix_compressedCell_filled (W : Matrix Y Y ℂ) (y : Y) :
    (compressedCell W).submatrix (fun r ↦ (r, some y)) (fun s ↦ (s, some y)) =
      xorShift Y y - (Fintype.card Y : ℂ)⁻¹ • (xorShift Y y + xorShift Y y) +
        (Fintype.card Y : ℂ)⁻¹ • (W + uniformResponseProjector) := by
  ext r s
  simp only [submatrix_apply, compressedCell_some_some, ite_true, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, uniformResponseProjector]
  ring

omit [Fintype Y] in
/-- The translation at a filled cell is Hermitian for exponent-two answers. -/
theorem conjTranspose_xorShift_of_add_self (hY : ∀ y : Y, y + y = 0) (y : Y) :
    (xorShift Y y)ᴴ = xorShift Y y := by
  ext r s
  have he : s = r + y ↔ r = s + y := by
    constructor
    · intro h; rw [h, add_assoc, hY, add_zero]
    · intro h; rw [h, add_assoc, hY, add_zero]
  simp [conjTranspose_apply, xorShift_apply, he]

omit [Fintype Y] in
/-- The decompressed cell is Hermitian when each response block is an involution. -/
theorem conjTranspose_decompressedCell (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : Wᴴ = W) : (decompressedCell W)ᴴ = decompressedCell W := by
  rw [decompressedCell, blockDiagonal_conjTranspose]
  congr 1
  funext c
  cases c with
  | none => exact hW
  | some y => exact conjTranspose_xorShift_of_add_self hY y

/-- Multiplication by a decompressed cell restricts to right multiplication by its filled
response block. -/
theorem submatrix_mul_decompressedCell (A : Matrix (Y × Option Y) (Y × Option Y) ℂ)
    (W : Matrix Y Y ℂ) (y : Y) :
    (A * decompressedCell W).submatrix (fun r ↦ (r, some y)) (fun s ↦ (s, some y)) =
      A.submatrix (fun r ↦ (r, some y)) (fun s ↦ (s, some y)) * xorShift Y y := by
  ext r s
  simp [Matrix.mul_apply, Fintype.sum_prod_type, decompressedCell, blockDiagonal_apply,
    emptyExtensionBlock]

/-- Multiplication on the left restricts to left multiplication by the filled response block. -/
theorem submatrix_decompressedCell_mul (A : Matrix (Y × Option Y) (Y × Option Y) ℂ)
    (W : Matrix Y Y ℂ) (y : Y) :
    (decompressedCell W * A).submatrix (fun r ↦ (r, some y)) (fun s ↦ (s, some y)) =
      xorShift Y y * A.submatrix (fun r ↦ (r, some y)) (fun s ↦ (s, some y)) := by
  ext r s
  simp [Matrix.mul_apply, Fintype.sum_prod_type, decompressedCell, blockDiagonal_apply,
    emptyExtensionBlock]

/-- The Gram matrix of a filled residual row, before expanding the filled response block. -/
theorem compressedCell_residual_row_gram (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1) (y : Y) :
    let R := (compressedCell W - decompressedCell W).submatrix (fun r ↦ (r, some y)) id
    let C := (compressedCell W).submatrix (fun r ↦ (r, some y)) (fun s ↦ (s, some y))
    R * Rᴴ = 2 • (1 : Matrix Y Y ℂ) - C * xorShift Y y - xorShift Y y * C := by
  have hWs : Wᴴ = W := by
    have hu := mem_unitaryGroup_iff'.mp hW
    rw [star_eq_conjTranspose] at hu
    calc
      _ = Wᴴ * (W * W) := by rw [hWW, Matrix.mul_one]
      _ = W := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hO := conjTranspose_compressedCell hY hW hWW
  have hD := conjTranspose_decompressedCell hY hWs
  have hm : (compressedCell W - decompressedCell W) *
      (compressedCell W - decompressedCell W)ᴴ =
      2 • (1 : Matrix (Y × Option Y) (Y × Option Y) ℂ) -
        compressedCell W * decompressedCell W - decompressedCell W * compressedCell W := by
    rw [conjTranspose_sub, hO, hD, sub_mul, mul_sub, mul_sub,
      compressedCell_mul_self hY hWW, decompressedCell_mul_self hY hWW]
    module
  dsimp only
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id, hm]
  simp only [submatrix_sub, submatrix_smul, Pi.sub_apply, Pi.smul_apply]
  rw [submatrix_one _ (fun _ _ h ↦ Prod.mk.inj h |>.1),
    submatrix_mul_decompressedCell, submatrix_decompressedCell_mul]

/-- A filled residual row has squared operator norm at most `6 / |Y|`. No uniform-column
hypothesis on `W` is needed. Involutivity of both translations and `W` is used in (13). -/
theorem norm_compressedCell_residual_row_sq_le (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1) (y : Y) :
    ‖(compressedCell W - decompressedCell W).submatrix
      (fun r ↦ (r, some y)) id‖ ^ 2 ≤ 6 / Fintype.card Y := by
  have hWs : Wᴴ = W := by
    have hu := mem_unitaryGroup_iff'.mp hW
    rw [star_eq_conjTranspose] at hu
    calc
      _ = Wᴴ * (W * W) := by rw [hWW, Matrix.mul_one]
      _ = W := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hX : ‖xorShift Y y‖ ≤ 1 := by
    apply l2_opNorm_le_one_of_conjTranspose_mul_self
    exact mem_unitaryGroup_iff'.mp (xorShift_mem_unitaryGroup y)
  have hWn : ‖W‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self (mem_unitaryGroup_iff'.mp hW)
  have hid := Matrix.emptyExtension_residual_identity (xorShift Y y) 1 W
    (uniformResponseProjector (Y := Y)) (Fintype.card Y : ℂ)⁻¹
    (xorShift_mul_self_of_add_self hY y) hWW (by simp) (by simp) (by simp)
    (xorShift_mul_uniformResponseProjector y) (uniformResponseProjector_mul_xorShift y)
  simp only [Matrix.one_mul, Matrix.mul_one] at hid
  have hR := compressedCell_residual_row_gram hY hW hWW y
  dsimp only at hR
  rw [submatrix_compressedCell_filled] at hR
  have hg := hR.trans hid
  have hb := Matrix.emptyExtension_residual_norm_sq_le
    ((compressedCell W - decompressedCell W).submatrix (fun r ↦ (r, some y)) id)
    (xorShift Y y) 1 W (uniformResponseProjector (Y := Y))
    (a := (Fintype.card Y : ℝ)⁻¹) (by positivity) hX (by simp) hWn
    (conjTranspose_xorShift_of_add_self hY y) (by simp) hWs
    (by simpa only [Matrix.one_mul] using uniformResponseProjector_posSemidef (Y := Y))
    (by simpa only [Matrix.one_mul, Matrix.mul_one, Complex.ofReal_inv,
      Complex.ofReal_natCast] using hg)
  simpa only [div_eq_mul_inv] using hb

end Quantum
