/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardLocality
public import VCVio.Quantum.VC.HadamardCellPartition

/-!
# The extended oracle on one database

The database operation is the direct sum of the compressed-cell operations over query inputs
and unaddressed cell contents. This form supports population truncation.
-/

public section

open Matrix OracleSpec
open scoped Kronecker Matrix.Norms.L2Operator ENNReal

namespace Quantum

/-- An entry of a tensor with only one nonidentity factor. -/
theorem piKron_mulSingle_apply {ι Z : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Z]
    (i : ι) (A : Matrix Z Z ℂ) (d e : ι → Z) :
    piKron (Pi.mulSingle i A) d e = if ∀ j, j ≠ i → d j = e j then A (d i) (e i) else 0 := by
  rw [piKron_apply, Fintype.prod_eq_mul_prod_subtype_ne _ i, Pi.mulSingle_eq_same]
  have hrest : (∏ j : {j // j ≠ i},
      (Pi.mulSingle i A : ι → Matrix Z Z ℂ) j.1 (d j.1) (e j.1)) =
      if ∀ j, j ≠ i → d j = e j then 1 else 0 := by
    have h1 (j : {j // j ≠ i}) : (Pi.mulSingle i A : ι → Matrix Z Z ℂ) j.1 = 1 :=
      Pi.mulSingle_eq_of_ne (M := fun _ ↦ Matrix Z Z ℂ) j.2 A
    simp only [h1, Matrix.one_apply]
    rw [Fintype.prod_boole]
    simp only [Subtype.forall]
  rw [hrest]
  split_ifs <;> simp

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The compressed extension on one database. -/
@[expose]
noncomputable def extendedCompressedOracle (W : Matrix Y Y ℂ) :
    Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  (1 ⊗ₖ compressAll X Y) * extendedTableOracle W (fun d x ↦ d x) *
    (1 ⊗ₖ compressAll X Y)

/-- A fixed-input response block is the addressed-cell tensor. -/
theorem submatrix_extendedCompressedOracle (W : Matrix Y Y ℂ) (x : X) (r s : Y) :
    (extendedCompressedOracle (X := X) W).submatrix
        (fun d ↦ ((x, r), d)) (fun d ↦ ((x, s), d)) =
      piKron (Pi.mulSingle x
        ((compressedCell W).submatrix (fun a ↦ (r, a)) (fun b ↦ (s, b)))) := by
  rw [extendedCompressedOracle, submatrix_one_kronecker_mul_mul_one_kronecker]
  have he : (extendedTableOracle W (fun d : Database X Y ↦ d)).submatrix
      (fun d ↦ ((x, r), d)) (fun d ↦ ((x, s), d)) =
      diagonal (fun d ↦ emptyExtensionBlock W (d x) r s) := by
    ext d e
    by_cases hd : d = e <;> simp [extendedTableOracle_apply, hd]
  rw [he, compressAll, piKron_mul_diagonal_coordinate_mul_piKron _
    (fun _ ↦ cellCompress_mul_self Y) x (fun a ↦ emptyExtensionBlock W a r s),
    cellCompress_mul_diagonal_block_mul]

/-- The one-database oracle preserves the input and every unaddressed cell. -/
theorem extendedCompressedOracle_apply (W : Matrix Y Y ℂ) (x z : X) (r s : Y)
    (d e : Database X Y) :
    extendedCompressedOracle W ((x, r), d) ((z, s), e) =
      if x = z ∧ ∀ j, j ≠ x → d j = e j then
        compressedCell W (r, d x) (s, e x) else 0 := by
  by_cases hx : x = z
  · subst z
    have he := congrFun (congrFun (submatrix_extendedCompressedOracle W x r s) d) e
    simpa only [submatrix_apply, piKron_mulSingle_apply, true_and] using he
  · have he := submatrix_one_kronecker_mul_mul_one_kronecker
      (compressAll X Y) (extendedTableOracle W (fun d : Database X Y ↦ d)) (x, r) (z, s)
    have hz : (extendedTableOracle W (fun d : Database X Y ↦ d)).submatrix
        (fun d ↦ ((x, r), d)) (fun d ↦ ((z, s), d)) = 0 := by
      ext d e
      simp [extendedTableOracle_apply, hx]
    rw [hz, Matrix.mul_zero, Matrix.zero_mul] at he
    simpa [extendedCompressedOracle, hx] using congrFun (congrFun he d) e

/-- The extended VC port is the one-database extension acting on its selected database. -/
theorem extendedVCPort_eq_onFactor {k : ℕ} (W : Matrix Y Y ℂ) (i : Fin k) :
    extendedVCPort k X Y W i =
      onFactor (splitAt (X × Y) (Database X Y) i) (extendedCompressedOracle W) := by
  ext ⟨⟨x, r⟩, d⟩ ⟨⟨z, s⟩, e⟩
  rw [onFactor_apply]
  simp only [splitAt_apply, extendedCompressedOracle_apply]
  by_cases hx : x = z
  · subst z
    have he := congrFun (congrFun (submatrix_extendedVCPort_same_input W i x r s) d) e
    change extendedVCPort k X Y W i ((x, r), d) ((x, s), e) = _ at he
    rw [he, piKron_mulSingle_apply]
    simp only [piKron_mulSingle_apply, submatrix_apply, true_and]
    have hr : ((fun j : {j // j ≠ i} ↦ d j.1) = fun j ↦ e j.1) ↔
        ∀ j, j ≠ i → d j = e j := by simp [funext_iff]
    simp only [hr]
    split_ifs <;> rfl
  · rw [extendedVCPort_apply_eq_zero_of_input_ne W i hx]
    simp [hx]

/-- The database-size truncation of the extended oracle. -/
@[expose]
noncomputable def truncatedExtendedOracle (W : Matrix Y Y ℂ) (t : ℕ) :
    Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  sizeProjector X Y t * extendedCompressedOracle W * sizeProjector X Y t

/-- Truncation deletes precisely the entries outside the population bound. -/
theorem truncatedExtendedOracle_apply (W : Matrix Y Y ℂ) (t : ℕ)
    (p q : (X × Y) × Database X Y) :
    truncatedExtendedOracle W t p q =
      if p.2.size ≤ t ∧ q.2.size ≤ t then extendedCompressedOracle W p q else 0 := by
  simp only [truncatedExtendedOracle, sizeProjector, mul_diagonal, diagonal_mul]
  split_ifs <;> simp_all

end Quantum
