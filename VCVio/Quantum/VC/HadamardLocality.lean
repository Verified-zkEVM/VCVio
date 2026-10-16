/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardCellBounds
public import VCVio.Quantum.VC.Proof.Extraction

/-!
# Locality of the empty-sector extension

Conjugating a table-controlled response by all cell compressions cancels the compressions on
unaddressed cells. This identifies the actual VC port with the single-cell matrix and supplies
the population estimate used in the repair note §3.1.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

/-- Conjugating a diagonal control of one coordinate by a tensor of involutions acts only
on that coordinate. -/
theorem piKron_mul_diagonal_coordinate_mul_piKron {ι Z : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z]
    (A : ι → Matrix Z Z ℂ) (hA : ∀ i, A i * A i = 1) (i : ι) (f : Z → ℂ) :
    piKron A * diagonal (fun d ↦ f (d i)) * piKron A =
      piKron (Pi.mulSingle i (A i * diagonal f * A i)) := by
  ext d e
  rw [Matrix.mul_apply]
  simp only [mul_diagonal]
  calc
    _ = ∑ z, f (z i) * (piKron A d z * piKron A z e) := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      rw [sum_mul_piKron_mul_piKron, piKron_apply]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp only [ite_true, Pi.mulSingle_eq_same]
        rw [Matrix.mul_apply]
        simp only [mul_diagonal]
        apply Finset.sum_congr rfl
        intro z _
        ring
      · simp only [hj, ite_false, one_mul, Pi.mulSingle_eq_of_ne hj]
        exact congrFun (congrFun (hA j) (d j)) (e j)

/-- A tensor acting on one coordinate preserves every other coordinate in its support. -/
theorem eq_of_piKron_mulSingle_ne_zero {ι Z : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq Z] (i : ι) (A : Matrix Z Z ℂ) {d e : ι → Z}
    (h : piKron (Pi.mulSingle i A) d e ≠ 0) {j : ι} (hj : j ≠ i) : d j = e j := by
  have hz := Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j)
  rw [Pi.mulSingle_eq_of_ne hj, Matrix.one_apply] at hz
  by_contra hne
  exact hz (ite_eq_right hne)


/-- The addressed factor of a nonzero tensor entry is nonzero. -/
theorem factor_ne_zero_of_piKron_mulSingle_ne_zero {ι Z : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq Z] (i : ι) (A : Matrix Z Z ℂ) {d e : ι → Z}
    (h : piKron (Pi.mulSingle i A) d e ≠ 0) : A (d i) (e i) ≠ 0 := by
  have hz := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  simpa only [Pi.mulSingle_eq_same] using hz

section ports

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

omit [Fintype Y] in
/-- Every response block of a decompressed table extension is diagonal in its database. -/
theorem submatrix_extendedTableOracle_response (W : Matrix Y Y ℂ)
    (i : Fin k) (x z : X) (r s : Y) :
    (extendedTableOracle W (fun d : Fin k → Database X Y ↦ d i)).submatrix
        (fun d ↦ ((x, r), d)) (fun d ↦ ((z, s), d)) =
      diagonal fun d ↦ if x = z then emptyExtensionBlock W (d i x) r s else 0 := by
  ext d e
  by_cases hx : x = z <;> by_cases hd : d = e <;>
    simp [extendedTableOracle_apply, hx, hd]

/-- Compressing a single response matrix element gives the response block of `compressedCell`. -/
theorem cellCompress_mul_diagonal_block_mul (W : Matrix Y Y ℂ) (r s : Y) :
    cellCompress Y * diagonal (fun a ↦ emptyExtensionBlock W a r s) * cellCompress Y =
      (compressedCell W).submatrix (fun a ↦ (r, a)) (fun b ↦ (s, b)) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, submatrix_apply, compressedCell_apply]

/-- A response block of an extended VC port changes only the addressed database cell. -/
theorem submatrix_extendedVCPort_same_input (W : Matrix Y Y ℂ)
    (i : Fin k) (x : X) (r s : Y) :
    (extendedVCPort k X Y W i).submatrix (fun d ↦ ((x, r), d)) (fun d ↦ ((x, s), d)) =
      piKron (Pi.mulSingle i (piKron (Pi.mulSingle x
        ((compressedCell W).submatrix (fun a ↦ (r, a)) (fun b ↦ (s, b)))))) := by
  rw [extendedVCPort, submatrix_one_kronecker_mul_mul_one_kronecker,
    submatrix_extendedTableOracle_response]
  simp only [ite_true, compressDatabases]
  rw [piKron_mul_diagonal_coordinate_mul_piKron _ (fun _ ↦ compressAll_mul_self X Y)
    i (fun d : Database X Y ↦ emptyExtensionBlock W (d x) r s)]
  congr 2
  rw [compressAll, piKron_mul_diagonal_coordinate_mul_piKron _
    (fun _ ↦ cellCompress_mul_self Y) x (fun a ↦ emptyExtensionBlock W a r s),
    cellCompress_mul_diagonal_block_mul]

/-- An extended VC port preserves its query input. -/
theorem extendedVCPort_apply_eq_zero_of_input_ne (W : Matrix Y Y ℂ)
    (i : Fin k) {x z : X} (hx : x ≠ z) (r s : Y) (d e : Fin k → Database X Y) :
    extendedVCPort k X Y W i ((x, r), d) ((z, s), e) = 0 := by
  have he := submatrix_one_kronecker_mul_mul_one_kronecker
    (compressDatabases k X Y) (extendedTableOracle W (fun d : Fin k → Database X Y ↦ d i))
    (x, r) (z, s)
  rw [submatrix_extendedTableOracle_response] at he
  simpa [extendedVCPort, hx] using congrFun (congrFun he d) e

/-- Nonzero entries of a VC port preserve every unaddressed database and cell. -/
theorem extendedVCPort_cells_eq (W : Matrix Y Y ℂ) (i : Fin k)
    (a b : X × Y) (d e : Fin k → Database X Y)
    (h : extendedVCPort k X Y W i (a, d) (b, e) ≠ 0)
    (j : Fin k) (x : X) (hjx : j ≠ i ∨ x ≠ a.1) : d j x = e j x := by
  have hab : a.1 = b.1 := by
    by_contra hne
    exact h (extendedVCPort_apply_eq_zero_of_input_ne W i hne a.2 b.2 d e)
  obtain ⟨z, r⟩ := a
  obtain ⟨z', s⟩ := b
  dsimp only at hab hjx
  subst z'
  have he := congrFun (congrFun (submatrix_extendedVCPort_same_input W i z r s) d) e
  change extendedVCPort k X Y W i ((z, r), d) ((z, s), e) = _ at he
  rw [he] at h
  rcases hjx with hj | hx
  · exact congrFun (eq_of_piKron_mulSingle_ne_zero i _ h hj) x
  · by_cases hj : j = i
    · subst j
      exact eq_of_piKron_mulSingle_ne_zero z _
        (factor_ne_zero_of_piKron_mulSingle_ne_zero i _ h) hx
    · exact congrFun (eq_of_piKron_mulSingle_ne_zero i _ h hj) x

/-- One VC port raises each database population by at most one. -/
theorem extendedVCPort_size_le (W : Matrix Y Y ℂ) (i j : Fin k)
    (a b : X × Y) (d e : Fin k → Database X Y)
    (h : extendedVCPort k X Y W i (a, d) (b, e) ≠ 0) :
    (d j).size ≤ (e j).size + 1 := by
  have he : d j = Function.update (e j) a.1 (d j a.1) := by
    funext x
    by_cases hx : x = a.1
    · subst x; simp
    · rw [Function.update_of_ne hx]
      exact extendedVCPort_cells_eq W i a b d e h j x (Or.inr hx)
  rw [he]
  exact Database.size_update_le _ _ _

end ports

end Quantum
