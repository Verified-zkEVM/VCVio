/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardResidual
public import VCVio.Quantum.MatrixMap.Commutant

/-!
# Partition bounds for a compressed cell

Summing the response-row estimates over changed filled labels gives the residual bound of the
repair note. Matrix completion produces a label-preserving approximation on one cell.
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace Quantum

variable {Y L : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [DecidableEq L]

/-- The fraction of filled answers whose label differs from the empty-cell label. -/
@[expose]
noncomputable def cellInstability (π : Option Y → L) : ℝ :=
  ((Finset.univ.filter fun y ↦ π (some y) ≠ π none).card : ℝ) / Fintype.card Y

/-- The projection onto cell labels differing from the empty-cell label. -/
@[expose]
def badCellProjector (π : Option Y → L) : Matrix (Y × Option Y) (Y × Option Y) ℂ :=
  diagonal fun p ↦ if π p.2 ≠ π none then 1 else 0

omit [AddCommGroup Y] in
/-- The changing-label projection is an orthogonal projection. -/
theorem isStarProjection_badCellProjector (π : Option Y → L) :
    IsStarProjection (badCellProjector π) := by
  have he : badCellProjector π =
      (labelProjector (fun p : Y × Option Y ↦ decide (π p.2 ≠ π none)) true :
        Matrix (Y × Option Y) (Y × Option Y) ℂ) := by
    simp [badCellProjector, labelProjector]
  rw [he]
  exact isStarProjection_labelProjector _ _

/-- The combined changing-label residual rows satisfy the coefficient-six bound. -/
theorem norm_badCellProjector_mul_residual_le (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1)
    (π : Option Y → L) :
    ‖badCellProjector π * (compressedCell W - decompressedCell W)‖ ≤
      Real.sqrt (6 * cellInstability π) := by
  have hI : 0 ≤ cellInstability π := by unfold cellInstability; positivity
  apply l2_opNorm_le_of_sum_norm_mulVec_sq_le (by positivity)
  intro v
  rw [Real.sq_sqrt (by positivity : 0 ≤ 6 * cellInstability π)]
  let M := compressedCell W - decompressedCell W
  have he : ∀ r a, ((badCellProjector π * M) *ᵥ v) (r, a) =
      if π a ≠ π none then (M *ᵥ v) (r, a) else 0 := by
    intro r a
    rw [← mulVec_mulVec]
    simp only [badCellProjector, mulVec_diagonal]
    split_ifs <;> simp
  change (∑ p : Y × Option Y, ‖((badCellProjector π * M) *ᵥ v) p‖ ^ 2) ≤ _
  simp only [Fintype.sum_prod_type, he, Fintype.sum_option, ne_eq, not_true_eq_false,
    ite_false, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [Finset.sum_comm]
  have hb : ∀ y, ∑ r : Y, ‖(if π (some y) ≠ π none then (M *ᵥ v) (r, some y) else 0)‖ ^ 2 ≤
      if π (some y) ≠ π none then (6 / Fintype.card Y) * ∑ p, ‖v p‖ ^ 2 else 0 := by
    intro y
    by_cases hy : π (some y) ≠ π none
    · simp_rw [ite_eq_left hy]
      have hr := sum_norm_mulVec_sq_le
        (M.submatrix (fun r ↦ (r, some y)) id) v
      have hn := norm_compressedCell_residual_row_sq_le hY hW hWW y
      exact hr.trans (mul_le_mul_of_nonneg_right hn (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    · simp [hy]
  refine (Finset.sum_le_sum fun y _ ↦ hb y).trans_eq ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  dsimp only [cellInstability]
  simp only [Fintype.sum_prod_type, Fintype.sum_option]
  ring

/-- Completion of the changing-label rows gives a label-preserving operator at squared
distance at most six times the changing-answer fraction. -/
theorem exists_pinch_eq_compressedCell_sub_sq_le (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1)
    (π : Option Y → L) :
    ∃ S, pinch (fun p : Y × Option Y ↦ π p.2) S = S ∧
      ‖compressedCell W - S‖ ^ 2 ≤ 6 * cellInstability π := by
  have hWs : Wᴴ = W := by
    have hu := mem_unitaryGroup_iff'.mp hW
    rw [star_eq_conjTranspose] at hu
    calc
      _ = Wᴴ * (W * W) := by rw [hWW, Matrix.mul_one]
      _ = W := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hP := isStarProjection_badCellProjector π
  have hPh : (badCellProjector π)ᴴ = badCellProjector π := hP.isSelfAdjoint
  have hrow := norm_badCellProjector_mul_residual_le hY hW hWW π
  have hcol : ‖(compressedCell W - decompressedCell W) * badCellProjector π‖ ≤
      Real.sqrt (6 * cellInstability π) := by
    rw [← l2_opNorm_conjTranspose, conjTranspose_mul, hPh, conjTranspose_sub,
      conjTranspose_compressedCell hY hW hWW, conjTranspose_decompressedCell hY hWs]
    exact hrow
  obtain ⟨T, hPT, hTP, hT⟩ := exists_completion hP hrow hcol
  refine ⟨compressedCell W - T, ?_, ?_⟩
  · rw [pinch_eq_self_iff]
    intro p q hS
    by_contra hpq
    have hD : decompressedCell W p q = 0 := by
      have hc : p.2 ≠ q.2 := fun he ↦ hpq (congrArg π he)
      simp [decompressedCell, blockDiagonal_apply, hc]
    have hroweq (hp : π p.2 ≠ π none) : T p q =
        (compressedCell W - decompressedCell W) p q := by
      have h := congrFun (congrFun hPT p) q
      simpa only [badCellProjector, diagonal_mul, ite_eq_left hp, one_mul] using h
    have hcoleq (hq : π q.2 ≠ π none) : T p q =
        (compressedCell W - decompressedCell W) p q := by
      have h := congrFun (congrFun hTP p) q
      simpa only [badCellProjector, mul_diagonal, ite_eq_left hq, mul_one] using h
    have he : T p q = (compressedCell W - decompressedCell W) p q := by
      by_cases hp : π p.2 ≠ π none
      · exact hroweq hp
      · apply hcoleq
        exact fun hq ↦ hpq ((not_ne_iff.mp hp).trans hq.symm)
    apply hS
    simp only [Matrix.sub_apply, he, hD, sub_zero, sub_self]
  · rw [sub_sub_cancel]
    exact (pow_le_pow_left₀ (norm_nonneg _) hT 2).trans_eq
      (Real.sq_sqrt (by unfold cellInstability; positivity))

/-- The cell-level generalized instability estimate, with constant `24`, for any auxiliary
label-controlled unitary. This uses the repair note's residual completion. -/
theorem norm_commutator_compressedCell_sq_le_twentyFour_mul
    (hY : ∀ y : Y, y + y = 0) {W : Matrix Y Y ℂ}
    (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1) (π : Option Y → L)
    {E : Type*} [Fintype E] [DecidableEq E] (U : L → Matrix E E ℂ)
    (hU : ∀ l, U l ∈ unitaryGroup E ℂ) :
    ‖labelControlled (fun p : (Y × Option Y) × E ↦ π p.1.2)
          (fun l ↦ (1 : Matrix (Y × Option Y) (Y × Option Y) ℂ) ⊗ₖ U l) *
          (compressedCell W ⊗ₖ (1 : Matrix E E ℂ)) -
        (compressedCell W ⊗ₖ (1 : Matrix E E ℂ)) *
          labelControlled (fun p : (Y × Option Y) × E ↦ π p.1.2)
            (fun l ↦ (1 : Matrix (Y × Option Y) (Y × Option Y) ℂ) ⊗ₖ U l)‖ ^ 2 ≤
      24 * cellInstability π := by
  obtain ⟨S, hS, hdist⟩ := exists_pinch_eq_compressedCell_sub_sq_le hY hW hWW π
  have h := l2_opNorm_commutator_labelControlled_one_kronecker_le (A := compressedCell W) hS hU
  calc
    _ ≤ (2 * ‖compressedCell W - S‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖compressedCell W - S‖ ^ 2 := by ring
    _ ≤ 4 * (6 * cellInstability π) := by gcongr
    _ = _ := by ring

end Quantum
