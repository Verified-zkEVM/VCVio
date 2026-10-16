/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardTruncation

/-!
# The coefficient-six binary event estimate

For a binary event projector `G`, its reflection `2G - I` is a label-controlled unitary and
its commutator is twice the event commutator. Thus the coefficient `24` of the generalized
instability bound gives the coefficient `6` of the repair note's equation (12).
-/

public section

open Matrix OracleSpec
open scoped Matrix.Norms.L2Operator ENNReal

namespace Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The truncated extension satisfies the coefficient-six bound for every binary database
event. The empty-sector response needs to be a unitary involution; its first column is arbitrary. -/
theorem norm_binary_commutator_truncatedExtendedOracle_sq_le
    [UniformAnswerMeasure (X →ₒ Y)] (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1)
    (π : Database X Y → Bool) (t : ℕ) (b : Bool) :
    ‖labelProjector (fun p : (X × Y) × Database X Y ↦ π p.2) b * truncatedExtendedOracle W t -
        truncatedExtendedOracle W t *
          labelProjector (fun p : (X × Y) × Database X Y ↦ π p.2) b‖ ^ 2 ≤
      6 * (Database.instability π t).toReal := by
  let U : Bool → Matrix Unit Unit ℂ := fun l ↦ if l = b then 1 else -1
  have hU : ∀ l, U l ∈ unitaryGroup Unit ℂ := by
    intro l
    by_cases h : l = b <;> simp [U, h, mem_unitaryGroup_iff]
  let O := truncatedExtendedOracle (X := X) W t
  let G : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
    labelProjector (fun p : (X × Y) × Database X Y ↦ π p.2) b
  have he : (auxiliaryCommutator O (fun a ↦ π a.2) U).submatrix
      (fun a ↦ (a, ())) (fun a ↦ (a, ())) = (2 : ℂ) • (G * O - O * G) := by
    ext a c
    simp only [submatrix_apply, auxiliaryCommutator_apply, Matrix.smul_apply,
      Matrix.sub_apply, G, labelProjector, diagonal_mul, mul_diagonal, U]
    split_ifs <;> simp <;> ring
  have hn := l2_opNorm_submatrix_le_of_injective
    (auxiliaryCommutator O (fun a ↦ π a.2) U)
    (f := fun a ↦ (a, ())) (g := fun a ↦ (a, ()))
    (fun _ _ h ↦ Prod.mk.inj h |>.1) (fun _ _ h ↦ Prod.mk.inj h |>.1)
  rw [he, norm_smul] at hn
  norm_num at hn
  have hs := norm_auxiliaryCommutator_truncatedExtendedOracle_sq_le hY hW hWW π t U hU
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ‖G * O - O * G‖) hn 2
  change ‖G * O - O * G‖ ^ 2 ≤ _
  nlinarith

end Quantum
