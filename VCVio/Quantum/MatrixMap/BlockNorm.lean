/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.MatrixMap.Norm

/-!
# The operator norm of a classically controlled operator

An operator controlled by a classical register `C`, `∑ c, |c⟩⟨c| ⊗ A c`, acts on the
block of each basis state `|c⟩` as `A c` and does not mix blocks. Its `L²` operator norm
is the largest block norm (`Matrix.l2_opNorm_sum_single_kronecker`). This is the step of
Lemma 9.2 of Chiesa, Di, Hu and Zheng (ePrint 2025/2166, pp. 58–59) that turns a bound for
every fixed value of a classical control register, the commitment tuple and the other databases,
into a bound for the
operator controlled by it; the index `C` is any finite type and the blocks are rectangular.

## Main results

* `Matrix.l2_opNorm_submatrix_le_of_injective`: restricting the rows and the columns along
  injective maps does not increase the norm.
* `Matrix.sum_single_kronecker_apply`: the entries of `∑ c, |c⟩⟨c| ⊗ A c`.
* `Matrix.l2_opNorm_sum_single_kronecker`: `‖∑ c, |c⟩⟨c| ⊗ A c‖ = ⨆ c, ‖A c‖`.
-/

public section

open scoped Matrix.Norms.L2Operator Kronecker

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}

/-! ## Restriction along injective maps -/

/-- The columns of the identity along an injective map form an isometry. -/
theorem conjTranspose_one_submatrix_mul_self [Fintype m] [DecidableEq m] {m' : Type*}
    [DecidableEq m'] {f : m' → m} (hf : Function.Injective f) :
    ((1 : Matrix m m 𝕜).submatrix id f)ᴴ * (1 : Matrix m m 𝕜).submatrix id f = 1 := by
  ext a b
  simp [mul_apply, one_apply, hf.eq_iff]

/-- Restricting the rows and the columns along injective maps does not increase the norm. -/
theorem l2_opNorm_submatrix_le_of_injective [Fintype m] [Fintype n] [DecidableEq n]
    {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m n 𝕜) {f : m' → m} {g : n' → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖A.submatrix f g‖ ≤ ‖A‖ := by
  classical
  have hP := l2_opNorm_le_one_of_conjTranspose_mul_self (conjTranspose_one_submatrix_mul_self
    (𝕜 := 𝕜) hf)
  have hQ := l2_opNorm_le_one_of_conjTranspose_mul_self (conjTranspose_one_submatrix_mul_self
    (𝕜 := 𝕜) hg)
  have h : A.submatrix f g =
      ((1 : Matrix m m 𝕜).submatrix id f)ᴴ * A * (1 : Matrix n n 𝕜).submatrix id g := by
    ext a b
    simp [mul_apply, one_apply]
  rw [h]
  calc ‖((1 : Matrix m m 𝕜).submatrix id f)ᴴ * A * (1 : Matrix n n 𝕜).submatrix id g‖
      ≤ ‖((1 : Matrix m m 𝕜).submatrix id f)ᴴ‖ * ‖A‖ *
          ‖(1 : Matrix n n 𝕜).submatrix id g‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ 1 * ‖A‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        gcongr
    _ = ‖A‖ := by ring

/-! ## Classically controlled operators -/

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The entries of the controlled operator `∑ c, |c⟩⟨c| ⊗ A c`: the entry of `A c`
inside the block of `c`, and `0` across blocks. -/
theorem sum_single_kronecker_apply (A : C → Matrix m n 𝕜) (c c' : C) (i : m) (j : n) :
    (∑ c₀, single c₀ c₀ (1 : 𝕜) ⊗ₖ A c₀) (c, i) (c', j) =
      if c = c' then A c i j else 0 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single c]
  · by_cases h : c = c'
    · subst h
      simp
    · simp [h]
  · intro b _ hb
    simp only [kroneckerMap_apply, single_apply]
    grind
  · simp

/-- The block of `c` of the controlled operator is `A c`. -/
theorem submatrix_sum_single_kronecker (A : C → Matrix m n 𝕜) (c : C) :
    (∑ c₀, single c₀ c₀ (1 : 𝕜) ⊗ₖ A c₀).submatrix
      (fun i ↦ (c, i)) (fun j ↦ (c, j)) = A c := by
  ext i j
  simp [sum_single_kronecker_apply]

/-- **The norm of a classically controlled operator** is the largest norm of its blocks:
`‖∑ c, |c⟩⟨c| ⊗ A c‖ = ⨆ c, ‖A c‖`, for any finite control register `C` (the
supremum over an empty `C` is `0`). -/
theorem l2_opNorm_sum_single_kronecker [Fintype m] [Fintype n] [DecidableEq n]
    (A : C → Matrix m n 𝕜) :
    ‖∑ c, single c c (1 : 𝕜) ⊗ₖ A c‖ = ⨆ c, ‖A c‖ := by
  classical
  set M := ∑ c, single c c (1 : 𝕜) ⊗ₖ A c
  have hbdd : BddAbove (Set.range fun c ↦ ‖A c‖) := (Set.finite_range _).bddAbove
  refine le_antisymm ?_ ?_
  · refine l2_opNorm_le_of_sum_norm_mulVec_sq_le (Real.iSup_nonneg fun _ ↦ norm_nonneg _)
      fun v ↦ ?_
    have hrow (c : C) (i : m) : (M *ᵥ v) (c, i) = (A c *ᵥ fun j ↦ v (c, j)) i := by
      simp only [mulVec, dotProduct, Fintype.sum_prod_type, M, sum_single_kronecker_apply,
        ite_mul, zero_mul]
      rw [Finset.sum_eq_single c (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
      simp
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    simp only [hrow]
    refine Finset.sum_le_sum fun c _ ↦ (sum_norm_mulVec_sq_le (A c) _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (le_ciSup hbdd c) 2
  · rcases isEmpty_or_nonempty C with hC | hC
    · rw [Real.iSup_of_isEmpty]
      exact norm_nonneg _
    · refine ciSup_le fun c ↦ ?_
      rw [← submatrix_sum_single_kronecker A c]
      exact l2_opNorm_submatrix_le_of_injective M (fun _ _ h ↦ (Prod.mk.inj h).2)
        (fun _ _ h ↦ (Prod.mk.inj h).2)

end Matrix

namespace Quantum.MatrixMap

open Matrix
open scoped ComplexOrder

/-- A squared operator-norm bound gives positive Gram slack for a rectangular matrix. -/
theorem posSemidef_scalar_sub_gram_of_norm_sq_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (K : Matrix m n ℂ) {r : ℝ} (h : ‖K‖ ^ 2 ≤ r) :
    (r • (1 : Matrix n n ℂ) - Kᴴ * K).PosSemidef := by
  have h₁ := posSemidef_l2_opNorm_sq_smul_one_sub K
  have h₂ := (PosSemidef.one (n := n) (R := ℂ)).smul (sub_nonneg.mpr h)
  convert h₁.add h₂ using 1
  module

end Quantum.MatrixMap
