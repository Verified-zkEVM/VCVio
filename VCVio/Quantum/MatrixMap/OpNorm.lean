/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator-norm estimates for matrices

General estimates for the `L²` operator norm of matrices, the norm of the scoped instance
`Matrix.instL2OpNormedAddCommGroup` (open `Matrix.Norms.L2Operator`). The norm of `A` is the
smallest `c` with `‖A v‖ ≤ c ‖v‖` for all vectors `v`, so every estimate here reduces to a sum of
squares over the entries of `A *ᵥ v`.

## Main results

* `Matrix.sum_norm_mulVec_sq_le` and `Matrix.l2_opNorm_le_of_sum_norm_mulVec_sq_le`: the operator
  norm in terms of sums of squares of coordinates.
* `Matrix.l2_opNorm_one_le`, `Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self`: the identity
  and every isometry have norm at most one.
* `Matrix.l2_opNorm_mul_mul_conjTranspose_le` and `Matrix.l2_opNorm_conjTranspose_mul_mul_le`:
  conjugating by an isometry does not increase the norm.
* `Matrix.l2_opNorm_kronecker_one_le`: tensoring with the identity of another register does not
  increase the norm.
* `Matrix.l2_opNorm_le_of_blocks`: a matrix whose nonzero entries stay inside the blocks of a
  labelling has norm at most `c` as soon as, for every block, the sum of the squared entries of
  the rows in that block is at most `c ^ 2`. This is the Frobenius bound applied block by block.
-/

public section

open scoped Matrix.Norms.L2Operator Kronecker

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ## The operator norm through coordinates -/

/-- The squared coordinates of `A *ᵥ v` sum to at most `‖A‖ ^ 2` times those of `v`. -/
theorem sum_norm_mulVec_sq_le [DecidableEq n] (A : Matrix m n 𝕜) (v : n → 𝕜) :
    ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
  have h := l2_opNorm_mulVec A (WithLp.toLp 2 v)
  have h₀ : 0 ≤ ‖(EuclideanSpace.equiv m 𝕜).symm (A *ᵥ v)‖ := norm_nonneg _
  have h₂ := pow_le_pow_left₀ h₀ h 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq] at h₂
  exact h₂

/-- A bound on the squared coordinates of `A *ᵥ v` for every `v` bounds the operator norm. -/
theorem l2_opNorm_le_of_sum_norm_mulVec_sq_le [DecidableEq n] {A : Matrix m n 𝕜} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ v : n → 𝕜, ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ c ^ 2 * ∑ j, ‖v j‖ ^ 2) :
    ‖A‖ ≤ c := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x ↦ ?_
  have hx := h x.ofLp
  have key : ‖((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans
      LinearMap.toContinuousLinearMap A) x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact hx
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
    two_ne_zero).mp key

/-- The identity matrix has norm at most one. -/
theorem l2_opNorm_one_le [DecidableEq n] : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 :=
  l2_opNorm_le_of_sum_norm_mulVec_sq_le zero_le_one fun v ↦ by simp

/-- An isometry has norm at most one. -/
theorem l2_opNorm_le_one_of_conjTranspose_mul_self [DecidableEq n] {U : Matrix m n 𝕜}
    (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self U
  rw [hU] at h
  nlinarith [norm_nonneg U, l2_opNorm_one_le (𝕜 := 𝕜) (n := n)]

/-- Conjugating by an isometry `U`, as `U A Uᴴ`, does not increase the norm. -/
theorem l2_opNorm_mul_mul_conjTranspose_le [DecidableEq m] [DecidableEq n] {U : Matrix m n 𝕜}
    (hU : Uᴴ * U = 1) (A : Matrix n n 𝕜) : ‖U * A * Uᴴ‖ ≤ ‖A‖ := by
  have h₁ := l2_opNorm_le_one_of_conjTranspose_mul_self hU
  have h₂ : ‖Uᴴ‖ ≤ 1 := (l2_opNorm_conjTranspose U).le.trans h₁
  calc ‖U * A * Uᴴ‖ ≤ ‖U * A‖ * ‖Uᴴ‖ := l2_opNorm_mul _ _
    _ ≤ ‖U‖ * ‖A‖ * ‖Uᴴ‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖A‖ * 1 := by gcongr
    _ = ‖A‖ := by ring

/-- Conjugating by the adjoint of a coisometry `U`, as `Uᴴ A U`, does not increase the norm. -/
theorem l2_opNorm_conjTranspose_mul_mul_le [DecidableEq m] [DecidableEq n] {U : Matrix m n 𝕜}
    (hU : U * Uᴴ = 1) (A : Matrix m m 𝕜) : ‖Uᴴ * A * U‖ ≤ ‖A‖ := by
  have h := l2_opNorm_mul_mul_conjTranspose_le (U := Uᴴ) (by rwa [conjTranspose_conjTranspose]) A
  rwa [conjTranspose_conjTranspose] at h

/-! ## Tensoring with the identity -/

/-- Tensoring with the identity of another register does not increase the norm. -/
theorem l2_opNorm_kronecker_one_le [DecidableEq n] [DecidableEq p] (A : Matrix m n 𝕜) :
    ‖A ⊗ₖ (1 : Matrix p p 𝕜)‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_sum_norm_mulVec_sq_le (norm_nonneg A) fun v ↦ ?_
  have hrow (i : m) (e : p) :
      ((A ⊗ₖ (1 : Matrix p p 𝕜)) *ᵥ v) (i, e) = (A *ᵥ fun j ↦ v (j, e)) i := by
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  simp only [Fintype.sum_prod_type, hrow]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j e ↦ ‖v (j, e)‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun e _ ↦ sum_norm_mulVec_sq_le A _

/-! ## The Frobenius bound block by block -/

/-- **Block Frobenius bound.** Let `βm` and `βn` label the rows and the columns of `A` by blocks,
with every nonzero entry of `A` inside a block. If, for every column `j`, the squared entries of
the rows in the block of `j` sum to at most `c ^ 2`, then `‖A‖ ≤ c`. -/
theorem l2_opNorm_le_of_blocks [DecidableEq n] {κ : Type*} [DecidableEq κ] {A : Matrix m n 𝕜}
    (βm : m → κ) (βn : n → κ) (hA : ∀ i j, A i j ≠ 0 → βm i = βn j) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ j, ∑ i, (if βm i = βn j then ∑ j', ‖A i j'‖ ^ 2 else 0) ≤ c ^ 2) :
    ‖A‖ ≤ c := by
  refine l2_opNorm_le_of_sum_norm_mulVec_sq_le hc fun v ↦ ?_
  -- Cauchy–Schwarz on each row, against `v` restricted to the block of the row.
  have hrow (i : m) : ‖(A *ᵥ v) i‖ ^ 2 ≤
      (∑ j, ‖A i j‖ ^ 2) * ∑ j, (if βm i = βn j then ‖v j‖ ^ 2 else 0) := by
    have hsum : (A *ᵥ v) i = ∑ j, A i j * (if βm i = βn j then v j else 0) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases h : A i j = 0
      · simp [h]
      · simp [hA i j h]
    have h₁ : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖if βm i = βn j then v j else 0‖ := by
      rw [hsum]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    refine h₂.trans ((Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_))
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  calc ∑ i, ‖(A *ᵥ v) i‖ ^ 2
      ≤ ∑ i, (∑ j', ‖A i j'‖ ^ 2) * ∑ j, (if βm i = βn j then ‖v j‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun i _ ↦ hrow i
    _ = ∑ j, ‖v j‖ ^ 2 * ∑ i, (if βm i = βn j then ∑ j', ‖A i j'‖ ^ 2 else 0) := by
        have h (i : m) : (∑ j', ‖A i j'‖ ^ 2) * ∑ j, (if βm i = βn j then ‖v j‖ ^ 2 else 0) =
            ∑ j, (if βm i = βn j then (∑ j', ‖A i j'‖ ^ 2) * ‖v j‖ ^ 2 else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
        rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp [mul_comm]
    _ ≤ ∑ j, ‖v j‖ ^ 2 * c ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hblock j) (by positivity)
    _ = c ^ 2 * ∑ j, ‖v j‖ ^ 2 := by rw [Finset.mul_sum]; simp only [mul_comm]

end Matrix
