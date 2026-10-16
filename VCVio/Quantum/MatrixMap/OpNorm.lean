/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Algebra.Star.StarProjection
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
* `Matrix.l2_opNorm_submatrix_equiv`: reindexing rows and columns does not change the norm.
* `Matrix.l2_opNorm_le_of_submatrix_le`: the same reduction with an arbitrary bound on each block,
  the norm being the largest norm of a block.
* `Matrix.l2_opNorm_le_of_corner_eq_zero`: a matrix with a vanishing corner block has norm at most
  `(√d + √(d + 4a)) / 2`, where `a` bounds the squared entries of each of the two adjacent blocks
  and `d` those of the opposite block. The corollaries `Matrix.l2_opNorm_sq_le_of_corner_eq_zero`
  (`‖E‖ ^ 2 ≤ 4 / 3 * c` from row and column sums at most `c` outside the corner) and
  `Matrix.l2_opNorm_sq_le_of_diagonal_blocks_eq_zero` (`‖E‖ ^ 2 ≤ c` when the opposite block
  vanishes too) are the linear algebra behind the sharp pinching constants `8` and `6`.
* `Matrix.l2_opNorm_add_le_max_of_isStarProjection`: two operators with orthogonal domains and
  orthogonal ranges have a sum of norm at most the larger of the two norms.
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

/-- The operator norm is at most the Frobenius norm. -/
theorem l2_opNorm_sq_le_sum_sq [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have h := l2_opNorm_le_of_blocks (κ := Unit) (A := A) (fun _ ↦ ()) (fun _ ↦ ())
    (fun _ _ _ ↦ rfl) (Real.sqrt_nonneg _) fun _ ↦ by
      rw [Real.sq_sqrt h0]
      simp
  calc ‖A‖ ^ 2 ≤ √(∑ i, ∑ j, ‖A i j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt h0

/-- Reindexing the rows and the columns by equivalences does not increase the norm. -/
theorem l2_opNorm_submatrix_equiv_le [DecidableEq n] {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq n'] (A : Matrix m n 𝕜) (e : m' ≃ m) (f : n' ≃ n) :
    ‖A.submatrix e f‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_sum_norm_mulVec_sq_le (norm_nonneg A) fun v ↦ ?_
  have hv : ∀ i, (A.submatrix e f *ᵥ v) i = (A *ᵥ (v ∘ f.symm)) (e i) := fun i ↦ by
    simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply]
    exact Fintype.sum_equiv f _ _ fun j ↦ by simp
  calc ∑ i, ‖(A.submatrix e f *ᵥ v) i‖ ^ 2 = ∑ i, ‖(A *ᵥ (v ∘ f.symm)) i‖ ^ 2 :=
        Fintype.sum_equiv e _ _ fun i ↦ by rw [hv]
    _ ≤ ‖A‖ ^ 2 * ∑ j, ‖(v ∘ f.symm) j‖ ^ 2 := sum_norm_mulVec_sq_le A _
    _ = ‖A‖ ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
        congr 1
        exact Fintype.sum_equiv f.symm _ _ fun j ↦ rfl

/-- Reindexing the rows and the columns by equivalences does not change the norm. -/
theorem l2_opNorm_submatrix_equiv [DecidableEq n] {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq n'] (A : Matrix m n 𝕜) (e : m' ≃ m) (f : n' ≃ n) :
    ‖A.submatrix e f‖ = ‖A‖ := by
  refine le_antisymm (l2_opNorm_submatrix_equiv_le A e f) ?_
  have h := l2_opNorm_submatrix_equiv_le (A.submatrix e f) e.symm f.symm
  rwa [submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, submatrix_id_id] at h

/-! ## The operator norm block by block -/

/-- **Block operator-norm bound.** Let `βm` and `βn` label the rows and the columns of `A` by
blocks, with every nonzero entry of `A` inside a block. If the restriction of `A` to every block,
a matrix indexed by the rows and the columns of that block, has norm at most `c`, then
`‖A‖ ≤ c`. -/
theorem l2_opNorm_le_of_submatrix_le [DecidableEq n] {κ : Type*} [DecidableEq κ]
    {A : Matrix m n 𝕜} (βm : m → κ) (βn : n → κ) (hA : ∀ i j, A i j ≠ 0 → βm i = βn j)
    {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ k, ‖A.submatrix (Subtype.val : {i // βm i = k} → m)
      (Subtype.val : {j // βn j = k} → n)‖ ≤ c) :
    ‖A‖ ≤ c := by
  refine l2_opNorm_le_of_sum_norm_mulVec_sq_le hc fun v ↦ ?_
  have hrow (k : κ) (i : {i // βm i = k}) :
      (A *ᵥ v) i.1 = (A.submatrix Subtype.val (Subtype.val : {j // βn j = k} → n) *ᵥ
        fun j ↦ v j.1) i := by
    simp only [mulVec, dotProduct, submatrix_apply]
    rw [← Finset.sum_subtype (Finset.univ.filter fun j ↦ βn j = k) (by simp)
      (fun j ↦ A i.1 j * v j), Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs with h
    · rfl
    · have h0 : A i.1 j = 0 := by
        by_contra h'
        exact h ((hA _ _ h').symm.trans i.2)
      simp [h0]
  have hblk (k : κ) : ∑ i ∈ Finset.univ.filter (fun i ↦ βm i = k), ‖(A *ᵥ v) i‖ ^ 2 ≤
      c ^ 2 * ∑ j ∈ Finset.univ.filter (fun j ↦ βn j = k), ‖v j‖ ^ 2 := by
    rw [Finset.sum_subtype (p := fun i ↦ βm i = k) (F := inferInstance) _ (fun i ↦ by simp)
        (fun i ↦ ‖(A *ᵥ v) i‖ ^ 2),
      Finset.sum_subtype (p := fun j ↦ βn j = k) (F := inferInstance) _ (fun j ↦ by simp)
        (fun j ↦ ‖v j‖ ^ 2)]
    simp only [hrow k]
    exact (sum_norm_mulVec_sq_le _ _).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hblock k) 2) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ.image βm ∪ Finset.univ.image βn) (g := βm)
      (fun i _ ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))),
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ.image βm ∪ Finset.univ.image βn) (g := βn)
      (fun j _ ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))),
    Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ hblk k

/-! ## A two-by-two block bound -/

omit [Fintype m] [Fintype n] in
/-- Cauchy–Schwarz for a finite sum of products. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (f g : ι → 𝕜) :
    ‖∑ j ∈ s, f j * g j‖ ^ 2 ≤ (∑ j ∈ s, ‖f j‖ ^ 2) * ∑ j ∈ s, ‖g j‖ ^ 2 := by
  have h₁ : ‖∑ j ∈ s, f j * g j‖ ≤ ∑ j ∈ s, ‖f j‖ * ‖g j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
  exact (pow_le_pow_left₀ (norm_nonneg _) h₁ 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/-- The scalar inequality behind the norm of a two-by-two block matrix with a zero corner: with
`λ = (t + √(t² + 4 s²)) / 2`, the largest eigenvalue of `!![0, s; s, t]`, one has
`s² w² + (s u + t w)² ≤ λ² (u² + w²)` for nonnegative `s, t, u, w`. -/
theorem sq_mul_sq_add_sq_le_of_nonneg {s t u w : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s ^ 2 * w ^ 2 + (s * u + t * w) ^ 2 ≤
      ((t + √(t ^ 2 + 4 * s ^ 2)) / 2) ^ 2 * (u ^ 2 + w ^ 2) := by
  set r := √(t ^ 2 + 4 * s ^ 2) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = t ^ 2 + 4 * s ^ 2 := Real.sq_sqrt (by positivity)
  set L := (t + r) / 2 with hLdef
  have hL : L ^ 2 = t * L + s ^ 2 := by
    rw [hLdef]
    linear_combination (1 / 4 : ℝ) * hr2
  have key : L * (L ^ 2 * (u ^ 2 + w ^ 2) - (s ^ 2 * w ^ 2 + (s * u + t * w) ^ 2)) =
      t * (L * u - s * w) ^ 2 := by
    linear_combination (u ^ 2 * L + w ^ 2 * (L + t)) * hL
  rcases (show 0 ≤ L by positivity).lt_or_eq with hLpos | hL0
  · have h₁ : 0 ≤ L * (L ^ 2 * (u ^ 2 + w ^ 2) - (s ^ 2 * w ^ 2 + (s * u + t * w) ^ 2)) := by
      rw [key]
      positivity
    linarith [nonneg_of_mul_nonneg_right h₁ hLpos]
  · have ht0 : t = 0 := by linarith
    have hr0' : r = 0 := by linarith
    have hs0 : s = 0 := by nlinarith
    rw [← hL0, ht0, hs0]
    simp

/-- **Two-by-two block bound.** Let `E` vanish on the corner `pm × pn`. If the squared entries
of both off-diagonal blocks `pm × ¬pn` and `¬pm × pn` sum to at most `a`, and those of the block
`¬pm × ¬pn` to at most `d`, then `‖E‖ ≤ (√d + √(d + 4 a)) / 2`, the largest eigenvalue of
`!![0, √a; √a, √d]`. -/
theorem l2_opNorm_le_of_corner_eq_zero [DecidableEq n] {E : Matrix m n 𝕜} (pm : m → Prop)
    (pn : n → Prop) [DecidablePred pm] [DecidablePred pn] (hE : ∀ i j, pm i → pn j → E i j = 0)
    {a d : ℝ} (ha₁ : ∑ i, ∑ j, (if pm i ∧ ¬ pn j then ‖E i j‖ ^ 2 else 0) ≤ a)
    (ha₂ : ∑ i, ∑ j, (if ¬ pm i ∧ pn j then ‖E i j‖ ^ 2 else 0) ≤ a)
    (hd : ∑ i, ∑ j, (if ¬ pm i ∧ ¬ pn j then ‖E i j‖ ^ 2 else 0) ≤ d) :
    ‖E‖ ≤ (√d + √(d + 4 * a)) / 2 := by
  have hnn : ∀ (q : m → n → Prop) [∀ i j, Decidable (q i j)],
      0 ≤ ∑ i, ∑ j, (if q i j then ‖E i j‖ ^ 2 else 0) := fun q _ ↦
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
  have ha0 : 0 ≤ a := (hnn _).trans ha₁
  have hd0 : 0 ≤ d := (hnn _).trans hd
  set s := √a with hsdef
  set t := √d with htdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have has : a = s ^ 2 := (Real.sq_sqrt ha0).symm
  have hdt : d = t ^ 2 := (Real.sq_sqrt hd0).symm
  have hroot : √(d + 4 * a) = √(t ^ 2 + 4 * s ^ 2) := by rw [has, hdt]
  rw [hroot]
  refine l2_opNorm_le_of_sum_norm_mulVec_sq_le (by positivity) fun v ↦ ?_
  set vA : n → 𝕜 := fun j ↦ if pn j then v j else 0 with hvA
  set vB : n → 𝕜 := fun j ↦ if pn j then 0 else v j with hvB
  set U2 := ∑ j, ‖vA j‖ ^ 2 with hU2
  set V2 := ∑ j, ‖vB j‖ ^ 2 with hV2
  have hv : ∑ j, ‖v j‖ ^ 2 = U2 + V2 := by
    rw [hU2, hV2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hvA, hvB]
    split_ifs <;> simp
  have hsplit : ∀ i, (E *ᵥ v) i = (E *ᵥ vA) i + (E *ᵥ vB) i := by
    intro i
    rw [← Pi.add_apply, ← mulVec_add]
    congr 2
    funext j
    simp only [hvA, hvB, Pi.add_apply]
    split_ifs <;> simp
  -- Cauchy–Schwarz on each row, against the two halves of `v`.
  have hα : ∀ i, ‖(E *ᵥ vA) i‖ ^ 2 ≤ (∑ j, if pn j then ‖E i j‖ ^ 2 else 0) * U2 := by
    intro i
    have e : (E *ᵥ vA) i = ∑ j, (if pn j then E i j else 0) * vA j := by
      simp only [mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hvA]
      split_ifs <;> simp
    rw [e]
    refine (norm_sum_mul_sq_le _ _ _).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  have hβ : ∀ i, ‖(E *ᵥ vB) i‖ ^ 2 ≤ (∑ j, if pn j then 0 else ‖E i j‖ ^ 2) * V2 := by
    intro i
    have e : (E *ᵥ vB) i = ∑ j, (if pn j then 0 else E i j) * vB j := by
      simp only [mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hvB]
      split_ifs <;> simp
    rw [e]
    refine (norm_sum_mul_sq_le _ _ _).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  have hα0 : ∀ i, pm i → (E *ᵥ vA) i = 0 := by
    intro i hi
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp only [hvA]
    split_ifs with hj
    · rw [hE i j hi hj, zero_mul]
    · rw [mul_zero]
  -- The three block sums, as sums over the rows.
  have hs1 : ∑ i ∈ Finset.univ.filter pm, (∑ j, if pn j then 0 else ‖E i j‖ ^ 2) ≤ a := by
    refine le_trans (le_of_eq ?_) ha₁
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : pm i
    · simp only [hi, true_and, ↓reduceIte]
      exact Finset.sum_congr rfl fun j _ ↦ by by_cases hj : pn j <;> simp [hj]
    · simp [hi]
  have hs2 : ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i),
      (∑ j, if pn j then ‖E i j‖ ^ 2 else 0) ≤ a := by
    refine le_trans (le_of_eq ?_) ha₂
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : pm i
    · simp [hi]
    · simp only [hi, not_false_eq_true, true_and, ↓reduceIte]
  have hs3 : ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i),
      (∑ j, if pn j then 0 else ‖E i j‖ ^ 2) ≤ d := by
    refine le_trans (le_of_eq ?_) hd
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : pm i
    · simp [hi]
    · simp only [hi, not_false_eq_true, true_and, ↓reduceIte]
      exact Finset.sum_congr rfl fun j _ ↦ by by_cases hj : pn j <;> simp [hj]
  -- Rows in `pm` see only `vB`; rows outside `pm` see both halves.
  set Sα := ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i), ‖(E *ᵥ vA) i‖ ^ 2 with hSα
  set Sβ := ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i), ‖(E *ᵥ vB) i‖ ^ 2 with hSβ
  set X := ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i), ‖(E *ᵥ vA) i‖ * ‖(E *ᵥ vB) i‖ with hX
  have hU0 : 0 ≤ U2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hV0 : 0 ≤ V2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hP : ∑ i ∈ Finset.univ.filter pm, ‖(E *ᵥ v) i‖ ^ 2 ≤ a * V2 := by
    calc ∑ i ∈ Finset.univ.filter pm, ‖(E *ᵥ v) i‖ ^ 2
        ≤ ∑ i ∈ Finset.univ.filter pm, (∑ j, if pn j then 0 else ‖E i j‖ ^ 2) * V2 := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          rw [hsplit, hα0 i (Finset.mem_filter.mp hi).2, zero_add]
          exact hβ i
      _ ≤ a * V2 := by rw [← Finset.sum_mul]; gcongr
  have hSα' : Sα ≤ s ^ 2 * U2 := by
    rw [← has]
    calc Sα ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i),
          (∑ j, if pn j then ‖E i j‖ ^ 2 else 0) * U2 := Finset.sum_le_sum fun i _ ↦ hα i
      _ ≤ a * U2 := by rw [← Finset.sum_mul]; gcongr
  have hSβ' : Sβ ≤ t ^ 2 * V2 := by
    rw [← hdt]
    calc Sβ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i),
          (∑ j, if pn j then 0 else ‖E i j‖ ^ 2) * V2 := Finset.sum_le_sum fun i _ ↦ hβ i
      _ ≤ d * V2 := by rw [← Finset.sum_mul]; gcongr
  have hX2 : X ^ 2 ≤ Sα * Sβ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hNP : ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ pm i), ‖(E *ᵥ v) i‖ ^ 2 ≤ Sα + 2 * X + Sβ := by
    rw [hSα, hSβ, hX, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [hsplit]
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le ((E *ᵥ vA) i) ((E *ᵥ vB) i)) 2
    nlinarith [this]
  set u := √U2 with hudef
  set w := √V2 with hwdef
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hUu : U2 = u ^ 2 := (Real.sq_sqrt hU0).symm
  have hVw : V2 = w ^ 2 := (Real.sq_sqrt hV0).symm
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ ↦ by positivity
  have hXle : X ≤ s * u * (t * w) := by
    have h₁ : X ^ 2 ≤ (s * u * (t * w)) ^ 2 := by
      calc X ^ 2 ≤ Sα * Sβ := hX2
        _ ≤ (s ^ 2 * U2) * (t ^ 2 * V2) :=
          mul_le_mul hSα' hSβ' (Finset.sum_nonneg fun i _ ↦ by positivity) (by positivity)
        _ = (s * u * (t * w)) ^ 2 := by rw [hUu, hVw]; ring
    exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).mp h₁
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ pm, hv, hUu, hVw]
  have hpoly := sq_mul_sq_add_sq_le_of_nonneg (u := u) (w := w) hs0 ht0
  rw [has, hVw] at hP
  rw [hUu] at hSα'
  rw [hVw] at hSβ'
  nlinarith [hP, hNP, hSα', hSβ', hXle, hpoly]

/-- **Two-by-two block bound, squared.** Let `E` vanish on the corner `pm × pn`. If the squared
entries of the rows outside `pm` sum to at most `c`, and so do those of the columns outside `pn`,
then `‖E‖² ≤ 4 c / 3`. -/
theorem l2_opNorm_sq_le_of_corner_eq_zero [DecidableEq n] {E : Matrix m n 𝕜} (pm : m → Prop)
    (pn : n → Prop) [DecidablePred pm] [DecidablePred pn] (hE : ∀ i j, pm i → pn j → E i j = 0)
    {c : ℝ} (hrow : ∑ i, (if pm i then 0 else ∑ j, ‖E i j‖ ^ 2) ≤ c)
    (hcol : ∑ j, (if pn j then 0 else ∑ i, ‖E i j‖ ^ 2) ≤ c) :
    ‖E‖ ^ 2 ≤ 4 / 3 * c := by
  set s₁ := ∑ i, ∑ j, (if pm i ∧ ¬ pn j then ‖E i j‖ ^ 2 else 0) with hs₁
  set s₂ := ∑ i, ∑ j, (if ¬ pm i ∧ pn j then ‖E i j‖ ^ 2 else 0) with hs₂
  set s₃ := ∑ i, ∑ j, (if ¬ pm i ∧ ¬ pn j then ‖E i j‖ ^ 2 else 0) with hs₃
  have hrow' : s₂ + s₃ ≤ c := by
    refine le_trans (le_of_eq ?_) hrow
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    by_cases hi : pm i
    · simp [hi]
    · simp only [hi, ↓reduceIte, not_false_eq_true, true_and]
      exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
  have hcol' : s₁ + s₃ ≤ c := by
    refine le_trans (le_of_eq ?_) hcol
    rw [hs₁, hs₃, Finset.sum_comm,
      Finset.sum_comm (f := fun i j ↦ if ¬ pm i ∧ ¬ pn j then ‖E i j‖ ^ 2 else 0),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    by_cases hj : pn j
    · simp [hj]
    · simp only [hj, ↓reduceIte, not_false_eq_true, and_true]
      exact Finset.sum_congr rfl fun i _ ↦ by by_cases hi : pm i <;> simp [hi]
  have h := l2_opNorm_le_of_corner_eq_zero pm pn hE (le_max_left s₁ s₂) (le_max_right s₁ s₂)
    le_rfl
  have hnn : ∀ (q : m → n → Prop) [∀ i j, Decidable (q i j)],
      0 ≤ ∑ i, ∑ j, (if q i j then ‖E i j‖ ^ 2 else 0) := fun q _ ↦
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
  set a := max s₁ s₂
  have ha0 : 0 ≤ a := (hnn _).trans (le_max_left _ _)
  have hd0 : 0 ≤ s₃ := hnn _
  have hac : a + s₃ ≤ c := max_le_iff.mpr ⟨hcol', hrow'⟩ |> fun h ↦ by
    rcases le_total s₁ s₂ with h' | h'
    · rw [show a = s₂ from max_eq_right h']; exact hrow'
    · rw [show a = s₁ from max_eq_left h']; exact hcol'
  set s := √a
  set t := √s₃
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have has : a = s ^ 2 := (Real.sq_sqrt ha0).symm
  have hdt : s₃ = t ^ 2 := (Real.sq_sqrt hd0).symm
  set r := √(s₃ + 4 * a)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = t ^ 2 + 4 * s ^ 2 := by rw [Real.sq_sqrt (by positivity), has, hdt]
  -- `((t + r) / 2) ^ 2 ≤ 4 (s ^ 2 + t ^ 2) / 3`, from `3 t r ≤ 2 s ^ 2 + 5 t ^ 2`.
  have h3 : 3 * t * r ≤ 2 * s ^ 2 + 5 * t ^ 2 := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    nlinarith [sq_nonneg (s ^ 2 - 2 * t ^ 2)]
  calc ‖E‖ ^ 2 ≤ ((t + r) / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ 4 / 3 * (a + s₃) := by rw [has, hdt]; nlinarith
    _ ≤ 4 / 3 * c := by gcongr

/-- **Two-by-two block bound without a diagonal.** Let `E` vanish on the blocks `pm × pn` and
`¬pm × ¬pn`. If the squared entries of the rows outside `pm` sum to at most `c`, and so do those
of the columns outside `pn`, then `‖E‖² ≤ c`. -/
theorem l2_opNorm_sq_le_of_diagonal_blocks_eq_zero [DecidableEq n] {E : Matrix m n 𝕜}
    (pm : m → Prop) (pn : n → Prop) [DecidablePred pm] [DecidablePred pn]
    (hE : ∀ i j, pm i → pn j → E i j = 0) (hE' : ∀ i j, ¬ pm i → ¬ pn j → E i j = 0) {c : ℝ}
    (hrow : ∑ i, (if pm i then 0 else ∑ j, ‖E i j‖ ^ 2) ≤ c)
    (hcol : ∑ j, (if pn j then 0 else ∑ i, ‖E i j‖ ^ 2) ≤ c) :
    ‖E‖ ^ 2 ≤ c := by
  have hd : ∑ i, ∑ j, (if ¬ pm i ∧ ¬ pn j then ‖E i j‖ ^ 2 else 0) ≤ 0 :=
    le_of_eq (Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ by
      split_ifs with h
      · rw [hE' i j h.1 h.2, norm_zero]; norm_num
      · rfl)
  have h₁ : ∑ i, ∑ j, (if pm i ∧ ¬ pn j then ‖E i j‖ ^ 2 else 0) ≤ c := by
    refine le_trans (le_of_eq ?_) hcol
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : pn j
    · simp [hj]
    · simp only [hj, ↓reduceIte, not_false_eq_true, and_true]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hi : pm i
      · simp [hi]
      · simp [hi, hE' i j hi hj]
  have h₂ : ∑ i, ∑ j, (if ¬ pm i ∧ pn j then ‖E i j‖ ^ 2 else 0) ≤ c := by
    refine le_trans (le_of_eq ?_) hrow
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : pm i
    · simp [hi]
    · simp only [hi, ↓reduceIte, not_false_eq_true, true_and]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : pn j
      · simp [hj]
      · simp [hj, hE' i j hi hj]
  have h := l2_opNorm_le_of_corner_eq_zero pm pn hE h₁ h₂ hd
  have hc : 0 ≤ c := le_trans (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by
    split_ifs <;> positivity) h₁
  rw [Real.sqrt_zero, zero_add, zero_add, show (4 : ℝ) * c = 2 ^ 2 * c by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at h
  calc ‖E‖ ^ 2 ≤ (2 * √c / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = c := by rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sq_sqrt hc]

/-- The polynomial inequality `4 v² − 3 v⁴ ≤ 4 / 3`: the maximum of `4 u² v² + v⁴` on the unit
circle `u² + v² = 1` is `4 / 3`, which is where the constant `4 / 3` of
`Matrix.l2_opNorm_sq_le_of_corner_eq_zero` comes from. -/
theorem four_mul_sq_sub_three_mul_pow_four_le (v : ℝ) : 4 * v ^ 2 - 3 * v ^ 4 ≤ 4 / 3 := by
  nlinarith [sq_nonneg (v ^ 2 - 2 / 3)]

/-! ## Orthogonal domains and ranges -/

end Matrix

open scoped InnerProductSpace in
/-- **Orthogonal domains and ranges.** Let `R` be an orthogonal projection, given by
`⟪R x, x - R x⟫ = 0`, and let `A` factor through `R` and `B` vanish on its range. If the ranges of
`A` and `B` are orthogonal, then `‖A + B‖ ≤ max ‖A‖ ‖B‖`. -/
theorem ContinuousLinearMap.norm_add_le_max_of_inner_eq_zero {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A B : E →L[𝕜] F} {R : E →L[𝕜] E} (hR : ∀ x, ⟪R x, x - R x⟫_𝕜 = 0)
    (hA : ∀ x, A (R x) = A x) (hB : ∀ x, B (R x) = 0) (hAB : ∀ x y, ⟪A x, B y⟫_𝕜 = 0) :
    ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by
  have hM : 0 ≤ max ‖A‖ ‖B‖ := le_max_of_le_left (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  set M := max ‖A‖ ‖B‖
  have hAx : ‖A x‖ ≤ M * ‖R x‖ := by
    rw [← hA x]
    exact (A.le_opNorm _).trans (by gcongr; exact le_max_left _ _)
  have hBx : ‖B x‖ ≤ M * ‖x - R x‖ := by
    have e : B x = B (x - R x) := by rw [map_sub, hB, sub_zero]
    rw [e]
    exact (B.le_opNorm _).trans (by gcongr; exact le_max_right _ _)
  have h₁ := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (A x) (B x) (hAB x x)
  have h₂ := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (R x) (x - R x) (hR x)
  rw [add_sub_cancel] at h₂
  rw [_root_.add_apply]
  have e : (M * ‖R x‖) * (M * ‖R x‖) + (M * ‖x - R x‖) * (M * ‖x - R x‖) =
      (M * ‖x‖) * (M * ‖x‖) := by
    have : (M * ‖x‖) * (M * ‖x‖) = M * M * (‖x‖ * ‖x‖) := by ring
    rw [this, h₂]
    ring
  refine (mul_self_le_mul_self_iff (norm_nonneg _) (by positivity)).mpr ?_
  rw [h₁, ← e]
  exact add_le_add (mul_self_le_mul_self (norm_nonneg _) hAx)
    (mul_self_le_mul_self (norm_nonneg _) hBx)

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

open scoped InnerProductSpace in
/-- **Orthogonal domains and ranges, for matrices.** Let `P` and `R` be orthogonal projections. If
`A = P A R` and `B = (1 - P) B (1 - R)`, so that `A` and `B` have orthogonal domains and orthogonal
ranges, then `‖A + B‖ ≤ max ‖A‖ ‖B‖`. -/
theorem l2_opNorm_add_le_max_of_isStarProjection [DecidableEq n] {P R A B : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hA : P * A * R = A)
    (hB : (1 - P) * B * (1 - R) = B) :
    ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [cstar_norm_def, cstar_norm_def A, cstar_norm_def B, map_add]
  have hadj : ∀ (M : Matrix n n 𝕜) x y,
      ⟪toEuclideanCLM (n := n) (𝕜 := 𝕜) M x, y⟫_𝕜 =
        ⟪x, toEuclideanCLM (n := n) (𝕜 := 𝕜) Mᴴ y⟫_𝕜 := by
    intro M x y
    rw [← star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hRR : R * R = R := hR.isIdempotentElem.eq
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hRs : Rᴴ = R := hR.isSelfAdjoint.star_eq
  have hPs : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hAR : A * R = A := by rw [← hA, Matrix.mul_assoc, hRR]
  have hR1 : (1 - R) * R = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hRR, sub_self]
  have hP1 : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hBR : B * R = 0 := by
    rw [← hB, Matrix.mul_assoc ((1 - P) * B) (1 - R) R, hR1, Matrix.mul_zero]
  refine ContinuousLinearMap.norm_add_le_max_of_inner_eq_zero
    (R := toEuclideanCLM (n := n) (𝕜 := 𝕜) R) (fun x ↦ ?_) (fun x ↦ ?_) (fun x ↦ ?_)
    (fun x y ↦ ?_)
  · rw [hadj, hRs, map_sub, ← mul_apply_eq_comp, ← map_mul, hRR, sub_self,
      inner_zero_right]
  · rw [← mul_apply_eq_comp, ← map_mul, hAR]
  · rw [← mul_apply_eq_comp, ← map_mul, hBR, map_zero,
      _root_.zero_apply]
  · have e : Aᴴ * B = 0 := by
      rw [← hA, ← hB, conjTranspose_mul, conjTranspose_mul, hPs]
      have : P * ((1 - P) * B * (1 - R)) = 0 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.zero_mul, Matrix.zero_mul]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, this, Matrix.mul_zero, Matrix.mul_zero]
    rw [hadj, ← mul_apply_eq_comp, ← map_mul, e, map_zero,
      _root_.zero_apply, inner_zero_right]

end Matrix
