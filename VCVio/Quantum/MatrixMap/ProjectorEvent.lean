/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.MatrixMap.OpNorm

/-!
# Events of a query computation through commutators with a projector

A query computation alternates adversary operations `A_j` and oracle queries. The register is
`n × ι`, where `ι` is a selector: at the `j`-th query the oracle `T_j i` acts on the block of
selector `i`, so the query is `blockDiagonal (T_j)`. Let `Q` be an operator on `n`, applied to every
block, that commutes with the adversary operations and annihilates the initial state (typically
the projector onto a bad event that is initially impossible). Then the final state `ψ_q`
satisfies
`‖Q ψ_q‖ ≤ ∑ j, √(∑ i, ‖[Q, T_j i]‖² m_j i)`, where `m_j i` is the mass of the state before the
`j`-th query on the selector `i`. When `Q` is an orthogonal projector and the initial state is
normalized, `‖Q ψ_q‖²` is the probability of the event, so it is at most the square of the right
side. This is an event form of the hybrid argument of Chiesa, Di, Hu and Zheng (ePrint 2025/2166,
Lemma 5.7) that avoids a purified measurement, and so saves the factor four of
`‖[M, T ⊗ 1]‖ = 2 ‖[Q, T]‖` for the binary measurement `M = Q ⊗ 1 + (1 - Q) ⊗ X`.

## Main results

* `commutator_list_prod`: the telescoping identity
  `[Q, T_1 ⋯ T_q] = ∑ j, T_1 ⋯ T_{j-1} [Q, T_j] T_{j+1} ⋯ T_q` in any ring.
* `Matrix.sum_norm_blockDiagonal_mulVec_sq_le`: a block-diagonal operator acts on the mass of each
  block separately.
* `Matrix.sqrt_sum_norm_blockDiagonal_mulVec_le_sum_sqrt`: the event bound above, and its squared
  form `Matrix.sum_norm_blockDiagonal_mulVec_sq_le_sq_sum_sqrt`.

The event bound only uses that the adversary operations and the oracles are contractions; support
projectors `P_j` of the computation can be folded into the oracles as `P_{j+1} T_j i P_j`.
-/

public section

open scoped Matrix.Norms.L2Operator

/-! ## The telescoping identity -/

/-- **The telescoping identity for commutators.** In any ring, the commutator of `Q` with a product
`T_1 ⋯ T_q` is `∑ j, T_1 ⋯ T_{j-1} [Q, T_j] T_{j+1} ⋯ T_q`. -/
theorem commutator_list_prod {R : Type*} [Ring R] (Q : R) (l : List R) :
    Q * l.prod - l.prod * Q =
      ∑ i : Fin l.length, (l.take i).prod * (Q * l[i] - l[i] * Q) * (l.drop (i + 1)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    erw [Fin.sum_univ_succ (n := l.length)]
    simp only [Fin.getElem_fin, Fin.val_zero, Fin.val_succ, List.take_zero, List.prod_nil,
      one_mul, List.getElem_cons_zero, zero_add, List.drop_zero, List.take_succ_cons,
      List.prod_cons, List.getElem_cons_succ, List.drop_succ_cons, mul_assoc,
      ← Finset.mul_sum] at ih ⊢
    rw [← ih]
    noncomm_ring

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Square roots of masses -/

section mass

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype n] in
/-- The square root of the mass of a vector satisfies the triangle inequality. -/
theorem sqrt_sum_norm_add_sq_le (v w : m → 𝕜) :
    √(∑ i, ‖(v + w) i‖ ^ 2) ≤ √(∑ i, ‖v i‖ ^ 2) + √(∑ i, ‖w i‖ ^ 2) := by
  have h := norm_add_le (WithLp.toLp 2 v : EuclideanSpace 𝕜 m) (WithLp.toLp 2 w)
  rw [← WithLp.toLp_add, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    EuclideanSpace.norm_eq] at h
  exact h

/-- An operator multiplies the square root of the mass by at most its norm. -/
theorem sqrt_sum_norm_mulVec_sq_le [DecidableEq n] (A : Matrix m n 𝕜) (v : n → 𝕜) :
    √(∑ i, ‖(A *ᵥ v) i‖ ^ 2) ≤ ‖A‖ * √(∑ j, ‖v j‖ ^ 2) := by
  calc √(∑ i, ‖(A *ᵥ v) i‖ ^ 2) ≤ √(‖A‖ ^ 2 * ∑ j, ‖v j‖ ^ 2) :=
        Real.sqrt_le_sqrt (sum_norm_mulVec_sq_le A v)
    _ = ‖A‖ * √(∑ j, ‖v j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A block-diagonal operator acts on the mass of each block separately: the mass of
`blockDiagonal M *ᵥ v` is at most `∑ i, ‖M i‖ ^ 2 m_i`, where `m_i` is the mass of `v` on the
block `i`. -/
theorem sum_norm_blockDiagonal_mulVec_sq_le [DecidableEq n] (M : ι → Matrix m n 𝕜)
    (v : n × ι → 𝕜) :
    ∑ a, ‖(blockDiagonal M *ᵥ v) a‖ ^ 2 ≤ ∑ i, ‖M i‖ ^ 2 * ∑ x, ‖v (x, i)‖ ^ 2 := by
  have hrow : ∀ x i, (blockDiagonal M *ᵥ v) (x, i) = (M i *ᵥ fun y ↦ v (y, i)) x := by
    intro x i
    simp [mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  simp only [hrow]
  exact sum_norm_mulVec_sq_le (M i) _

end mass

/-! ## The event bound -/

section event

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- **The event bound of a query computation.** Let `ψ (j + 1) = A j (blockDiagonal (T j) ψ j)`
for `j < q`, with contractions `A j` that commute with `Q` on every block and contractions
`T j i`, and let `Q` annihilate the initial state `ψ 0`. Then
`‖Q ψ q‖ ≤ ∑ j < q, √(∑ i, ‖[Q, T j i]‖² m j i)`, where `m j i = ∑ x, ‖ψ j (x, i)‖²` is the mass of
the state before the `j`-th query on the selector `i`. -/
theorem sqrt_sum_norm_blockDiagonal_mulVec_le_sum_sqrt (Q : Matrix n n 𝕜) (q : ℕ)
    (ψ : ℕ → n × ι → 𝕜) (A : ℕ → Matrix (n × ι) (n × ι) 𝕜) (T : ℕ → ι → Matrix n n 𝕜)
    (hA : ∀ j < q, ‖A j‖ ≤ 1)
    (hAQ : ∀ j < q, A j * blockDiagonal (fun _ ↦ Q) = blockDiagonal (fun _ ↦ Q) * A j)
    (hT : ∀ j < q, ∀ i, ‖T j i‖ ≤ 1)
    (hψ : ∀ j < q, ψ (j + 1) = A j *ᵥ (blockDiagonal (T j) *ᵥ ψ j))
    (h0 : blockDiagonal (fun _ ↦ Q) *ᵥ ψ 0 = 0) :
    √(∑ a, ‖(blockDiagonal (fun _ ↦ Q) *ᵥ ψ q) a‖ ^ 2) ≤
      ∑ j ∈ Finset.range q, √(∑ i, ‖Q * T j i - T j i * Q‖ ^ 2 * ∑ x, ‖ψ j (x, i)‖ ^ 2) := by
  suffices key : ∀ k ≤ q, √(∑ a, ‖(blockDiagonal (fun _ ↦ Q) *ᵥ ψ k) a‖ ^ 2) ≤
      ∑ j ∈ Finset.range k, √(∑ i, ‖Q * T j i - T j i * Q‖ ^ 2 * ∑ x, ‖ψ j (x, i)‖ ^ 2) from
    key q le_rfl
  intro k
  induction k with
  | zero => intro _; simp [h0]
  | succ k ih =>
    intro hk
    have hkq : k < q := hk
    set Qb := blockDiagonal (fun _ : ι ↦ Q) with hQb
    have hcomm : blockDiagonal (fun i ↦ Q * T k i - T k i * Q) =
        Qb * blockDiagonal (T k) - blockDiagonal (T k) * Qb := by
      rw [hQb, ← blockDiagonal_mul, ← blockDiagonal_mul, ← blockDiagonal_sub]
      rfl
    have e : Qb *ᵥ ψ (k + 1) = A k *ᵥ (blockDiagonal (T k) *ᵥ (Qb *ᵥ ψ k)) +
        A k *ᵥ (blockDiagonal (fun i ↦ Q * T k i - T k i * Q) *ᵥ ψ k) := by
      rw [hψ k hkq, mulVec_mulVec, ← hAQ k hkq, ← mulVec_mulVec, ← mulVec_add]
      congr 1
      rw [hcomm, sub_mulVec]
      simp only [mulVec_mulVec]
      abel
    have hBD : ∀ w : n × ι → 𝕜, √(∑ a, ‖(blockDiagonal (T k) *ᵥ w) a‖ ^ 2) ≤
        √(∑ a, ‖w a‖ ^ 2) := by
      intro w
      refine Real.sqrt_le_sqrt ((sum_norm_blockDiagonal_mulVec_sq_le (T k) w).trans ?_)
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      calc ‖T k i‖ ^ 2 * ∑ x, ‖w (x, i)‖ ^ 2 ≤ 1 * ∑ x, ‖w (x, i)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (hT k hkq i))
              (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        _ = ∑ x, ‖w (x, i)‖ ^ 2 := one_mul _
    have hAv : ∀ w : n × ι → 𝕜, √(∑ a, ‖(A k *ᵥ w) a‖ ^ 2) ≤ √(∑ a, ‖w a‖ ^ 2) := fun w ↦
      (sqrt_sum_norm_mulVec_sq_le (A k) w).trans
        (mul_le_of_le_one_left (Real.sqrt_nonneg _) (hA k hkq))
    rw [e, Finset.sum_range_succ]
    refine (sqrt_sum_norm_add_sq_le _ _).trans (add_le_add ?_ ?_)
    · exact ((hAv _).trans (hBD _)).trans (ih hkq.le)
    · exact (hAv _).trans (Real.sqrt_le_sqrt (sum_norm_blockDiagonal_mulVec_sq_le _ _))

/-- **The event bound of a query computation, squared.** Under the hypotheses of
`Matrix.sqrt_sum_norm_blockDiagonal_mulVec_le_sum_sqrt`, the squared projected mass `‖Q ψ q‖²` is
at most `(∑ j < q, √(∑ i, ‖[Q, T j i]‖² m j i))²`. It is the probability of the event when `Q` is
an orthogonal projector and the initial state is normalized. -/
theorem sum_norm_blockDiagonal_mulVec_sq_le_sq_sum_sqrt (Q : Matrix n n 𝕜) (q : ℕ)
    (ψ : ℕ → n × ι → 𝕜) (A : ℕ → Matrix (n × ι) (n × ι) 𝕜) (T : ℕ → ι → Matrix n n 𝕜)
    (hA : ∀ j < q, ‖A j‖ ≤ 1)
    (hAQ : ∀ j < q, A j * blockDiagonal (fun _ ↦ Q) = blockDiagonal (fun _ ↦ Q) * A j)
    (hT : ∀ j < q, ∀ i, ‖T j i‖ ≤ 1)
    (hψ : ∀ j < q, ψ (j + 1) = A j *ᵥ (blockDiagonal (T j) *ᵥ ψ j))
    (h0 : blockDiagonal (fun _ ↦ Q) *ᵥ ψ 0 = 0) :
    ∑ a, ‖(blockDiagonal (fun _ ↦ Q) *ᵥ ψ q) a‖ ^ 2 ≤
      (∑ j ∈ Finset.range q,
        √(∑ i, ‖Q * T j i - T j i * Q‖ ^ 2 * ∑ x, ‖ψ j (x, i)‖ ^ 2)) ^ 2 := by
  have h := sqrt_sum_norm_blockDiagonal_mulVec_le_sum_sqrt Q q ψ A T hA hAQ hT hψ h0
  have h₀ : 0 ≤ ∑ a, ‖(blockDiagonal (fun _ ↦ Q) *ᵥ ψ q) a‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  calc _ = √(∑ a, ‖(blockDiagonal (fun _ ↦ Q) *ᵥ ψ q) a‖ ^ 2) ^ 2 := (Real.sq_sqrt h₀).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

end event

end Matrix
