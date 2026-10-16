/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.MatrixMap.ProjectorEvent
public import VCVio.Quantum.Oracle.Compressed.BinaryPartition
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Database events of a query computation with a truncated compressed oracle

Let `π` label the databases and let `Q = P^(i) ⊗ 1_E` project the joint register onto the
databases of label `i`. A computation queries, at its `j`-th step, the truncated compressed oracle
`O^(t) ⊗ 1_E` on the selectors of a set `S`, and on the other selectors applies contractions that
commute with `Q`, such as other oracles that do not touch the database. If the adversary operations
commute with `Q` and the initial state has no database of label `i`, then the squared projected
mass of the final state, which is the probability that the final database has label `i` when the
initial state is normalized, satisfies
`‖Q ψ_q‖² ≤ 6 I (∑ j < q, √m_j)² ≤ 6 q I w`,
where `I = I(π, t)` is the instability ([CDHZ, Definition 5.3]), `m_j` is the mass of the state
on the selectors of `S` before the `j`-th step, and `w = ∑ j, m_j` is the total query mass.

## Comparison with [CDHZ]

The bound combines the event bound `Matrix.sum_norm_blockDiagonal_mulVec_sq_le_sq_sum_sqrt` with
the projector commutator bound
`Quantum.l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul`, so its constant is
`6` for every labelling. The hybrid argument of [CDHZ, Lemma 5.7] through a purified binary
measurement `M` instead pays `‖[M, O^(t) ⊗ 1]‖²`: this is at most `24 I` by
`Quantum.l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul`, and at most `80 I` with
the constant of [CDHZ, Theorem 5.4]. All three constants are formalized.

[CDHZ]: A. Chiesa, Z. Di, Z. Hu and Y. Zheng, ePrint 2025/2166.

## Main results

* `Quantum.l2_opNorm_truncatedOracle_le_one`: the truncated oracle is a contraction.
* `Quantum.sum_norm_labelProjector_mulVec_sq_le_six_mul_sq_sum_sqrt`: the bound `6 I (∑ √m_j)²`.
* `Quantum.sum_norm_labelProjector_mulVec_sq_le_six_mul_mul_sum`: the bound `6 q I w`.
-/

public section

open Matrix
open OracleSpec
open scoped Matrix.Norms.L2Operator Kronecker

namespace Quantum

section contraction

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The size projector has norm at most one. -/
theorem l2_opNorm_sizeProjector_le_one (t : ℕ) : ‖sizeProjector X Y t‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (sizeProjector X Y t)
  rw [conjTranspose_sizeProjector, sizeProjector_mul_self] at h
  nlinarith [norm_nonneg (sizeProjector X Y t)]

variable [AddCommGroup Y]

/-- The truncated compressed oracle `O^(t) = P_size^(t) cO P_size^(t)` is a contraction. -/
theorem l2_opNorm_truncatedOracle_le_one (t : ℕ) : ‖truncatedOracle X Y t‖ ≤ 1 := by
  have hP := l2_opNorm_sizeProjector_le_one (X := X) (Y := Y) t
  have hO : ‖compressedOracle X Y‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self conjTranspose_compressedOracle_mul_self
  calc ‖truncatedOracle X Y t‖ ≤ ‖sizeProjector X Y t * compressedOracle X Y‖ *
        ‖sizeProjector X Y t‖ := l2_opNorm_mul _ _
    _ ≤ ‖sizeProjector X Y t‖ * ‖compressedOracle X Y‖ * ‖sizeProjector X Y t‖ := by
        gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

end contraction

section event

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] {ι : Type*} [DecidableEq ι] {E : Type*} [Fintype E]
  [DecidableEq E] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The projector onto the databases of label `i` commutes with the truncated oracle up to
`6 I(π, t)`, also when tensored with the identity of another register `E`. -/
theorem l2_opNorm_labelProjector_kronecker_commutator_truncatedOracle_sq_le_six_mul
    (π : Database X Y → ι) (t : ℕ) (i : ι) :
    ‖labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ) *
          (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ) *
          (labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ
            (1 : Matrix E E ℂ))‖ ^ 2 ≤
      6 * (Database.instability π t).toReal := by
  have hsub : ∀ A B : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ,
      A ⊗ₖ (1 : Matrix E E ℂ) - B ⊗ₖ (1 : Matrix E E ℂ) = (A - B) ⊗ₖ (1 : Matrix E E ℂ) := by
    intro A B
    ext a b
    simp [kroneckerMap_apply, sub_mul]
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, hsub]
  exact (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_kronecker_one_le _) 2).trans
    (l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul π t i)

/-- **Database events of a query computation, with the constant `6`.** Let `ψ (j + 1) =
A j (blockDiagonal (T j) ψ j)` for `j < q`, where the selector register `κ` chooses the operation
`T j k` on the joint register `((X × Y) × Database X Y) × E`. Suppose that the selectors in `S`
query the truncated oracle `O^(t) ⊗ 1_E`, that the other selectors apply contractions commuting
with `Q = P^(i) ⊗ 1_E`, that the contractions `A j` commute with `Q` on every selector, and that
`Q` annihilates `ψ 0`. Then the squared projected mass `‖Q ψ q‖²` is at most
`6 I(π, t) (∑ j < q, √m_j)²`, where `m_j` is the mass of `ψ j` on the selectors of `S`. For a
normalized `ψ 0`, `‖Q ψ q‖²` is the probability that the final database has label `i`. -/
theorem sum_norm_labelProjector_mulVec_sq_le_six_mul_sq_sum_sqrt (π : Database X Y → ι) (t : ℕ)
    (i : ι) (S : Finset κ) (q : ℕ) (ψ : ℕ → (((X × Y) × Database X Y) × E) × κ → ℂ)
    (A : ℕ → Matrix ((((X × Y) × Database X Y) × E) × κ) ((((X × Y) × Database X Y) × E) × κ) ℂ)
    (T : ℕ → κ → Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ)
    (hA : ∀ j < q, ‖A j‖ ≤ 1)
    (hAQ : ∀ j < q, A j * blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) =
      blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) * A j)
    (hS : ∀ j < q, ∀ k ∈ S, T j k = truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ))
    (hT : ∀ j < q, ∀ k ∉ S, ‖T j k‖ ≤ 1)
    (hTQ : ∀ j < q, ∀ k ∉ S,
      labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ) * T j k =
        T j k * (labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ
          (1 : Matrix E E ℂ)))
    (hψ : ∀ j < q, ψ (j + 1) = A j *ᵥ (blockDiagonal (T j) *ᵥ ψ j))
    (h0 : blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ
      ψ 0 = 0) :
    ∑ a, ‖(blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ
          ψ q) a‖ ^ 2 ≤
      6 * (Database.instability π t).toReal *
        (∑ j ∈ Finset.range q, √(∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2)) ^ 2 := by
  set Q := labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)
  set c := 6 * (Database.instability π t).toReal with hc
  have hc₀ : 0 ≤ c := mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  have hT' : ∀ j < q, ∀ k, ‖T j k‖ ≤ 1 := by
    intro j hj k
    by_cases hk : k ∈ S
    · rw [hS j hj k hk]
      exact (l2_opNorm_kronecker_one_le _).trans (l2_opNorm_truncatedOracle_le_one t)
    · exact hT j hj k hk
  have hev := sum_norm_blockDiagonal_mulVec_sq_le_sq_sum_sqrt Q q ψ A T hA hAQ hT' hψ h0
  refine hev.trans ?_
  have hterm : ∀ j ∈ Finset.range q,
      √(∑ k, ‖Q * T j k - T j k * Q‖ ^ 2 * ∑ x, ‖ψ j (x, k)‖ ^ 2) ≤
        √c * √(∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2) := by
    intro j hj
    have hj : j < q := Finset.mem_range.mp hj
    rw [← Real.sqrt_mul hc₀, Finset.mul_sum]
    refine Real.sqrt_le_sqrt ?_
    rw [← Finset.sum_add_sum_compl S]
    have hzero : ∑ k ∈ Sᶜ, ‖Q * T j k - T j k * Q‖ ^ 2 * ∑ x, ‖ψ j (x, k)‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun k hk ↦ by
        rw [hTQ j hj k (Finset.mem_compl.mp hk), sub_self, norm_zero]
        ring
    rw [hzero, add_zero]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    rw [hS j hj k hk]
    exact mul_le_mul_of_nonneg_right
      (l2_opNorm_labelProjector_kronecker_commutator_truncatedOracle_sq_le_six_mul π t i)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  calc _ ≤ (∑ j ∈ Finset.range q, √c * √(∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _)
          (Finset.sum_le_sum hterm) 2
    _ = c * (∑ j ∈ Finset.range q, √(∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2)) ^ 2 := by
        rw [← Finset.mul_sum, mul_pow, Real.sq_sqrt hc₀]

/-- **Database events of a query computation, by the total query mass.** Under the hypotheses of
`Quantum.sum_norm_labelProjector_mulVec_sq_le_six_mul_sq_sum_sqrt`, the squared projected mass
`‖Q ψ q‖²` is at most `6 q I(π, t) w`, where `w = ∑ j < q, m_j` is the total
mass of the computation on the selectors of `S`. -/
theorem sum_norm_labelProjector_mulVec_sq_le_six_mul_mul_sum (π : Database X Y → ι) (t : ℕ)
    (i : ι) (S : Finset κ) (q : ℕ) (ψ : ℕ → (((X × Y) × Database X Y) × E) × κ → ℂ)
    (A : ℕ → Matrix ((((X × Y) × Database X Y) × E) × κ) ((((X × Y) × Database X Y) × E) × κ) ℂ)
    (T : ℕ → κ → Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ)
    (hA : ∀ j < q, ‖A j‖ ≤ 1)
    (hAQ : ∀ j < q, A j * blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) =
      blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) * A j)
    (hS : ∀ j < q, ∀ k ∈ S, T j k = truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ))
    (hT : ∀ j < q, ∀ k ∉ S, ‖T j k‖ ≤ 1)
    (hTQ : ∀ j < q, ∀ k ∉ S,
      labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ) * T j k =
        T j k * (labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ
          (1 : Matrix E E ℂ)))
    (hψ : ∀ j < q, ψ (j + 1) = A j *ᵥ (blockDiagonal (T j) *ᵥ ψ j))
    (h0 : blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ
      ψ 0 = 0) :
    ∑ a, ‖(blockDiagonal (fun _ ↦
        labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ
          ψ q) a‖ ^ 2 ≤
      6 * q * (Database.instability π t).toReal *
        ∑ j ∈ Finset.range q, ∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2 := by
  have h := sum_norm_labelProjector_mulVec_sq_le_six_mul_sq_sum_sqrt π t i S q ψ A T hA hAQ hS hT
    hTQ hψ h0
  have hcs : (∑ j ∈ Finset.range q, √(∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2)) ^ 2 ≤
      q * ∑ j ∈ Finset.range q, ∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range q)
      (f := fun j ↦ √(∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2))
    simp only [Finset.card_range] at this
    refine this.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ Real.sq_sqrt ?_
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hc₀ : 0 ≤ 6 * (Database.instability π t).toReal :=
    mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  calc _ ≤ _ := h
    _ ≤ 6 * (Database.instability π t).toReal *
          (q * ∑ j ∈ Finset.range q, ∑ k ∈ S, ∑ x, ‖ψ j (x, k)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hc₀
    _ = _ := by ring

end event

end Quantum
