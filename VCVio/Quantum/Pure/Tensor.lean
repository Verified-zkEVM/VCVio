/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Pure.Instrument

/-!
# Operators on one register of a product

The product system `A × R` has state space `ℂ^A ⊗ ℂ^R`, in that order. The product vector
`ψ ⊗ᵥ χ` (`Quantum.tensorVec`) has coefficient `ψ a * χ r` at `(a, r)`, and Kronecker products of
operators follow the same order: `(K ⊗ₖ L) (b, s) (a, r) = K b a * L s r`.
Open the `Quantum` scope for `⊗ᵥ` and the `Kronecker` scope for `⊗ₖ`.

An operator `K` on `A` acts on `A × R` as `K ⊗ₖ 1`, leaving `R` untouched. This is the vector form
of `Quantum.DSubInstrument.frame R`, which puts the untouched register on the right: framing
neither prepares nor discards `R`, and the input may be entangled with it
(`Quantum.SubInstrument.frame_ofContraction`, `Quantum.DSubInstrument.frame_ofKraus`).

The norm of `K ⊗ₖ 1` is the norm of `K` when `R` is nonempty (`Quantum.l2_opNorm_kronecker_one`),
and at most the norm of `K` in general (`Quantum.l2_opNorm_kronecker_one_le`; it is `0` when `R`
is empty). The norm is taken over all vectors on `A × R`, entangled ones included. So
contractions, isometries and the norm estimates of `VCVio.Quantum.Pure.Norm` hold for an operator
that leaves a register untouched. `1 ⊗ₖ K`, with the untouched register on the left, has the same
norm (`Quantum.l2_opNorm_one_kronecker`).

## Main definitions

* `Quantum.tensorVec ψ χ`, written `ψ ⊗ᵥ χ`: the product vector on `A × R`.
* `Quantum.sliceRight x r`: the vector `a ↦ x (a, r)`, the coefficients of `x` at the basis state
  `r` of the right register. It is not a partial trace, and `x` may be entangled.
-/

public section

open scoped ComplexOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
open Matrix WithLp

namespace Quantum

variable {A B A' B' R S α : Type*}

/-! ## Relabelling the bases -/

section Reindex

variable [Fintype A] [Fintype B] [Fintype A'] [Fintype B']

/-- Relabelling the basis along an equivalence preserves the norm of a vector. -/
theorem norm_toLp_comp_equiv (x : EuclideanSpace ℂ A) (f : A' ≃ A) :
    ‖toLp 2 (x.ofLp ∘ f)‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt (Equiv.sum_comp f fun a ↦ ‖x.ofLp a‖ ^ 2)

variable [DecidableEq A] [DecidableEq A']

/-- Relabelling the bases of an operator along equivalences does not increase its operator
norm. -/
theorem l2_opNorm_submatrix_equiv_le (K : Matrix B A ℂ) (e : B' ≃ B) (f : A' ≃ A) :
    ‖K.submatrix e f‖ ≤ ‖K‖ := by
  refine l2_opNorm_le_of_forall (norm_nonneg K) fun x ↦ ?_
  have h : K.submatrix e f •ᵥ x =
      toLp 2 ((K •ᵥ toLp 2 (x.ofLp ∘ f.symm)).ofLp ∘ e) := by
    rw [Matrix.toLpLin_apply, Matrix.submatrix_mulVec_equiv, ofLp_applyVec]
  rw [h, norm_toLp_comp_equiv]
  exact (norm_applyVec_le K _).trans_eq (by rw [norm_toLp_comp_equiv])

/-- Relabelling the bases of an operator along equivalences preserves its operator norm. -/
theorem l2_opNorm_submatrix_equiv (K : Matrix B A ℂ) (e : B' ≃ B) (f : A' ≃ A) :
    ‖K.submatrix e f‖ = ‖K‖ := by
  refine le_antisymm (l2_opNorm_submatrix_equiv_le K e f) ?_
  have h := l2_opNorm_submatrix_equiv_le (K.submatrix e f) e.symm f.symm
  rwa [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] at h

end Reindex

/-! ## Product vectors -/

section tensorVec

/-- The product vector `ψ ⊗ χ` on the product system: its entry at `(a, r)` is `ψ a * χ r`. -/
@[expose]
def tensorVec (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R) : EuclideanSpace ℂ (A × R) :=
  toLp 2 fun x ↦ ψ.ofLp x.1 * χ.ofLp x.2

@[inherit_doc]
scoped infixl:100 " ⊗ᵥ " => tensorVec

/-- The entry of a product vector at `(a, r)` is `ψ a * χ r`. -/
@[simp]
theorem ofLp_tensorVec_apply (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R) (x : A × R) :
    (ψ ⊗ᵥ χ).ofLp x = ψ.ofLp x.1 * χ.ofLp x.2 :=
  rfl

/-- The norm of a product vector is the product of the norms. -/
@[simp]
theorem norm_tensorVec [Fintype A] [Fintype R] (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R) :
    ‖ψ ⊗ᵥ χ‖ = ‖ψ‖ * ‖χ‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp [mul_pow]

/-- The inner product of two product vectors is the product of the inner products. -/
theorem inner_tensorVec_tensorVec [Fintype A] [Fintype R] (ψ φ : EuclideanSpace ℂ A)
    (χ ξ : EuclideanSpace ℂ R) :
    ⟪ψ ⊗ᵥ χ, φ ⊗ᵥ ξ⟫_ℂ = ⟪ψ, φ⟫_ℂ * ⟪χ, ξ⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type, Finset.sum_mul_sum,
    ofLp_tensorVec_apply, map_mul]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun r _ ↦ by ring

/-- A Kronecker product of operators acts on a product vector factor by factor. -/
theorem kronecker_applyVec_tensorVec [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R]
    (K : Matrix B A ℂ) (L : Matrix S R ℂ) (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R) :
    (K ⊗ₖ L) •ᵥ (ψ ⊗ᵥ χ) = (K •ᵥ ψ) ⊗ᵥ (L •ᵥ χ) := by
  ext ⟨b, s⟩
  simp only [ofLp_applyVec, Matrix.mulVec, dotProduct, ofLp_tensorVec_apply, kronecker_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun r _ ↦ by ring

/-- An operator on the first register acts on the first factor of a product vector. -/
theorem kronecker_one_applyVec_tensorVec [Fintype A] [Fintype R] [DecidableEq A]
    [DecidableEq R] (K : Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R) :
    (K ⊗ₖ (1 : Matrix R R ℂ)) •ᵥ (ψ ⊗ᵥ χ) = (K •ᵥ ψ) ⊗ᵥ χ := by
  rw [kronecker_applyVec_tensorVec, one_applyVec]

/-- Applying a contraction to the first factor preserves subnormalization of a product vector. -/
theorem norm_applyVec_tensorVec_le_one [Fintype A] [Fintype B] [Fintype R] [DecidableEq A]
    {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1) (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R)
    (h : ‖ψ ⊗ᵥ χ‖ ≤ 1) : ‖(K •ᵥ ψ) ⊗ᵥ χ‖ ≤ 1 := by
  rw [norm_tensorVec] at h ⊢
  exact (mul_le_mul_of_nonneg_right (norm_applyVec_le_of_norm_le_one hK ψ)
    (norm_nonneg χ)).trans h

/-- An operator on the second register acts on the second factor of a product vector. -/
theorem one_kronecker_applyVec_tensorVec [Fintype A] [Fintype R] [DecidableEq A]
    [DecidableEq R] (L : Matrix S R ℂ) (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R) :
    ((1 : Matrix A A ℂ) ⊗ₖ L) •ᵥ (ψ ⊗ᵥ χ) = ψ ⊗ᵥ (L •ᵥ χ) := by
  rw [kronecker_applyVec_tensorVec, one_applyVec]

/-- The operator `|ψ ⊗ χ⟩⟨φ ⊗ ξ|` is the Kronecker product of `|ψ⟩⟨φ|` and `|χ⟩⟨ξ|`. -/
theorem ketBra_tensorVec_tensorVec (ψ : EuclideanSpace ℂ B) (φ : EuclideanSpace ℂ A)
    (χ : EuclideanSpace ℂ S) (ξ : EuclideanSpace ℂ R) :
    ketBra (ψ ⊗ᵥ χ) (φ ⊗ᵥ ξ) = ketBra ψ φ ⊗ₖ ketBra χ ξ := by
  ext ⟨b, s⟩ ⟨a, r⟩
  simp only [ketBra_apply, ofLp_tensorVec_apply, kronecker_apply, star_mul']
  ring

end tensorVec

/-! ## Slices along the second register -/

section sliceRight

/-- The component of a vector on `A × R` at the basis state `r` of the second register: the
vector on `A` with entries `x (a, r)`. -/
@[expose]
def sliceRight (x : EuclideanSpace ℂ (A × R)) (r : R) : EuclideanSpace ℂ A :=
  toLp 2 fun a ↦ x.ofLp (a, r)

/-- The entry of a slice at `a` is the entry of the vector at `(a, r)`. -/
@[simp]
theorem ofLp_sliceRight_apply (x : EuclideanSpace ℂ (A × R)) (r : R) (a : A) :
    (sliceRight x r).ofLp a = x.ofLp (a, r) :=
  rfl

/-- The squared norm of a vector on `A × R` is the sum of the squared norms of its slices. -/
theorem norm_sq_eq_sum_norm_sq_sliceRight [Fintype A] [Fintype R] (x : EuclideanSpace ℂ (A × R)) :
    ‖x‖ ^ 2 = ∑ r, ‖sliceRight x r‖ ^ 2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  exact Fintype.sum_prod_type_right _

/-- An operator on the first register acts on each slice separately. -/
theorem sliceRight_kronecker_one_applyVec [Fintype A] [Fintype R] [DecidableEq A]
    [DecidableEq R] (K : Matrix B A ℂ) (x : EuclideanSpace ℂ (A × R)) (r : R) :
    sliceRight ((K ⊗ₖ (1 : Matrix R R ℂ)) •ᵥ x) r = K •ᵥ sliceRight x r := by
  ext b
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

end sliceRight

/-! ## The norm of an operator on one register -/

section Norm

/-- An operator on the second register is the relabelling, along the swap of the two registers,
of the same operator on the first register. -/
theorem one_kronecker_eq_submatrix_swap [DecidableEq R] (K : Matrix B A ℂ) :
    (1 : Matrix R R ℂ) ⊗ₖ K =
      (K ⊗ₖ (1 : Matrix R R ℂ)).submatrix (Equiv.prodComm R B) (Equiv.prodComm R A) := by
  ext ⟨r, b⟩ ⟨s, a⟩
  simp [mul_comm]

variable [Fintype A] [Fintype B] [Fintype R] [DecidableEq A] [DecidableEq R]

/-- An operator on the first register of a product does not exceed its own norm. -/
theorem l2_opNorm_kronecker_one_le (K : Matrix B A ℂ) :
    ‖K ⊗ₖ (1 : Matrix R R ℂ)‖ ≤ ‖K‖ := by
  refine l2_opNorm_le_of_forall (norm_nonneg K) fun x ↦ ?_
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ?_
  rw [mul_pow, norm_sq_eq_sum_norm_sq_sliceRight, norm_sq_eq_sum_norm_sq_sliceRight x,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  rw [sliceRight_kronecker_one_applyVec, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_applyVec_le K _) 2

/-- An operator on the first register of a product with a nonempty second register has its own
norm. On an empty second register the product system is empty and the norm is zero. -/
theorem l2_opNorm_kronecker_one [Nonempty R] (K : Matrix B A ℂ) :
    ‖K ⊗ₖ (1 : Matrix R R ℂ)‖ = ‖K‖ := by
  refine le_antisymm (l2_opNorm_kronecker_one_le K) ?_
  obtain ⟨r⟩ := ‹Nonempty R›
  refine l2_opNorm_le_of_forall (norm_nonneg _) fun ψ ↦ ?_
  have h := norm_applyVec_le (K ⊗ₖ (1 : Matrix R R ℂ)) (ψ ⊗ᵥ EuclideanSpace.single r 1)
  rwa [kronecker_one_applyVec_tensorVec, norm_tensorVec, norm_tensorVec,
    PiLp.norm_single, norm_one, mul_one, mul_one] at h

/-- An operator on the second register of a product does not exceed its own norm. -/
theorem l2_opNorm_one_kronecker_le (K : Matrix B A ℂ) :
    ‖(1 : Matrix R R ℂ) ⊗ₖ K‖ ≤ ‖K‖ := by
  rw [one_kronecker_eq_submatrix_swap, l2_opNorm_submatrix_equiv]
  exact l2_opNorm_kronecker_one_le K

/-- An operator on the second register of a product with a nonempty first register has its own
norm. -/
theorem l2_opNorm_one_kronecker [Nonempty R] (K : Matrix B A ℂ) :
    ‖(1 : Matrix R R ℂ) ⊗ₖ K‖ = ‖K‖ := by
  rw [one_kronecker_eq_submatrix_swap, l2_opNorm_submatrix_equiv, l2_opNorm_kronecker_one]

end Norm

/-! ## Agreement with framing -/

namespace SubInstrument

open DSubInstrument

variable [Fintype A] [Fintype B] [DecidableEq A] (R) [Fintype R] [DecidableEq R]

/-- Framing the subinstrument of a contraction `K` by an ancilla gives the subinstrument of
`K ⊗ₖ 1`. -/
theorem frame_ofContraction (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) :
    (ofContraction K hK).frame R =
      ofContraction (K ⊗ₖ (1 : Matrix R R ℂ)) ((l2_opNorm_kronecker_one_le K).trans hK) :=
  DSubInstrument.ext <| funext fun u ↦ by
    rw [branch_frame_apply, branch_ofContraction, branch_ofContraction, MatrixMap.amplify_conj]

omit [DecidableEq R] in
/-- A framed contraction sends the pure substate of a product vector `ψ ⊗ᵥ χ` to the pure
substate of `(K •ᵥ ψ) ⊗ᵥ χ`. -/
theorem post_frame_ofContraction_ofVector_tensorVec (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (ψ : EuclideanSpace ℂ A) (χ : EuclideanSpace ℂ R) (h : ‖ψ ⊗ᵥ χ‖ ≤ 1)
    (u : PUnit) :
    ((ofContraction K hK).frame R).post (.ofVector (ψ ⊗ᵥ χ) h) u =
      .ofVector ((K •ᵥ ψ) ⊗ᵥ χ) (norm_applyVec_tensorVec_le_one hK ψ χ h) :=
  SubState.ext <| by
    classical
    rw [frame_ofContraction, post_ofContraction_ofVector, SubState.matrix_ofVector,
      SubState.matrix_ofVector, kronecker_one_applyVec_tensorVec]

end SubInstrument

namespace DSubInstrument

variable {B : α → Type*} [∀ a, Fintype (B a)] (R) [Fintype R] [DecidableEq R]

/-- The operators `K a ⊗ₖ 1` of a complete family of Kraus operators form a complete family. -/
theorem sum_conjTranspose_kronecker_one_mul_self [DecidableEq A] [Fintype α]
    {K : (a : α) → Matrix (B a) A ℂ}
    (hK : ∑ a, (K a)ᴴ * K a = 1) :
    ∑ a, (K a ⊗ₖ (1 : Matrix R R ℂ))ᴴ * (K a ⊗ₖ (1 : Matrix R R ℂ)) = 1 := by
  rw [← Matrix.one_kronecker_one, ← hK]
  ext ⟨a, r⟩ ⟨a', s⟩
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.sum_apply, kronecker_apply, Finset.sum_mul]

/-- Framing a Kraus measurement by an ancilla gives the Kraus measurement with operators
`K a ⊗ₖ 1`. -/
theorem frame_ofKraus [Fintype A] [DecidableEq A] [Fintype α]
    (K : (a : α) → Matrix (B a) A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) :
    (ofKraus K hK).frame R =
      ofKraus (fun a ↦ K a ⊗ₖ (1 : Matrix R R ℂ))
        (sum_conjTranspose_kronecker_one_mul_self R hK) :=
  DSubInstrument.ext <| funext fun a ↦ by
    rw [branch_frame_apply, branch_ofKraus_apply, branch_ofKraus_apply, MatrixMap.amplify_conj]

end DSubInstrument

namespace SubInstrument

/-- Framing a constant-output Kraus measurement tensors each operator with the identity. -/
theorem frame_ofKraus [Fintype A] [DecidableEq A] [Fintype B] [Fintype α]
    (R : Type*) [Fintype R] [DecidableEq R]
    (K : α → Matrix B A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) :
    (ofKraus K hK).frame R =
      ofKraus (fun a ↦ K a ⊗ₖ (1 : Matrix R R ℂ))
        (DSubInstrument.sum_conjTranspose_kronecker_one_mul_self R hK) :=
  DSubInstrument.frame_ofKraus R K hK

end SubInstrument

end Quantum
