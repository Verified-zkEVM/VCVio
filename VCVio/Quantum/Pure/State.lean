/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Observe
public import VCVio.Quantum.Pure.Vector

/-!
# Pure substates

The operator `|ψ⟩⟨φ|` of two state vectors is `Quantum.ketBra ψ φ`, and the pure substate of a
subnormalized vector `ψ` is `Quantum.SubState.ofVector ψ`, with density matrix `|ψ⟩⟨ψ|` and trace
`‖ψ‖ ^ 2`. Conjugating `|ψ⟩⟨ψ|` by an operator `K` gives `|Kψ⟩⟨Kψ|` (`Quantum.conj_ketBra_self`),
which is how a statement about vectors becomes a statement about the density matrices of
`Quantum.SubInstrument`.

Vector, adjoint, and matrix-order conventions are in `VCVio.Quantum.Pure.Vector`.

## Main definitions

* `Quantum.ketBra ψ φ`: the operator `|ψ⟩⟨φ|`, as a matrix.
* `Quantum.SubState.ofVector ψ hψ`: the pure substate of a vector with `‖ψ‖ ≤ 1`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018:
  [author's PDF](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=70).
  Quantum states: Definition 2.5, PDF p. 70 (printed p. 62). PDF pages are counted from one.
-/

public section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Matrix WithLp

namespace Quantum

variable {A B C D : Type*}

/-! ## Rank-one operators -/

/-- The operator `|ψ⟩⟨φ|` from the system of `φ` to the system of `ψ`: the matrix with entries
`ψ b * conj (φ a)`. -/
@[expose]
def ketBra (ψ : EuclideanSpace ℂ B) (φ : EuclideanSpace ℂ A) : Matrix B A ℂ :=
  Matrix.vecMulVec ψ.ofLp (star φ.ofLp)

section ketBra

/-- The entry of `|ψ⟩⟨φ|` at `(b, a)` is `ψ b * conj (φ a)`. -/
@[simp]
theorem ketBra_apply (ψ : EuclideanSpace ℂ B) (φ : EuclideanSpace ℂ A) (b : B) (a : A) :
    ketBra ψ φ b a = ψ.ofLp b * star (φ.ofLp a) :=
  rfl

/-- The conjugate transpose of `|ψ⟩⟨φ|` is `|φ⟩⟨ψ|`. -/
@[simp]
theorem conjTranspose_ketBra (ψ : EuclideanSpace ℂ B) (φ : EuclideanSpace ℂ A) :
    (ketBra ψ φ)ᴴ = ketBra φ ψ := by
  ext a b
  simp [mul_comm]

/-- Multiplying `|ψ⟩⟨φ|` on the left by `K` gives `|Kψ⟩⟨φ|`. -/
theorem mul_ketBra [Fintype B] [DecidableEq B] (K : Matrix C B ℂ) (ψ : EuclideanSpace ℂ B)
    (φ : EuclideanSpace ℂ A) : K * ketBra ψ φ = ketBra (K •ᵥ ψ) φ :=
  Matrix.mul_vecMulVec ..

/-- Multiplying `|ψ⟩⟨φ|` on the right by `Kᴴ` gives `|ψ⟩⟨Kφ|`. -/
theorem ketBra_mul_conjTranspose [Fintype A] [DecidableEq A] (ψ : EuclideanSpace ℂ B)
    (φ : EuclideanSpace ℂ A) (K : Matrix C A ℂ) : ketBra ψ φ * Kᴴ = ketBra ψ (K •ᵥ φ) := by
  rw [ketBra, Matrix.vecMulVec_mul, ketBra, ofLp_applyVec, Matrix.star_mulVec]

/-- Conjugating `|ψ⟩⟨φ|` by two operators gives `|Kψ⟩⟨Lφ|`. -/
theorem mul_ketBra_mul_conjTranspose [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (K : Matrix C B ℂ) (L : Matrix D A ℂ) (ψ : EuclideanSpace ℂ B) (φ : EuclideanSpace ℂ A) :
    K * ketBra ψ φ * Lᴴ = ketBra (K •ᵥ ψ) (L •ᵥ φ) := by
  rw [mul_ketBra, ketBra_mul_conjTranspose]

/-- The Kraus map of `K` sends `|ψ⟩⟨ψ|` to `|Kψ⟩⟨Kψ|`. -/
theorem conj_ketBra_self [Fintype A] [DecidableEq A] (K : Matrix B A ℂ)
    (ψ : EuclideanSpace ℂ A) : MatrixMap.conj K (ketBra ψ ψ) = ketBra (K •ᵥ ψ) (K •ᵥ ψ) :=
  mul_ketBra_mul_conjTranspose K K ψ ψ

/-- The operator `|ψ⟩⟨φ|` sends `χ` to `⟪φ, χ⟫ • ψ`. -/
theorem ketBra_applyVec [Fintype A] [DecidableEq A] (ψ : EuclideanSpace ℂ B)
    (φ χ : EuclideanSpace ℂ A) : ketBra ψ φ •ᵥ χ = ⟪φ, χ⟫_ℂ • ψ := by
  ext b
  simp [ketBra, Matrix.vecMulVec_mulVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
    mul_comm]

/-- The trace of `|ψ⟩⟨φ|` is the inner product `⟪φ, ψ⟫`. -/
theorem trace_ketBra [Fintype A] (ψ φ : EuclideanSpace ℂ A) : (ketBra ψ φ).trace = ⟪φ, ψ⟫_ℂ := by
  rw [ketBra, Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct]

/-- The trace of `|ψ⟩⟨ψ|` is the squared norm of `ψ`. -/
theorem trace_ketBra_self [Fintype A] (ψ : EuclideanSpace ℂ A) :
    (ketBra ψ ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_ketBra, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The real part of the trace of `|ψ⟩⟨ψ|` is the squared norm of `ψ`. -/
@[simp]
theorem trace_re_ketBra_self [Fintype A] (ψ : EuclideanSpace ℂ A) :
    (ketBra ψ ψ).trace.re = ‖ψ‖ ^ 2 := by
  rw [trace_ketBra_self, Complex.ofReal_re]

/-- The operator `|ψ⟩⟨ψ|` is positive semidefinite. -/
theorem posSemidef_ketBra_self [Finite A] (ψ : EuclideanSpace ℂ A) : (ketBra ψ ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ.ofLp

/-- The operator `|ψ⟩⟨ψ|` does not change when `ψ` is multiplied by a phase. -/
theorem ketBra_smul_self {c : ℂ} (hc : ‖c‖ = 1) (ψ : EuclideanSpace ℂ A) :
    ketBra (c • ψ) (c • ψ) = ketBra ψ ψ := by
  ext a b
  have h : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  simp only [ketBra_apply, ofLp_smul, Pi.smul_apply, smul_eq_mul, star_mul']
  linear_combination ψ.ofLp a * star (ψ.ofLp b) * h

end ketBra

/-! ## Pure substates -/

variable [Fintype A] [Fintype B]

/-- The subnormalized pure density operator `ρψ = |ψ⟩⟨ψ|` for `‖ψ‖ ≤ 1`.
Its trace is `‖ψ‖²`, interpreted as the branch weight. A unit vector gives a normalized pure
state; zero gives the zero substate. The normalized case uses the state convention of Watrous,
Definition 2.5 (PDF p. 70); allowing trace below one records unsuccessful computation.

Vectors differing by a scalar of modulus one give the same substate (`ofVector_smul`). General
mixed substates need not have a vector representative. `conj_matrix_ofVector` proves that
`K |ψ⟩⟨ψ| K† = |Kψ⟩⟨Kψ|`. Vector and adjoint conventions are in `VCVio.Quantum.Pure.Vector`. -/
@[expose]
def SubState.ofVector (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) : SubState A where
  matrix := ketBra ψ ψ
  posSemidef := posSemidef_ketBra_self ψ
  trace_re_le_one := by
    rw [trace_re_ketBra_self]
    exact pow_le_one₀ (norm_nonneg ψ) hψ

namespace SubState

/-- The density matrix of the pure substate of `ψ` is `|ψ⟩⟨ψ|`. -/
@[simp]
theorem matrix_ofVector (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    (ofVector ψ hψ).matrix = ketBra ψ ψ :=
  rfl

/-- The trace of the pure substate of `ψ` is `‖ψ‖ ^ 2`. -/
theorem trace_re_matrix_ofVector (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    (ofVector ψ hψ).matrix.trace.re = ‖ψ‖ ^ 2 :=
  trace_re_ketBra_self ψ

/-- The Kraus map of `K` sends the pure substate of `ψ` to the pure substate of `K •ᵥ ψ`,
whenever the image is subnormalized, in particular when `K` is a contraction. -/
theorem conj_matrix_ofVector [DecidableEq A] (K : Matrix B A ℂ) (ψ : EuclideanSpace ℂ A)
    (hψ : ‖ψ‖ ≤ 1) (hKψ : ‖K •ᵥ ψ‖ ≤ 1) :
    MatrixMap.conj K (ofVector ψ hψ).matrix = (ofVector (K •ᵥ ψ) hKψ).matrix :=
  conj_ketBra_self K ψ

/-- Pure substates of vectors that differ by a phase are equal. -/
theorem ofVector_smul {c : ℂ} (hc : ‖c‖ = 1) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    ofVector (c • ψ) (by rwa [norm_smul, hc, one_mul]) = ofVector ψ hψ :=
  SubState.ext (ketBra_smul_self hc ψ)

end SubState

end Quantum
