/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import VCVio.Quantum.MatrixMap

/-!
# State vectors and operators

The core (`VCVio.Quantum.SubInstrument`) describes states by density matrices. Many quantum
query arguments are instead written with state vectors, operator norms and the triangle
inequality. This file and the others in `VCVio.Quantum.Pure` provide that vocabulary, and prove
that it agrees with the density-matrix semantics, so that a proof can argue with vectors and
conclude a statement about `outcomeMeasure`.

## Conventions

* For a finite computational basis `A`, vectors are `EuclideanSpace ℂ A`, with
  `‖ψ‖² = ∑ a, ‖ψ a‖²`. A unit vector represents a normalized pure state. A vector with
  `‖ψ‖ ≤ 1` can represent an unnormalized branch of weight `‖ψ‖²`, including the zero branch.
  Algebraic and norm lemmas assume no normalization unless their statements say so.
* An operator from `A` to `B` is the same `K : Matrix B A ℂ` that the core uses as a Kraus
  operator: `Quantum.MatrixMap.conj K` is the map `ρ ↦ KρK†`, distinct from scalar `conj`.
  It acts on column vectors,
  `(K •ᵥ ψ) b = ∑ a, K b a * ψ a`, through Mathlib's `Matrix.toEuclideanLin` (open the `Quantum`
  scope for `•ᵥ`). `L * K` applies `K` first.
* The inner product `⟪φ, ψ⟫ = ∑ a, conj (φ a) * ψ a` is conjugate-linear in its first argument,
  as is the physicists' `⟨φ|ψ⟩`.
* `K†` is the adjoint, written `Kᴴ` in Lean. Matrix inequalities in these descriptions use
  positive-semidefinite (Löwner) order: `X ≤ Y` means `Y - X` is positive semidefinite (PSD).
* Opening `Matrix.Norms.L2Operator` makes `‖K‖` the operator norm `sup_{‖ψ‖ ≤ 1} ‖K •ᵥ ψ‖`. A bare
  function `A → ℂ` carries the supremum norm instead, which is why vectors are `EuclideanSpace`.

## Why vectors and density matrices coexist

Vectors describe interference and errors that accumulate over queries: an operator `K` changes
vector distances by at most a factor `‖K‖`. A retained history with one Kraus operator at each
step can still be described by a vector. Combining different histories adds their density
matrices, and the result can be mixed, with no single-vector representative.

For example, measuring the qubit `|+⟩ = (|0⟩ + |1⟩) / √2` in the computational basis and forgetting
the outcome gives `(|0⟩⟨0| + |1⟩⟨1|) / 2 = I / 2`. This is mixed. Forgetting an outcome need not
produce a mixed state: the same measurement on `|0⟩` leaves `|0⟩⟨0|`. Density matrices let the
core compose both kinds of computation while retaining the quantum state needed by later steps.

The bridge is the pure substate `|ψ⟩⟨ψ|` (`Quantum.SubState.ofVector`, in
`VCVio.Quantum.Pure.State`) together with the Born rule for Kraus measurements
(`VCVio.Quantum.Pure.Instrument`). Both descriptions use the same operator matrices.

## Main results

* `Quantum.norm_applyVec_le` and `Quantum.l2_opNorm_le_of_forall`: the operator norm bounds the
  action, and is the least such bound.
* `Quantum.inner_applyVec_applyVec` and `Quantum.norm_sq_applyVec`: operators move through inner
  products as their conjugate transposes.
* `Quantum.posSemidef_one_sub_conjTranspose_mul_self_iff`: `K† K ≤ I` in positive-semidefinite
  order, meaning `I - K† K` is PSD, exactly when `‖K‖ ≤ 1`. Here `K†` is Lean's `Kᴴ`.
  This identifies contractions with the hypothesis of `Quantum.MatrixMap.isTNI_conj`, whose
  map is `ρ ↦ KρK†`, rather than entrywise complex conjugation.
* `Quantum.sum_norm_sq_applyVec`: a complete family of Kraus operators preserves the squared norm.
* `Quantum.norm_sq_applyVec_add_norm_sq_one_sub_applyVec`: Pythagoras for an orthogonal
  projection, which Mathlib calls a star projection (`IsStarProjection`).

Tensor order and untouched registers are in `VCVio.Quantum.Pure.Tensor`.
-/

public section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Matrix WithLp

namespace Quantum

/-- The action of an operator `K : Matrix B A ℂ` on a state vector `ψ : EuclideanSpace ℂ A`. -/
scoped notation:73 K:74 " •ᵥ " ψ:73 => Matrix.toEuclideanLin K ψ

variable {A B C ι : Type*} [Fintype A] [DecidableEq A]

/-! ## The action on vectors -/

/-- The entries of `K •ᵥ ψ` are those of the matrix-vector product. -/
theorem ofLp_applyVec (K : Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    (K •ᵥ ψ).ofLp = K *ᵥ ψ.ofLp :=
  rfl

/-- A product of operators acts as the composite of the actions. -/
theorem mul_applyVec [Fintype B] [DecidableEq B] (K : Matrix C B ℂ) (L : Matrix B A ℂ)
    (ψ : EuclideanSpace ℂ A) : (K * L) •ᵥ ψ = K •ᵥ L •ᵥ ψ :=
  congrArg (toLp 2) (Matrix.mulVec_mulVec ψ.ofLp K L).symm

/-- The identity operator acts as the identity. -/
theorem one_applyVec (ψ : EuclideanSpace ℂ A) : (1 : Matrix A A ℂ) •ᵥ ψ = ψ := by
  simp

/-- The action is additive in the operator. -/
theorem add_applyVec (K L : Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    (K + L) •ᵥ ψ = K •ᵥ ψ + L •ᵥ ψ := by
  simp

/-- The action is subtractive in the operator. -/
theorem sub_applyVec (K L : Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    (K - L) •ᵥ ψ = K •ᵥ ψ - L •ᵥ ψ := by
  simp

/-- The action commutes with finite sums of operators. -/
theorem sum_applyVec (s : Finset ι) (K : ι → Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    (∑ i ∈ s, K i) •ᵥ ψ = ∑ i ∈ s, K i •ᵥ ψ := by
  simp

/-! ## Operator norm -/

variable [Fintype B] [Fintype C]

/-- The operator norm bounds the action on vectors. -/
theorem norm_applyVec_le (K : Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    ‖K •ᵥ ψ‖ ≤ ‖K‖ * ‖ψ‖ :=
  Matrix.l2_opNorm_mulVec K ψ

/-- A contraction does not increase the norm of a vector. -/
theorem norm_applyVec_le_of_norm_le_one {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1)
    (ψ : EuclideanSpace ℂ A) : ‖K •ᵥ ψ‖ ≤ ‖ψ‖ :=
  (norm_applyVec_le K ψ).trans (mul_le_of_le_one_left (norm_nonneg ψ) hK)

/-- A contraction sends subnormalized vectors to subnormalized vectors. -/
theorem norm_applyVec_le_one {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1) {ψ : EuclideanSpace ℂ A}
    (hψ : ‖ψ‖ ≤ 1) : ‖K •ᵥ ψ‖ ≤ 1 :=
  (norm_applyVec_le_of_norm_le_one hK ψ).trans hψ

/-- A bound on the action of an operator on every vector bounds its operator norm. -/
theorem l2_opNorm_le_of_forall {K : Matrix B A ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ψ : EuclideanSpace ℂ A, ‖K •ᵥ ψ‖ ≤ c * ‖ψ‖) : ‖K‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc h

/-- A product of contractions is a contraction. -/
theorem l2_opNorm_mul_le_one [DecidableEq B] {K : Matrix C B ℂ} {L : Matrix B A ℂ} (hK : ‖K‖ ≤ 1)
    (hL : ‖L‖ ≤ 1) : ‖K * L‖ ≤ 1 :=
  (Matrix.l2_opNorm_mul K L).trans <|
    (mul_le_mul hK hL (norm_nonneg L) zero_le_one).trans_eq (one_mul 1)

/-- The identity operator has norm at most one; the norm is zero on the empty system. -/
theorem l2_opNorm_one_le : ‖(1 : Matrix A A ℂ)‖ ≤ 1 :=
  l2_opNorm_le_of_forall zero_le_one fun ψ ↦ by simp

/-! ## Inner products and the conjugate transpose -/

omit [DecidableEq A] in
/-- The real part of the inner product of a vector with itself is its squared norm. -/
theorem re_inner_self (ψ : EuclideanSpace ℂ A) : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The inner product of two images moves one operator to the other side as its conjugate
transpose. -/
theorem inner_applyVec_applyVec [DecidableEq B] (K : Matrix C A ℂ) (L : Matrix C B ℂ)
    (ψ : EuclideanSpace ℂ A) (φ : EuclideanSpace ℂ B) :
    ⟪K •ᵥ ψ, L •ᵥ φ⟫_ℂ = ⟪ψ, (Kᴴ * L) •ᵥ φ⟫_ℂ := by
  classical
  rw [mul_applyVec, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- The squared norm of an image is the expectation of `Kᴴ * K`. -/
theorem norm_sq_applyVec (K : Matrix B A ℂ) (ψ : EuclideanSpace ℂ A) :
    ‖K •ᵥ ψ‖ ^ 2 = (⟪ψ, (Kᴴ * K) •ᵥ ψ⟫_ℂ).re := by
  rw [← inner_applyVec_applyVec, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- An isometry preserves inner products. -/
theorem inner_applyVec_applyVec_of_isometry {K : Matrix B A ℂ} (hK : Kᴴ * K = 1)
    (ψ φ : EuclideanSpace ℂ A) : ⟪K •ᵥ ψ, K •ᵥ φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  rw [inner_applyVec_applyVec, hK, one_applyVec]

/-- An isometry preserves norms. -/
theorem norm_applyVec_of_isometry {K : Matrix B A ℂ} (hK : Kᴴ * K = 1)
    (ψ : EuclideanSpace ℂ A) : ‖K •ᵥ ψ‖ = ‖ψ‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_sq_applyVec, hK, one_applyVec, re_inner_self]

/-- An isometry is a contraction. -/
theorem l2_opNorm_le_one_of_isometry {K : Matrix B A ℂ} (hK : Kᴴ * K = 1) : ‖K‖ ≤ 1 :=
  l2_opNorm_le_of_forall zero_le_one fun ψ ↦ by rw [norm_applyVec_of_isometry hK, one_mul]

/-- A unitary matrix preserves norms. -/
theorem norm_applyVec_of_mem_unitaryGroup {U : Matrix A A ℂ} (hU : U ∈ Matrix.unitaryGroup A ℂ)
    (ψ : EuclideanSpace ℂ A) : ‖U •ᵥ ψ‖ = ‖ψ‖ :=
  norm_applyVec_of_isometry (Matrix.mem_unitaryGroup_iff'.mp hU) ψ

/-- A unitary matrix is a contraction. -/
theorem l2_opNorm_le_one_of_mem_unitaryGroup {U : Matrix A A ℂ}
    (hU : U ∈ Matrix.unitaryGroup A ℂ) : ‖U‖ ≤ 1 :=
  l2_opNorm_le_one_of_isometry (Matrix.mem_unitaryGroup_iff'.mp hU)

/-! ## Contractions and positivity -/

/-- The expectation of `1 - Kᴴ * K` is the squared norm lost by `K`. -/
theorem inner_one_sub_conjTranspose_mul_self_applyVec (K : Matrix B A ℂ)
    (ψ : EuclideanSpace ℂ A) :
    ⟪ψ, (1 - Kᴴ * K) •ᵥ ψ⟫_ℂ = ((‖ψ‖ ^ 2 - ‖K •ᵥ ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [sub_applyVec, inner_sub_right, ← inner_applyVec_applyVec, one_applyVec,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The quadratic form of a matrix is the expectation of its action. -/
theorem star_dotProduct_mulVec_eq_inner (M : Matrix A A ℂ) (ψ : EuclideanSpace ℂ A) :
    star ψ.ofLp ⬝ᵥ (M *ᵥ ψ.ofLp) = ⟪ψ, M •ᵥ ψ⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, ofLp_applyVec]

/-- The matrix `1 - Kᴴ * K` is positive semidefinite exactly when `K` is a contraction for the
operator norm. -/
theorem posSemidef_one_sub_conjTranspose_mul_self_iff (K : Matrix B A ℂ) :
    (1 - Kᴴ * K).PosSemidef ↔ ‖K‖ ≤ 1 := by
  have key (ψ : EuclideanSpace ℂ A) :
      0 ≤ star ψ.ofLp ⬝ᵥ ((1 - Kᴴ * K) *ᵥ ψ.ofLp) ↔ ‖K •ᵥ ψ‖ ≤ ‖ψ‖ := by
    rw [star_dotProduct_mulVec_eq_inner, inner_one_sub_conjTranspose_mul_self_applyVec,
      Complex.zero_le_real, sub_nonneg, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨fun h ↦ l2_opNorm_le_of_forall zero_le_one fun ψ ↦ ?_, fun h ↦ ⟨?_, fun x ↦ ?_⟩⟩
  · rw [one_mul]
    exact (key ψ).mp (h.2 ψ.ofLp)
  · exact Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self K)
  · exact (key (toLp 2 x)).mpr (norm_applyVec_le_of_norm_le_one h _)

/-! ## Complete families of Kraus operators -/

/-- A complete family of Kraus operators preserves the total squared norm: the squared norms of
the branches sum to the squared norm of the input. -/
theorem sum_norm_sq_applyVec [Fintype ι] {K : ι → Matrix B A ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (ψ : EuclideanSpace ℂ A) :
    ∑ i, ‖K i •ᵥ ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp_rw [norm_sq_applyVec]
  rw [← Complex.re_sum, ← inner_sum, ← sum_applyVec, hK, one_applyVec, re_inner_self]

/-- Each branch of a complete family of Kraus operators has squared norm at most that of the
input. -/
theorem norm_applyVec_le_of_sum_conjTranspose_mul_self [Fintype ι] {K : ι → Matrix B A ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (i : ι) (ψ : EuclideanSpace ℂ A) : ‖K i •ᵥ ψ‖ ≤ ‖ψ‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [← sum_norm_sq_applyVec hK ψ]
  exact Finset.single_le_sum (f := fun j ↦ ‖K j •ᵥ ψ‖ ^ 2) (fun j _ ↦ sq_nonneg _)
    (Finset.mem_univ i)

/-- Each member of a complete family of Kraus operators is a contraction. -/
theorem l2_opNorm_le_one_of_sum_conjTranspose_mul_self [Fintype ι] {K : ι → Matrix B A ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (i : ι) : ‖K i‖ ≤ 1 :=
  l2_opNorm_le_of_forall zero_le_one fun ψ ↦ by
    rw [one_mul]
    exact norm_applyVec_le_of_sum_conjTranspose_mul_self hK i ψ

/-! ## Star projections -/

/-- A star projection is a contraction. -/
theorem l2_opNorm_le_one_of_isStarProjection {P : Matrix A A ℂ} (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 :=
  hP.norm_le

/-- The squared norm of the image under a star projection is the expectation of the
projection. -/
theorem norm_sq_applyVec_of_isStarProjection {P : Matrix A A ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ A) : ‖P •ᵥ ψ‖ ^ 2 = (⟪ψ, P •ᵥ ψ⟫_ℂ).re := by
  rw [norm_sq_applyVec, ← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq,
    hP.isIdempotentElem.eq]

/-- Pythagorean identity for a star projection `P`: the squared norms of the components of a
vector in the range of `P` and in the range of `1 - P` sum to its squared norm. -/
theorem norm_sq_applyVec_add_norm_sq_one_sub_applyVec {P : Matrix A A ℂ}
    (hP : IsStarProjection P) (ψ : EuclideanSpace ℂ A) :
    ‖P •ᵥ ψ‖ ^ 2 + ‖(1 - P) •ᵥ ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [norm_sq_applyVec_of_isStarProjection hP, norm_sq_applyVec_of_isStarProjection hP.one_sub,
    sub_applyVec, one_applyVec, inner_sub_right, Complex.sub_re, re_inner_self]
  ring

/-- A star projection does not increase the norm of a vector. -/
theorem norm_applyVec_le_of_isStarProjection {P : Matrix A A ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ A) : ‖P •ᵥ ψ‖ ≤ ‖ψ‖ :=
  norm_applyVec_le_of_norm_le_one (l2_opNorm_le_one_of_isStarProjection hP) ψ

end Quantum
