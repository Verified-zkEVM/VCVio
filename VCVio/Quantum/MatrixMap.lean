/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import ToMathlib.Analysis.Matrix.PosSemidef

/-!
# Linear maps between matrix algebras

This file fixes the representation of finite-dimensional quantum systems and of the maps
between them, and the conventions every other quantum file uses.

A finite basis type `A` represents the Hilbert space `ℂ^A`, with operator algebra
`M_A = Matrix A A ℂ`. A normalized quantum state is a density matrix: a positive semidefinite
matrix `ρ` with `tr ρ = 1`. `Quantum.SubState` instead permits `tr ρ ≤ 1`, so its trace can
also record the weight of a successful branch. Positive semidefinite means that `ρ` is
Hermitian and `v†ρv ≥ 0` for every vector `v`.

`Quantum.MatrixMap A B` is a complex-linear map `Φ : M_A → M_B`. Its raw linear-map API allows
arbitrary basis types; the physical state and instrument APIs use finite bases.

## Conventions

* **Vectors are columns.** A matrix `K : Matrix B A ℂ` sends vectors on `A` to vectors on `B`:
  the output index comes first. `Kᴴ` is the conjugate transpose, written `K†` in physics.
* **Products.** The basis `A × R` represents `ℂ^A ⊗ ℂ^R`, in that order. Kronecker products
  follow the same order: `(X ⊗ₖ Y) (a, r) (b, s) = X a b * Y r s`.
* **Amplification.** `amplify Φ R` is `Φ ⊗ id_R`: the system is on the left, and the map acts
  as the identity on the reference factor `R` on the right. It acts on the whole of `M_{A × R}`,
  including on operators that are entangled across the two factors.
* **Kraus maps.** `conj K` is `ρ ↦ K ρ K†`. Here "conj" means conjugation by a matrix, not
  entrywise complex conjugation. Applying `K` and then `L` gives `conj (L * K)`.

## Physical maps

A positive map preserves positive semidefinite matrices. To act on one part of an entangled
system, it must remain positive when extended by the identity on a reference system.
For example, transposition is positive on a qubit, but `transpose ⊗ id` sends the normalized
Bell density matrix `ρ = |ψ⟩⟨ψ|`, where `|ψ⟩ = (|00⟩ + |11⟩) / √2`, to a matrix with
negative eigenvalue `-1/2`. An eigenvector is `|01⟩ - |10⟩`.
A map is *completely positive* (`IsCP`) when `Φ ⊗ id_R` is positive for every finite `R`.

Physical maps are completely positive. A completely positive map that is also trace
nonincreasing (`IsTNI`) is a *quantum operation*: it may fail, and the trace it loses is the
probability of failure. A completely positive trace-preserving (`IsTP`) map is a *quantum
channel*. `IsTNI` alone is not a physicality condition: the map `-id` satisfies it.

## Main definitions

* `Quantum.MatrixMap.amplify Φ R`: the map `Φ ⊗ id_R`, applied blockwise.
* `Quantum.MatrixMap.amplifyLeft V A`: the blockwise application `id_A ⊗ V` on the right factor
  of `A × R`. It commutes with `amplify` (`Quantum.MatrixMap.amplify_comp_amplifyLeft`).
* `Quantum.MatrixMap.IsCP`: complete positivity, as positivity of every amplification by
  `Fin k`. `Quantum.MatrixMap.IsCP.amplify_posSemidef` extends it to every finite reference.
* `Quantum.MatrixMap.IsTP`, `Quantum.MatrixMap.IsTNI`: trace preservation, and trace
  nonincrease on positive semidefinite inputs.
* `Quantum.MatrixMap.conj K`: the Kraus map `ρ ↦ K ρ K†`.
* `Quantum.MatrixMap.traceRight A R`: the partial trace over the right factor of `A × R`.

Positivity is Mathlib's `Matrix.PosSemidef`, read with the `ComplexOrder` partial order on `ℂ`.
Branch families for classical outcomes are developed in `VCVio.Quantum.MatrixMap.Family`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018.
  PDF page numbers below are 1-based. Complete positivity and trace preservation:
  equations (1.124)–(1.125), printed p. 23,
  [Chapter 1 PDF p. 23](https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf#page=23).
  Density operators as states: Definition 2.5, printed p. 62,
  [full PDF p. 70](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=70).
  Partial trace: equations (2.30)–(2.34), printed p. 68,
  [full PDF p. 76](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=76).
  Channels: Definition 2.13, printed p. 73,
  [full PDF p. 81](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=81).
  The CP–Kraus correspondence: Theorem 2.22, printed p. 82,
  [full PDF p. 90](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=90).
  This file proves the direction from Kraus form to complete positivity.
-/

public section

open scoped ComplexOrder Kronecker
open Matrix

namespace Quantum

/-- A linear map from the operators on the system with basis `A` to the operators on the system
with basis `B`. -/
abbrev MatrixMap (A B : Type*) := Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ

namespace MatrixMap

variable {A B C R S ι : Type*}

/-! ## Amplification -/

/-- The amplification `Φ ⊗ id_R` of a matrix map by an ancilla with basis `R`: the block of the
output at ancilla indices `(r, s)` is `Φ` applied to the block of the input at `(r, s)`. -/
@[expose]
def amplify (Φ : MatrixMap A B) (R : Type*) : MatrixMap (A × R) (B × R) where
  toFun ρ := Matrix.of fun x y ↦ Φ (ρ.submatrix (·, x.2) (·, y.2)) x.1 y.1
  map_add' ρ σ := by
    ext x y
    simp [Matrix.submatrix_add]
  map_smul' c ρ := by
    ext x y
    simp [Matrix.submatrix_smul]

/-- The entry of an amplified map at `(x, y)` is the entry at `(x.1, y.1)` of the map applied to
the block of the input at ancilla indices `(x.2, y.2)`. -/
@[simp]
theorem amplify_apply (Φ : MatrixMap A B) (ρ : Matrix (A × R) (A × R) ℂ) (x y : B × R) :
    Φ.amplify R ρ x y = Φ (ρ.submatrix (·, x.2) (·, y.2)) x.1 y.1 :=
  rfl

/-- The block of an amplified map at ancilla indices `(r, s)` is the map applied to the block of
the input at `(r, s)`. -/
theorem amplify_apply_submatrix (Φ : MatrixMap A B) (ρ : Matrix (A × R) (A × R) ℂ) (r s : R) :
    (Φ.amplify R ρ).submatrix (·, r) (·, s) = Φ (ρ.submatrix (·, r) (·, s)) :=
  rfl

/-- Amplifying the identity map gives the identity map. -/
@[simp]
theorem amplify_id : amplify (LinearMap.id : MatrixMap A A) R = LinearMap.id :=
  rfl

/-- Amplifying the zero map gives the zero map. -/
@[simp]
theorem amplify_zero : amplify (0 : MatrixMap A B) R = 0 :=
  rfl

/-- Amplification is additive. -/
theorem amplify_add (Φ Ψ : MatrixMap A B) :
    amplify (Φ + Ψ) R = Φ.amplify R + Ψ.amplify R :=
  rfl

/-- Amplification commutes with composition. -/
theorem amplify_comp (Ψ : MatrixMap B C) (Φ : MatrixMap A B) :
    amplify (Ψ ∘ₗ Φ) R = Ψ.amplify R ∘ₗ Φ.amplify R :=
  rfl

/-- Amplification commutes with finite sums. -/
theorem amplify_sum (s : Finset ι) (Φ : ι → MatrixMap A B) :
    amplify (∑ i ∈ s, Φ i) R = ∑ i ∈ s, (Φ i).amplify R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, amplify_add, ih]

/-- Amplification is natural in the ancilla: relabelling the ancilla of the input along
`f : R → S` relabels the ancilla of the output. -/
theorem amplify_submatrix_prodMap (Φ : MatrixMap A B) (f : R → S)
    (ρ : Matrix (A × S) (A × S) ℂ) :
    Φ.amplify R (ρ.submatrix (Prod.map id f) (Prod.map id f)) =
      (Φ.amplify S ρ).submatrix (Prod.map id f) (Prod.map id f) :=
  rfl

/-- Amplifying twice is amplifying once by the product ancilla, up to reassociation. -/
theorem amplify_amplify_apply (Φ : MatrixMap A B) (ρ : Matrix ((A × R) × S) ((A × R) × S) ℂ) :
    (Φ.amplify R).amplify S ρ =
      (Φ.amplify (R × S) (ρ.submatrix (Equiv.prodAssoc A R S).symm
        (Equiv.prodAssoc A R S).symm)).submatrix (Equiv.prodAssoc B R S)
        (Equiv.prodAssoc B R S) :=
  rfl

/-! ## Amplification on the left -/

/-- The amplification `id_A ⊗ V` of a matrix map `V` on the right factor of `A × R`: the block of
the output at indices `(a, a')` of `A` is `V` applied to the block of the input at `(a, a')`. -/
@[expose]
def amplifyLeft (V : MatrixMap R S) (A : Type*) : MatrixMap (A × R) (A × S) where
  toFun ρ := Matrix.of fun x y ↦ V (ρ.submatrix (x.1, ·) (y.1, ·)) x.2 y.2
  map_add' ρ σ := by
    ext x y
    simp [Matrix.submatrix_add]
  map_smul' c ρ := by
    ext x y
    simp [Matrix.submatrix_smul]

/-- The entry of a left amplification at `(x, y)` is the entry at `(x.2, y.2)` of the map
applied to the block of the input at `(x.1, y.1)`. -/
@[simp]
theorem amplifyLeft_apply (V : MatrixMap R S) (ρ : Matrix (A × R) (A × R) ℂ) (x y : A × S) :
    V.amplifyLeft A ρ x y = V (ρ.submatrix (x.1, ·) (y.1, ·)) x.2 y.2 :=
  rfl

/-- The block of a left amplification at `(a, a')` is the map applied to the block of the input
at `(a, a')`. -/
theorem amplifyLeft_apply_submatrix (V : MatrixMap R S) (ρ : Matrix (A × R) (A × R) ℂ)
    (a a' : A) : (V.amplifyLeft A ρ).submatrix (a, ·) (a', ·) = V (ρ.submatrix (a, ·) (a', ·)) :=
  rfl

/-- Amplifying the identity map on the left gives the identity map. -/
@[simp]
theorem amplifyLeft_id : amplifyLeft (LinearMap.id : MatrixMap R R) A = LinearMap.id :=
  rfl

/-- Amplifying the zero map on the left gives the zero map. -/
@[simp]
theorem amplifyLeft_zero : amplifyLeft (0 : MatrixMap R S) A = 0 :=
  rfl

/-- Left amplification is additive. -/
theorem amplifyLeft_add (V W : MatrixMap R S) :
    amplifyLeft (V + W) A = V.amplifyLeft A + W.amplifyLeft A :=
  rfl

/-- Left amplification commutes with composition. -/
theorem amplifyLeft_comp (W : MatrixMap S C) (V : MatrixMap R S) :
    amplifyLeft (W ∘ₗ V) A = W.amplifyLeft A ∘ₗ V.amplifyLeft A :=
  rfl

/-- A matrix map on a finite system is determined by its values on the matrix units:
`Φ ρ = ∑ a a', ρ a a' • Φ (single a a' 1)`. -/
theorem apply_eq_sum_single [Fintype A] [DecidableEq A] (Φ : MatrixMap A B)
    (ρ : Matrix A A ℂ) : Φ ρ = ∑ a, ∑ a', ρ a a' • Φ (Matrix.single a a' 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun a' _ ↦ ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Maps on different tensor factors commute: `(Φ ⊗ id) ∘ (id ⊗ V) = (id ⊗ V) ∘ (Φ ⊗ id)`. -/
theorem amplify_comp_amplifyLeft [Finite A] (Φ : MatrixMap A B) (V : MatrixMap R S) :
    Φ.amplify S ∘ₗ V.amplifyLeft A = V.amplifyLeft B ∘ₗ Φ.amplify R := by
  classical
  have := Fintype.ofFinite A
  refine LinearMap.ext fun ρ ↦ ?_
  ext ⟨b, s⟩ ⟨b', s'⟩
  have hN : (Φ.amplify R ρ).submatrix (b, ·) (b', ·) =
      ∑ a, ∑ a', Φ (Matrix.single a a' 1) b b' • ρ.submatrix (a, ·) (a', ·) := by
    ext r r'
    simp only [Matrix.submatrix_apply, amplify_apply]
    rw [apply_eq_sum_single Φ]
    simp [Matrix.sum_apply, mul_comm]
  simp only [LinearMap.comp_apply, amplify_apply, amplifyLeft_apply]
  rw [hN, apply_eq_sum_single Φ]
  simp [Matrix.sum_apply, map_sum, map_smul, mul_comm]

/-- An amplification acts on a product operator through its left factor:
`(Φ ⊗ id) (ρ ⊗ σ) = Φ ρ ⊗ σ`. -/
theorem amplify_kronecker (Φ : MatrixMap A B) (ρ : Matrix A A ℂ) (σ : Matrix R R ℂ) :
    Φ.amplify R (ρ ⊗ₖ σ) = Φ ρ ⊗ₖ σ := by
  ext ⟨b, r⟩ ⟨b', r'⟩
  have h : (ρ ⊗ₖ σ).submatrix (·, r) (·, r') = σ r r' • ρ := by
    ext a a'
    simp [mul_comm]
  rw [amplify_apply, h, map_smul]
  simp [mul_comm]

/-- A left amplification acts on a product operator through its right factor:
`(id ⊗ V) (ρ ⊗ σ) = ρ ⊗ V σ`. -/
theorem amplifyLeft_kronecker (V : MatrixMap R S) (ρ : Matrix A A ℂ) (σ : Matrix R R ℂ) :
    V.amplifyLeft A (ρ ⊗ₖ σ) = ρ ⊗ₖ V σ := by
  ext ⟨a, s⟩ ⟨a', s'⟩
  have h : (ρ ⊗ₖ σ).submatrix (a, ·) (a', ·) = ρ a a' • σ := by
    ext r r'
    simp
  rw [amplifyLeft_apply, h, map_smul]
  simp

/-! ## Partial trace -/

/-- The partial trace over the right factor of `A × R`, which discards the system `R`:
`(traceRight A R ρ) a a' = ∑ r, ρ (a, r) (a', r)`. Nothing is divided by the size of `R`, and
`traceRight A R (X ⊗ₖ Y) = tr Y • X` (`traceRight_kronecker`). This is the partial trace of
Watrous, equations (2.30)–(2.34), printed p. 68, full PDF p. 76 (see the module references),
for two factors. -/
@[expose]
def traceRight (A R : Type*) [Fintype R] : MatrixMap (A × R) A where
  toFun ρ := Matrix.of fun a a' ↦ ∑ r, ρ (a, r) (a', r)
  map_add' ρ σ := by
    ext a a'
    simp [Finset.sum_add_distrib]
  map_smul' c ρ := by
    ext a a'
    simp [Finset.mul_sum]

section traceRight

variable [Fintype R]

/-- The entry of a partial trace at `(a, a')` is the trace of the block at `(a, a')`. -/
@[simp]
theorem traceRight_apply (ρ : Matrix (A × R) (A × R) ℂ) (a a' : A) :
    traceRight A R ρ a a' = ∑ r, ρ (a, r) (a', r) :=
  rfl

/-- The partial trace sums the diagonal blocks over the traced-out factor. -/
theorem traceRight_eq_sum_submatrix (ρ : Matrix (A × R) (A × R) ℂ) :
    traceRight A R ρ = ∑ r, ρ.submatrix (·, r) (·, r) := by
  ext a a'
  simp [Matrix.sum_apply]

/-- The partial trace preserves the trace. -/
theorem trace_traceRight [Fintype A] (ρ : Matrix (A × R) (A × R) ℂ) :
    (traceRight A R ρ).trace = ρ.trace := by
  simp [Matrix.trace, Fintype.sum_prod_type]

/-- The partial trace of a positive semidefinite matrix is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.traceRight {ρ : Matrix (A × R) (A × R) ℂ}
    (hρ : ρ.PosSemidef) : (traceRight A R ρ).PosSemidef := by
  rw [traceRight_eq_sum_submatrix]
  exact Matrix.posSemidef_sum _ fun r _ ↦ hρ.submatrix _

/-- The partial trace of a product operator: `tr_R (ρ ⊗ σ) = tr σ • ρ`. -/
theorem traceRight_kronecker (ρ : Matrix A A ℂ) (σ : Matrix R R ℂ) :
    traceRight A R (ρ ⊗ₖ σ) = σ.trace • ρ := by
  ext a a'
  simp [Matrix.trace, Finset.mul_sum, mul_comm]

/-- The partial trace over `R` commutes with a map acting on the left factor. -/
theorem traceRight_comp_amplify (Φ : MatrixMap A B) :
    traceRight B R ∘ₗ Φ.amplify R = Φ ∘ₗ traceRight A R := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, traceRight_eq_sum_submatrix,
    traceRight_eq_sum_submatrix, map_sum]
  rfl

end traceRight

/-! ## Complete positivity -/

/-- Complete positivity: for every `k : ℕ` and every positive semidefinite `ρ` on `A × Fin k`,
the matrix `(Φ ⊗ id_{Fin k}) ρ` is positive semidefinite. The reference `Fin k` is the right
factor, and `ρ` may be entangled across the two factors.

Quantifying over `Fin k` loses no finite reference system: `IsCP.amplify_posSemidef` gives the
same conclusion for every finite basis type. Taking `k = 1` shows that `Φ` is positive.
See Watrous, equation (1.124), printed p. 23, Chapter 1 PDF p. 23 (see the module references). -/
@[expose]
def IsCP (Φ : MatrixMap A B) : Prop :=
  ∀ (k : ℕ) (ρ : Matrix (A × Fin k) (A × Fin k) ℂ),
    ρ.PosSemidef → (Φ.amplify (Fin k) ρ).PosSemidef

namespace IsCP

/-- A completely positive map stays positive after amplification by any finite ancilla. -/
theorem amplify_posSemidef [Finite R] {Φ : MatrixMap A B} (hΦ : Φ.IsCP)
    {ρ : Matrix (A × R) (A × R) ℂ} (hρ : ρ.PosSemidef) : (Φ.amplify R ρ).PosSemidef := by
  have h := (hΦ _ _ (hρ.submatrix (Prod.map id (Finite.equivFin R).symm))).submatrix
    (Prod.map id (Finite.equivFin R))
  rw [← amplify_submatrix_prodMap, Matrix.submatrix_submatrix] at h
  simpa [Prod.map_comp_map] using h

/-- A completely positive map is positive. -/
theorem posSemidef {Φ : MatrixMap A B} (hΦ : Φ.IsCP) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (Φ ρ).PosSemidef :=
  (hΦ 1 _ (hρ.submatrix Prod.fst)).submatrix fun b ↦ (b, (0 : Fin 1))

/-- The identity map is completely positive. -/
protected theorem id : IsCP (LinearMap.id : MatrixMap A A) :=
  fun _ _ hρ ↦ hρ

/-- The zero map is completely positive. -/
protected theorem zero : IsCP (0 : MatrixMap A B) :=
  fun _ _ _ ↦ PosSemidef.zero

/-- A composite of completely positive maps is completely positive. -/
protected theorem comp {Ψ : MatrixMap B C} {Φ : MatrixMap A B} (hΨ : Ψ.IsCP) (hΦ : Φ.IsCP) :
    IsCP (Ψ ∘ₗ Φ) :=
  fun k ρ hρ ↦ hΨ k _ (hΦ k ρ hρ)

/-- A sum of two completely positive maps is completely positive. -/
protected theorem add {Φ Ψ : MatrixMap A B} (hΦ : Φ.IsCP) (hΨ : Ψ.IsCP) : IsCP (Φ + Ψ) :=
  fun k ρ hρ ↦ (hΦ k ρ hρ).add (hΨ k ρ hρ)

/-- A finite sum of completely positive maps is completely positive. -/
protected theorem sum (s : Finset ι) {Φ : ι → MatrixMap A B} (hΦ : ∀ i ∈ s, (Φ i).IsCP) :
    IsCP (∑ i ∈ s, Φ i) := fun k ρ hρ ↦ by
  rw [amplify_sum, LinearMap.sum_apply]
  exact posSemidef_sum s fun i hi ↦ hΦ i hi k ρ hρ

/-- Amplification by a finite ancilla preserves complete positivity. -/
protected theorem amplify [Finite R] {Φ : MatrixMap A B} (hΦ : Φ.IsCP) : (Φ.amplify R).IsCP :=
  fun k ρ hρ ↦ by
    rw [amplify_amplify_apply]
    exact (hΦ.amplify_posSemidef (hρ.submatrix _)).submatrix _

end IsCP

/-! ## Kraus maps -/

/-- The Kraus map `ρ ↦ K ρ K†` of `K : Matrix B A ℂ`, which takes operators on `A` to operators
on `B`. It is completely positive (`isCP_conj`). It is trace nonincreasing when `K† K ≤ 1`
(`isTNI_conj`) and trace preserving when `K† K = 1` (`isTP_conj`). Here "conj" means
conjugation by `K`, not entrywise complex conjugation. -/
@[expose]
def conj [Fintype A] (K : Matrix B A ℂ) : MatrixMap A B where
  toFun ρ := K * ρ * Kᴴ
  map_add' ρ σ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c ρ := by simp

/-- The Kraus map of `K` sends `ρ` to `K * ρ * Kᴴ`. -/
@[simp]
theorem conj_apply [Fintype A] (K : Matrix B A ℂ) (ρ : Matrix A A ℂ) :
    conj K ρ = K * ρ * Kᴴ :=
  rfl

/-- The Kraus map of the zero matrix is the zero map. -/
@[simp]
theorem conj_zero [Fintype A] : conj (0 : Matrix B A ℂ) = 0 :=
  LinearMap.ext fun ρ ↦ by simp

/-- The Kraus map of the identity matrix is the identity map. -/
@[simp]
theorem conj_one [Fintype A] [DecidableEq A] : conj (1 : Matrix A A ℂ) = LinearMap.id :=
  LinearMap.ext fun ρ ↦ by simp

/-- The Kraus map of a product is the composite of the Kraus maps. -/
theorem conj_mul [Fintype A] [Fintype B] (K : Matrix C B ℂ) (L : Matrix B A ℂ) :
    conj (K * L) = conj K ∘ₗ conj L :=
  LinearMap.ext fun ρ ↦ by
    simp only [conj_apply, LinearMap.comp_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Amplifying a Kraus map is the Kraus map of the Kronecker product with the identity. -/
theorem amplify_conj [Fintype A] [Fintype R] [DecidableEq R] (K : Matrix B A ℂ) :
    amplify (conj K) R = conj (K ⊗ₖ (1 : Matrix R R ℂ)) := by
  refine LinearMap.ext fun ρ ↦ ?_
  ext ⟨b, r⟩ ⟨b', s⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite (starRingEnd ℂ)]

/-- Amplifying a Kraus map on the left is the Kraus map of the Kronecker product of the identity
with its operator: `id_A ⊗ conj K = conj (1 ⊗ K)`. -/
theorem amplifyLeft_conj [Fintype R] [Fintype A] [DecidableEq A] (K : Matrix S R ℂ) :
    (conj K).amplifyLeft A = conj ((1 : Matrix A A ℂ) ⊗ₖ K) := by
  refine LinearMap.ext fun ρ ↦ ?_
  ext ⟨a, s⟩ ⟨a', s'⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite (starRingEnd ℂ)]

/-- Kraus maps are completely positive. -/
theorem isCP_conj [Fintype A] [Finite B] (K : Matrix B A ℂ) : (conj K).IsCP := fun k ρ hρ ↦ by
  rw [amplify_conj, conj_apply]
  exact hρ.mul_mul_conjTranspose_same _

/-! ## Trace conditions -/

/-- The trace of an amplified map sums the traces of the map on the diagonal ancilla blocks. -/
theorem trace_amplify_apply [Fintype B] [Fintype R] (Φ : MatrixMap A B)
    (ρ : Matrix (A × R) (A × R) ℂ) :
    (Φ.amplify R ρ).trace = ∑ r, (Φ (ρ.submatrix (·, r) (·, r))).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type_right]

/-- The trace on a product basis sums the traces of the diagonal ancilla blocks. -/
theorem trace_eq_sum_trace_submatrix [Fintype A] [Fintype R] (ρ : Matrix (A × R) (A × R) ℂ) :
    ρ.trace = ∑ r, (ρ.submatrix (·, r) (·, r)).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type_right]

/-- On a positive semidefinite input, the trace of one member of a completely positive family
is at most the trace of the sum of the family. -/
theorem trace_re_apply_le_sum [Fintype B] (s : Finset ι) {Φ : ι → MatrixMap A B}
    (hcp : ∀ i ∈ s, (Φ i).IsCP) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) {i : ι} (hi : i ∈ s) :
    (Φ i ρ).trace.re ≤ ((∑ j ∈ s, Φ j) ρ).trace.re := by
  rw [LinearMap.sum_apply, Matrix.trace_sum, Complex.re_sum]
  exact Finset.single_le_sum (f := fun j ↦ (Φ j ρ).trace.re)
    (fun j hj ↦ ((hcp j hj).posSemidef hρ).trace_re_nonneg) hi

section Trace

variable [Fintype A] [Fintype B] [Fintype C]

/-- Trace preservation: `tr (Φ X) = tr X` for every matrix `X`, not only for states. Together
with complete positivity this makes `Φ` a quantum channel (Watrous, equation (1.125), printed
p. 23, Chapter 1 PDF p. 23; Definition 2.13, printed p. 73, full PDF p. 81; see the module
references). -/
@[expose]
def IsTP (Φ : MatrixMap A B) : Prop :=
  ∀ ρ : Matrix A A ℂ, (Φ ρ).trace = ρ.trace

/-- Trace nonincrease: `Re (tr (Φ ρ)) ≤ Re (tr ρ)` for every positive semidefinite `ρ`.

For a completely positive map both traces are real and nonnegative, and this is the condition
that makes `Φ` a quantum operation: the trace it loses is the probability that it fails. On its
own the predicate says nothing about positivity; `-id` satisfies it. -/
@[expose]
def IsTNI (Φ : MatrixMap A B) : Prop :=
  ∀ ρ : Matrix A A ℂ, ρ.PosSemidef → (Φ ρ).trace.re ≤ ρ.trace.re

namespace IsTP

/-- A trace-preserving map is trace nonincreasing. -/
theorem isTNI {Φ : MatrixMap A B} (hΦ : Φ.IsTP) : Φ.IsTNI :=
  fun ρ _ ↦ (congrArg Complex.re (hΦ ρ)).le

/-- The identity map is trace preserving. -/
protected theorem id : IsTP (LinearMap.id : MatrixMap A A) :=
  fun _ ↦ rfl

/-- A composite of trace-preserving maps is trace preserving. -/
protected theorem comp {Ψ : MatrixMap B C} {Φ : MatrixMap A B} (hΨ : Ψ.IsTP) (hΦ : Φ.IsTP) :
    IsTP (Ψ ∘ₗ Φ) :=
  fun ρ ↦ (hΨ (Φ ρ)).trans (hΦ ρ)

/-- Composing trace-preserving maps after the members of a family with trace-preserving sum
gives a family with trace-preserving sum. -/
theorem sum_comp (s : Finset ι) {Φ : ι → MatrixMap A B} {Ψ : ι → MatrixMap B C}
    (hΨ : ∀ i ∈ s, (Ψ i).IsTP) (hΦ : IsTP (∑ i ∈ s, Φ i)) :
    IsTP (∑ i ∈ s, Ψ i ∘ₗ Φ i) := fun ρ ↦ by
  rw [← hΦ ρ, LinearMap.sum_apply, LinearMap.sum_apply, Matrix.trace_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun i hi ↦ hΨ i hi _

/-- Amplification preserves trace preservation. -/
protected theorem amplify [Fintype R] {Φ : MatrixMap A B} (hΦ : Φ.IsTP) :
    (Φ.amplify R).IsTP := fun ρ ↦ by
  rw [trace_amplify_apply, trace_eq_sum_trace_submatrix]
  exact Finset.sum_congr rfl fun r _ ↦ hΦ _

end IsTP

namespace IsTNI

/-- The identity map is trace nonincreasing. -/
protected theorem id : IsTNI (LinearMap.id : MatrixMap A A) :=
  fun _ _ ↦ le_rfl

/-- The zero map is trace nonincreasing. -/
protected theorem zero : IsTNI (0 : MatrixMap A B) :=
  fun ρ hρ ↦ by simpa using hρ.trace_re_nonneg

/-- Trace nonincrease composes, given that the first map is completely positive. -/
protected theorem comp {Ψ : MatrixMap B C} {Φ : MatrixMap A B} (hΨ : Ψ.IsTNI) (hΦ : Φ.IsTNI)
    (hcp : Φ.IsCP) : IsTNI (Ψ ∘ₗ Φ) :=
  fun ρ hρ ↦ (hΨ (Φ ρ) (hcp.posSemidef hρ)).trans (hΦ ρ hρ)

/-- Composing trace-nonincreasing maps after the members of a completely positive family with
trace-nonincreasing sum gives a family with trace-nonincreasing sum. -/
theorem sum_comp (s : Finset ι) {Φ : ι → MatrixMap A B} {Ψ : ι → MatrixMap B C}
    (hcp : ∀ i ∈ s, (Φ i).IsCP) (hΨ : ∀ i ∈ s, (Ψ i).IsTNI) (hΦ : IsTNI (∑ i ∈ s, Φ i)) :
    IsTNI (∑ i ∈ s, Ψ i ∘ₗ Φ i) := fun ρ hρ ↦ by
  refine le_trans ?_ (hΦ ρ hρ)
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Matrix.trace_sum, Matrix.trace_sum,
    Complex.re_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun i hi ↦ hΨ i hi _ ((hcp i hi).posSemidef hρ)

/-- Amplification preserves trace nonincrease. -/
protected theorem amplify [Fintype R] {Φ : MatrixMap A B} (hΦ : Φ.IsTNI) :
    (Φ.amplify R).IsTNI := fun ρ hρ ↦ by
  rw [trace_amplify_apply, trace_eq_sum_trace_submatrix, Complex.re_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun r _ ↦ hΦ _ (hρ.submatrix _)

end IsTNI

/-- The trace of a Kraus map moves the Kraus operators to one side. -/
theorem trace_conj_apply (K : Matrix B A ℂ) (ρ : Matrix A A ℂ) :
    (conj K ρ).trace = (Kᴴ * K * ρ).trace :=
  Matrix.trace_mul_cycle K ρ Kᴴ

/-- The Kraus map of an isometry is trace preserving. -/
theorem isTP_conj [DecidableEq A] {K : Matrix B A ℂ} (h : Kᴴ * K = 1) : (conj K).IsTP :=
  fun ρ ↦ by rw [trace_conj_apply, h, Matrix.one_mul]

/-- The Kraus maps of a family of operators with `∑ i, (K i)ᴴ * K i = 1` sum to a
trace-preserving map. -/
theorem isTP_sum_conj [DecidableEq A] [Fintype ι] {K : ι → Matrix B A ℂ}
    (h : ∑ i, (K i)ᴴ * K i = 1) : IsTP (∑ i, conj (K i)) := fun ρ ↦ by
  simp_rw [LinearMap.sum_apply, Matrix.trace_sum, trace_conj_apply]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, h, Matrix.one_mul]

/-- The Kraus map of a contraction is trace nonincreasing. -/
theorem isTNI_conj [DecidableEq A] {K : Matrix B A ℂ} (h : (1 - Kᴴ * K).PosSemidef) :
    (conj K).IsTNI := fun ρ hρ ↦ by
  have := h.trace_mul_re_nonneg hρ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
  rw [trace_conj_apply]
  exact sub_nonneg.mp this

omit [Fintype A] in
/-- Tracing out the right factor discards a trace-preserving map acting on it. -/
theorem traceRight_comp_amplifyLeft [Fintype R] [Fintype S] {V : MatrixMap R S} (hV : V.IsTP) :
    traceRight A S ∘ₗ V.amplifyLeft A = traceRight A R := by
  refine LinearMap.ext fun ρ ↦ ?_
  ext a a'
  have h := hV (ρ.submatrix (a, ·) (a', ·))
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply] at h
  simpa [LinearMap.comp_apply] using h

end Trace

end MatrixMap

end Quantum
