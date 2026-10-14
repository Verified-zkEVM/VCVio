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

/-!
# Linear maps between matrix algebras

A finite-dimensional quantum system is presented by a basis type `A`, and its operators are the
complex matrices `Matrix A A ℂ`. `Quantum.MatrixMap A B` is the type of linear maps from the
operators on `A` to the operators on `B`.

## Main definitions

* `Quantum.MatrixMap.amplify Φ R`: the blockwise application `Φ ⊗ id_R` on a system extended by
  an ancilla with basis `R`.
* `Quantum.MatrixMap.traceRight A R`: the partial trace over the right factor of `A × R`.
* `Quantum.MatrixMap.IsCP`: complete positivity, as positivity of every finite amplification.
* `Quantum.MatrixMap.IsTP`, `Quantum.MatrixMap.IsTNI`: trace preservation, and trace
  nonincrease on positive semidefinite inputs.
* `Quantum.MatrixMap.conj K`: the Kraus map `ρ ↦ K * ρ * Kᴴ`.

Positivity is Mathlib's `Matrix.PosSemidef`, read with the `ComplexOrder` partial order on `ℂ`.
-/

public section

open scoped ComplexOrder Kronecker
open Matrix

/-- The trace of a positive semidefinite complex matrix has nonnegative real part. -/
theorem Matrix.PosSemidef.trace_re_nonneg {n : Type*} [Fintype n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ ρ.trace.re :=
  (Complex.nonneg_iff.mp hρ.trace_nonneg).1

/-- The trace of a product of two positive semidefinite complex matrices has nonnegative real
part. -/
theorem Matrix.PosSemidef.trace_mul_re_nonneg {n : Type*} [Fintype n] {P ρ : Matrix n n ℂ}
    (hP : P.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (P * ρ).trace.re := by
  classical
  open scoped MatrixOrder in
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (hP.mul_mul_conjTranspose_same Y).trace_re_nonneg

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

/-! ## Partial trace -/

/-- The partial trace over the right factor of `A × R`: the entry at `(a, a')` sums the diagonal
of the block at `(a, a')`. -/
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

/-- A matrix map is completely positive when each of its amplifications by a finite ancilla
`Fin k` sends positive semidefinite matrices to positive semidefinite matrices.

Positivity of every finite amplification is also the shape of complete positivity in Physlib's
`QuantumInfo` development, which keeps a comparison with it direct; no such comparison is
formalized here. -/
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

/-- The Kraus map `ρ ↦ K * ρ * Kᴴ` of a rectangular matrix `K`. -/
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

/-- A matrix map is trace preserving. -/
@[expose]
def IsTP (Φ : MatrixMap A B) : Prop :=
  ∀ ρ : Matrix A A ℂ, (Φ ρ).trace = ρ.trace

/-- A matrix map is trace nonincreasing on positive semidefinite inputs. -/
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

end Trace

end MatrixMap

end Quantum
