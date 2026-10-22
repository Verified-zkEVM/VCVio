/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.Matrix.Hermitian
public import VCVio.Quantum.MatrixMap.Family

/-!
# Choi matrices, Kraus decompositions and Stinespring form

This file proves the finite-dimensional representation theorems for completely positive maps
`Φ : M_A → M_B`, where `M_A = Matrix A A ℂ` for a finite basis `A`. They are three descriptions of
the same map, each useful in a different argument:

* **Choi matrix.** One matrix `choi Φ` on `B × A` that determines `Φ`. The map `Φ` is completely
  positive exactly when `choi Φ` is positive semidefinite, so complete positivity reduces to one
  matrix condition.
* **Kraus operators.** Operators `K i : Matrix B A ℂ`, finitely many, with
  `Φ ρ = ∑ i, K i * ρ * (K i)†`. `Φ` is trace preserving exactly when `∑ i, (K i)† * K i = 1`,
  and trace nonincreasing exactly when `∑ i, (K i)† * K i ≤ 1`.
* **Stinespring operator.** One operator `S` into a larger system `B × ι`, with `Φ ρ` the partial
  trace of `S ρ S†` over the environment `ι`. `S` is an isometry for a channel and a contraction for
  a trace-nonincreasing map.

## Conventions

Vectors are columns, so `K : Matrix B A ℂ` maps `ℂ^A` to `ℂ^B`, and `K†` is its conjugate transpose.
The basis `B × A` represents `ℂ^B ⊗ ℂ^A`, in that order. With `E a a' = single a a' 1`, the Choi
matrix is output first and unnormalized:

`choi Φ = ∑ a a', Φ (E a a') ⊗ E a a'`, equivalently `choi Φ = (Φ ⊗ id_A) (|Ω⟩⟨Ω|)`,

where `|Ω⟩ = ∑ a, |a⟩ ⊗ |a⟩` is not divided by `√|A|`. This is the operator `J(Φ)` of Watrous,
equations (2.64)–(2.65), printed p. 78 / full-book PDF p. 86 (see References below). The
Stinespring operator puts the environment on the right: `S ψ = ∑ i, (K i ψ) ⊗ |i⟩`.

## How the proofs go

Complete positivity gives positivity of `(Φ ⊗ id_A) (|Ω⟩⟨Ω|)`, which is the Choi matrix
(`choi_eq_amplify`). A positive semidefinite matrix factors as `Y† * Y` (Mathlib's C⋆-algebra
factorization, with no eigenvalue decomposition), and each row of `Y` gives a Kraus operator
(`krausOfFactor`). The trace identity is `tr (Φ ρ) = tr ((∑ i, (K i)† * K i) ρ)`.
Trace preservation is tested on matrix units; trace nonincrease is tested on all positive `ρ`,
using self-duality of the positive semidefinite cone. Stacking the Kraus operators gives `S`, with
`S† S = ∑ i, (K i)† * K i`.

## Why programs need this

A subinstrument branch is a completely positive map on density matrices. Pure-state hybrid
arguments instead use operators on vectors. A Kraus representation connects these descriptions:
on input `|ψ⟩⟨ψ|`, the branch outputs `∑ i, |K i ψ⟩⟨K i ψ|`. Retaining the index `i` describes
each component by the unnormalized vector `K i ψ`; forgetting it adds the output matrices.

For two successive subinstruments with fixed output systems and finitely many intermediate
outcomes, `Quantum.DSubInstrument.branch_bind_eq_sum_conj_mul` gives path operators
`L a b j * K a i`. The rightmost operator acts first. Different paths contribute matrices, not
amplitudes, so their vectors are not added coherently. This is a two-stage identity; this file
does not construct a whole-program Kraus refinement or prove its coarse-graining law.

## Main definitions

* `Quantum.MatrixMap.choi Φ`, and `Quantum.MatrixMap.ofChoi C`, the map with Choi matrix `C`;
  together the linear equivalence `Quantum.MatrixMap.choiEquiv`.
* `Quantum.MatrixMap.krausOfFactor Y`: the Kraus operators read off the rows of a factor `Y` of the
  Choi matrix.
* `Quantum.MatrixMap.krausOps Φ hΦ`: a chosen family of Kraus operators of a completely positive
  map, indexed by `B × A`.
* `Quantum.MatrixMap.stinespring K`: the Kraus operators stacked into one operator from `A` to
  `B × ι`.

## Main results

* `Quantum.MatrixMap.ofChoi_choi`, `Quantum.MatrixMap.apply_eq_sum_choi`: a map is recovered from
  its Choi matrix.
* `Quantum.MatrixMap.isCP_iff_posSemidef_choi`: complete positivity is positivity of the Choi
  matrix.
* `Quantum.MatrixMap.isCP_iff_exists_kraus`: complete positivity is having Kraus operators
  (Choi's theorem); `Quantum.MatrixMap.IsCP.exists_kraus` gives at most `|A| * |B|` of them.
* `Quantum.MatrixMap.isTP_sum_conj_iff`, `Quantum.MatrixMap.isTNI_sum_conj_iff`: the trace
  conditions in terms of Kraus operators.
* `Quantum.MatrixMap.sum_conj_eq_traceRight_comp_conj`,
  `Quantum.MatrixMap.IsCP.exists_stinespring_of_isTNI`,
  `Quantum.MatrixMap.IsCP.exists_stinespring_of_isTP`: Stinespring form, with a contraction or an
  isometry into `B × (B × A)`.
* `Quantum.MatrixMap.IsCPTNIFamily.exists_kraus_of_fintype`: finitely many branches have Kraus
  operators jointly, with one completeness inequality.

## Not covered

* **Minimality.** The environment `B × A` and the `|A| * |B|` Kraus operators are sufficient,
  possibly nonminimal; the Kraus rank is not defined.
* **Infinitely many outcomes.** Each branch of an instrument with infinitely many outcomes has Kraus
  operators (`Quantum.MatrixMap.IsCPTNIFamily.exists_kraus`), but one Stinespring operator for all
  branches would map into the infinite-dimensional space `ℂ^B ⊗ ℓ²(outcomes × (B × A))`, and is
  not built here.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018,
  [full-book PDF](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=86). PDF locators below are
  one-based pages in this full-book PDF, not the separate chapter PDF: Choi representation,
  equations (2.64)–(2.65), printed p. 78 / PDF p. 86; Stinespring representation, equation (2.71),
  printed p. 79 / PDF p. 87; Theorem 2.22 (complete positivity, Choi positivity, Kraus and
  Stinespring forms), printed p. 82 / PDF p. 90; Theorem 2.26 (trace preservation),
  printed p. 87 / PDF p. 95; Corollary 2.27 (isometric Stinespring form of a channel),
  printed p. 89 / PDF p. 97. Theorem 2.22 assumes a nonzero map; the results here also cover the
  zero map and do not assert the theorem's rank-minimal clauses.
-/

public section

open scoped ComplexOrder
open Matrix

namespace Quantum

namespace MatrixMap

variable {A B ι : Type*}

/-! ## The Choi matrix -/

section Choi

/-- The Choi matrix of `Φ : M_A → M_B`, on `B × A` (output first):
`choi Φ (b, a) (b', a') = Φ (single a a' 1) b b'`. For finite `A` this is
`∑ a a', Φ (single a a' 1) ⊗ single a a' 1`, which is `(Φ ⊗ id_A) (|Ω⟩⟨Ω|)` for the unnormalized
`|Ω⟩ = ∑ a, |a⟩ ⊗ |a⟩` (Watrous, equation (2.65), printed p. 78 / full-book PDF p. 86;
see the module references). -/
@[expose]
def choi [DecidableEq A] (Φ : MatrixMap A B) : Matrix (B × A) (B × A) ℂ :=
  Matrix.of fun x y ↦ Φ (single x.2 y.2 1) x.1 y.1

/-- The entry of the Choi matrix at `(x, y)` is the entry at `(x.1, y.1)` of the map applied to
the matrix unit `single x.2 y.2 1`. -/
@[simp]
theorem choi_apply [DecidableEq A] (Φ : MatrixMap A B) (x y : B × A) :
    choi Φ x y = Φ (single x.2 y.2 1) x.1 y.1 :=
  rfl

/-- The linear map with Choi matrix `C`, for any `C` on `B × A`:
`ofChoi C ρ b b' = ∑ a a', ρ a a' * C (b, a) (b', a')`. It inverts `choi` (`choi_ofChoi`,
`ofChoi_choi`). Nothing is assumed of `C`; the map is completely positive exactly when `C` is
positive semidefinite (`isCP_iff_posSemidef_choi`). -/
@[expose]
def ofChoi [Fintype A] (C : Matrix (B × A) (B × A) ℂ) : MatrixMap A B where
  toFun ρ := Matrix.of fun b b' ↦ ∑ a, ∑ a', ρ a a' * C (b, a) (b', a')
  map_add' ρ σ := by
    ext b b'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c ρ := by
    ext b b'
    simp [Finset.mul_sum, mul_assoc]

/-- The entry of `ofChoi C ρ` at `(b, b')` is `∑ a, ∑ a', ρ a a' * C (b, a) (b', a')`. -/
@[simp]
theorem ofChoi_apply [Fintype A] (C : Matrix (B × A) (B × A) ℂ) (ρ : Matrix A A ℂ) (b b' : B) :
    ofChoi C ρ b b' = ∑ a, ∑ a', ρ a a' * C (b, a) (b', a') :=
  rfl

/-- The Choi matrix of `ofChoi C` is `C`. -/
@[simp]
theorem choi_ofChoi [Fintype A] [DecidableEq A] (C : Matrix (B × A) (B × A) ℂ) :
    choi (ofChoi C) = C := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.single_apply, ite_and]

/-- A matrix map is recovered from its Choi matrix by `ofChoi`. -/
@[simp]
theorem ofChoi_choi [Fintype A] [DecidableEq A] (Φ : MatrixMap A B) : ofChoi (choi Φ) = Φ := by
  refine LinearMap.ext fun ρ ↦ ?_
  have hρ : ρ = ∑ a, ∑ a', ρ a a' • single a a' (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
    simp_rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_rhs => rw [hρ]
  ext b b'
  simp only [ofChoi_apply, choi_apply, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]

/-- A matrix map is determined by its Choi matrix: the entry of `Φ ρ` at `(b, b')` is
`∑ a, ∑ a', ρ a a' * choi Φ (b, a) (b', a')`. -/
theorem apply_eq_sum_choi [Fintype A] [DecidableEq A] (Φ : MatrixMap A B) (ρ : Matrix A A ℂ)
    (b b' : B) : Φ ρ b b' = ∑ a, ∑ a', ρ a a' * choi Φ (b, a) (b', a') := by
  conv_lhs => rw [← ofChoi_choi Φ]
  rfl

/-- The Choi matrix is injective. -/
theorem choi_injective [Finite A] [DecidableEq A] :
    Function.Injective (choi : MatrixMap A B → _) := by
  cases nonempty_fintype A
  exact Function.LeftInverse.injective ofChoi_choi

/-- Two matrix maps are equal iff their Choi matrices are equal. -/
theorem choi_inj [Finite A] [DecidableEq A] {Φ Ψ : MatrixMap A B} : choi Φ = choi Ψ ↔ Φ = Ψ :=
  choi_injective.eq_iff

/-- The Choi matrix is additive. -/
theorem choi_add [DecidableEq A] (Φ Ψ : MatrixMap A B) : choi (Φ + Ψ) = choi Φ + choi Ψ := by
  ext x y
  simp

/-- The Choi matrix commutes with scalar multiplication. -/
theorem choi_smul [DecidableEq A] (c : ℂ) (Φ : MatrixMap A B) : choi (c • Φ) = c • choi Φ := by
  ext x y
  simp

/-- The Choi matrix of the zero map is zero. -/
@[simp]
theorem choi_zero [DecidableEq A] : choi (0 : MatrixMap A B) = 0 := by
  ext x y
  simp

/-- The Choi matrix commutes with finite sums. -/
theorem choi_sum [DecidableEq A] (s : Finset ι) (Φ : ι → MatrixMap A B) :
    choi (∑ i ∈ s, Φ i) = ∑ i ∈ s, choi (Φ i) := by
  ext x y
  simp [LinearMap.sum_apply, Matrix.sum_apply]

/-- The Choi matrix as a linear equivalence between matrix maps and matrices on `B × A`. -/
@[expose]
def choiEquiv [Fintype A] [DecidableEq A] : MatrixMap A B ≃ₗ[ℂ] Matrix (B × A) (B × A) ℂ where
  toFun := choi
  invFun := ofChoi
  map_add' := choi_add
  map_smul' := choi_smul
  left_inv := ofChoi_choi
  right_inv := choi_ofChoi

/-- The linear equivalence `choiEquiv` is `choi`. -/
@[simp]
theorem choiEquiv_apply [Fintype A] [DecidableEq A] (Φ : MatrixMap A B) :
    choiEquiv Φ = choi Φ :=
  rfl

/-- The inverse of `choiEquiv` is `ofChoi`. -/
@[simp]
theorem choiEquiv_symm_apply [Fintype A] [DecidableEq A] (C : Matrix (B × A) (B × A) ℂ) :
    choiEquiv.symm C = ofChoi C :=
  rfl

/-- The Choi matrix of a sum of Kraus maps: the entry at `(x, y)` is
`∑ i, K i x.1 x.2 * star (K i y.1 y.2)`. -/
theorem choi_sum_conj_apply [Fintype A] [DecidableEq A] [Fintype ι] (K : ι → Matrix B A ℂ)
    (x y : B × A) : choi (∑ i, conj (K i)) x y = ∑ i, K i x.1 x.2 * star (K i y.1 y.2) := by
  simp [LinearMap.sum_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- The Choi matrix of a map is `Φ ⊗ id_A` applied to the unnormalized maximally entangled
matrix on `A × A`. -/
theorem choi_eq_amplify [DecidableEq A] (Φ : MatrixMap A B) :
    choi Φ = Φ.amplify A (vecMulVec (fun x : A × A ↦ if x.1 = x.2 then (1 : ℂ) else 0)
      (star fun x : A × A ↦ if x.1 = x.2 then (1 : ℂ) else 0)) := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  rw [choi_apply, amplify_apply]
  refine congrArg (fun M ↦ Φ M b b') ?_
  ext x y
  simp only [Matrix.single_apply, vecMulVec_apply, Matrix.submatrix_apply, Pi.star_apply]
  split_ifs <;> simp_all

/-- The Choi matrix of a completely positive map is positive semidefinite. -/
theorem IsCP.posSemidef_choi [Finite A] [DecidableEq A] {Φ : MatrixMap A B} (hΦ : Φ.IsCP) :
    (choi Φ).PosSemidef := by
  rw [choi_eq_amplify]
  exact hΦ.amplify_posSemidef (posSemidef_vecMulVec_self_star _)

end Choi

/-! ## Kraus operators -/

section Kraus

/-- The Kraus operators read off the rows of a matrix `Y : Matrix ι (B × A) ℂ`: the operator at
`k` has entry `star (Y k (b, a))` at `(b, a)`. When `choi Φ = Yᴴ * Y`, these are Kraus operators of
`Φ` (`Quantum.MatrixMap.eq_sum_conj_krausOfFactor`). -/
@[expose]
def krausOfFactor (Y : Matrix ι (B × A) ℂ) (k : ι) : Matrix B A ℂ :=
  Matrix.of fun b a ↦ star (Y k (b, a))

/-- The entry of `krausOfFactor Y k` at `(b, a)` is `star (Y k (b, a))`. -/
@[simp]
theorem krausOfFactor_apply (Y : Matrix ι (B × A) ℂ) (k : ι) (b : B) (a : A) :
    krausOfFactor Y k b a = star (Y k (b, a)) :=
  rfl

/-- A factorization `choi Φ = Yᴴ * Y` gives Kraus operators of `Φ`, one for each row of `Y`. -/
theorem eq_sum_conj_krausOfFactor [Fintype A] [DecidableEq A] [Fintype ι] {Φ : MatrixMap A B}
    {Y : Matrix ι (B × A) ℂ} (h : choi Φ = Yᴴ * Y) : Φ = ∑ k, conj (krausOfFactor Y k) := by
  rw [← choi_inj]
  ext x y
  rw [choi_sum_conj_apply, h, Matrix.mul_apply]
  simp

/-- **Choi's theorem**, existence of Kraus operators: a completely positive map `Φ` is a sum of
Kraus maps `∑ k, conj (K k)` with `K` indexed by `B × A`. -/
theorem IsCP.exists_kraus [Fintype A] [Fintype B] {Φ : MatrixMap A B} (hΦ : Φ.IsCP) :
    ∃ K : B × A → Matrix B A ℂ, Φ = ∑ k, conj (K k) := by
  classical
  open scoped MatrixOrder in
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hΦ.posSemidef_choi.nonneg
  exact ⟨krausOfFactor Y, eq_sum_conj_krausOfFactor (by rw [hY, star_eq_conjTranspose])⟩

/-- A finite sum of Kraus maps is completely positive. -/
theorem isCP_sum_conj [Fintype A] [Finite B] [Fintype ι] (K : ι → Matrix B A ℂ) :
    IsCP (∑ i, conj (K i)) :=
  IsCP.sum _ fun i _ ↦ isCP_conj (K i)

/-- A map is completely positive if and only if its Choi matrix is positive semidefinite
(Watrous, Theorem 2.22, printed p. 82 / full-book PDF p. 90; see the module references).
Complete positivity quantifies over every reference system; the Choi matrix is a single test,
with the reference system `A`. -/
theorem isCP_iff_posSemidef_choi [Finite A] [Finite B] [DecidableEq A]
    {Φ : MatrixMap A B} : Φ.IsCP ↔ (choi Φ).PosSemidef := by
  refine ⟨IsCP.posSemidef_choi, fun h ↦ ?_⟩
  classical
  cases nonempty_fintype A
  cases nonempty_fintype B
  open scoped MatrixOrder in
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  rw [eq_sum_conj_krausOfFactor (Φ := Φ) (Y := Y) (by rw [hY, star_eq_conjTranspose])]
  exact isCP_sum_conj _

/-- **Choi's theorem.** A map `Φ : M_A → M_B` is completely positive if and only if
`Φ ρ = ∑ i, K i * ρ * (K i)†` for finitely many operators `K i : Matrix B A ℂ` (Watrous,
Theorem 2.22, printed p. 82 / full-book PDF p. 90; see the module references). The index type
may lie in any universe; `IsCP.exists_kraus` gives operators indexed by `B × A`. -/
theorem isCP_iff_exists_kraus [Fintype A] [Finite B] {Φ : MatrixMap A B} :
    Φ.IsCP ↔ ∃ (κ : Type*) (_ : Fintype κ) (K : κ → Matrix B A ℂ), Φ = ∑ i, conj (K i) := by
  refine ⟨fun hΦ ↦ ?_, fun ⟨κ, _, K, hK⟩ ↦ hK ▸ isCP_sum_conj K⟩
  cases nonempty_fintype B
  obtain ⟨K, hK⟩ := hΦ.exists_kraus
  let e := Equiv.ulift.trans (Fintype.equivFin (B × A)).symm
  exact ⟨ULift (Fin (Fintype.card (B × A))), inferInstance, K ∘ e,
    hK.trans (Fintype.sum_equiv e _ _ fun _ ↦ rfl).symm⟩

/-- A noncanonical, chosen family of Kraus operators of a completely positive map, indexed by
`B × A`. -/
noncomputable def krausOps [Fintype A] [Fintype B] (Φ : MatrixMap A B) (hΦ : Φ.IsCP) :
    B × A → Matrix B A ℂ :=
  Classical.choose hΦ.exists_kraus

/-- A completely positive map is the sum of the Kraus maps of its chosen Kraus operators. -/
theorem sum_conj_krausOps [Fintype A] [Fintype B] (Φ : MatrixMap A B) (hΦ : Φ.IsCP) :
    ∑ k, conj (krausOps Φ hΦ k) = Φ :=
  (Classical.choose_spec hΦ.exists_kraus).symm

end Kraus

/-! ## Trace conditions on Kraus operators -/

section Trace

variable [Fintype A] [Fintype B] [Fintype ι]

/-- The trace of a sum of Kraus maps pairs the input with `∑ i, (K i)ᴴ * K i`. -/
theorem trace_sum_conj_apply (K : ι → Matrix B A ℂ) (ρ : Matrix A A ℂ) :
    ((∑ i, conj (K i)) ρ).trace = ((∑ i, (K i)ᴴ * K i) * ρ).trace := by
  simp_rw [LinearMap.sum_apply, Matrix.trace_sum, trace_conj_apply]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]

omit [Fintype A] in
/-- The operator `∑ i, (K i)ᴴ * K i` is positive semidefinite. -/
theorem posSemidef_sum_conjTranspose_mul_self [Finite A] (K : ι → Matrix B A ℂ) :
    (∑ i, (K i)ᴴ * K i).PosSemidef :=
  posSemidef_sum _ fun i _ ↦ posSemidef_conjTranspose_mul_self (K i)

variable [DecidableEq A]

/-- The map `ρ ↦ ∑ i, K i * ρ * (K i)†` is trace preserving if and only if
`∑ i, (K i)† * K i = 1`, the completeness relation; it is then a quantum channel (Watrous,
Theorem 2.26, printed p. 87 / full-book PDF p. 95; see the module references). -/
theorem isTP_sum_conj_iff {K : ι → Matrix B A ℂ} :
    IsTP (∑ i, conj (K i)) ↔ ∑ i, (K i)ᴴ * K i = 1 := by
  refine ⟨fun h ↦ ?_, isTP_sum_conj⟩
  ext a a'
  have h1 := h (single a' a 1)
  rw [trace_sum_conj_apply, Matrix.trace_mul_single] at h1
  by_cases ha : a = a'
  · subst ha
    simpa [Matrix.trace_single_eq_same] using h1
  · simpa [Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm ha), Matrix.one_apply_ne ha] using h1

/-- The finite Kraus map `Φ ρ = ∑ i, K i * ρ * (K i)†` is trace nonincreasing on positive
semidefinite inputs iff `∑ i, (K i)† * K i ≤ 1` in the Loewner order, expressed here as
positive semidefiniteness of the difference. When these conditions hold, `Φ` is a quantum
operation. On a positive semidefinite input with trace one, its failure probability is
`1 - Re tr (Φ ρ) = Re tr ((1 - ∑ i, (K i)† * K i) * ρ)`.
This is the inequality counterpart of the completeness relation in `isTP_sum_conj_iff`. -/
theorem isTNI_sum_conj_iff {K : ι → Matrix B A ℂ} :
    IsTNI (∑ i, conj (K i)) ↔ (1 - ∑ i, (K i)ᴴ * K i).PosSemidef := by
  constructor
  · refine fun h ↦ (isHermitian_one.sub
      (posSemidef_sum_conjTranspose_mul_self K).isHermitian).posSemidef_of_trace_mul_re_nonneg
      fun ρ hρ ↦ ?_
    have h1 := h ρ hρ
    rw [trace_sum_conj_apply] at h1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
    exact sub_nonneg.mpr h1
  · intro h ρ hρ
    have h1 := h.trace_mul_re_nonneg hρ
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h1
    rw [trace_sum_conj_apply]
    exact sub_nonneg.mp h1

/-- The Kraus map of `K` is trace preserving iff `K` is an isometry. -/
theorem isTP_conj_iff {K : Matrix B A ℂ} : (conj K).IsTP ↔ Kᴴ * K = 1 := by
  simpa using isTP_sum_conj_iff (K := fun _ : Unit ↦ K)

/-- The Kraus map of `K` is trace nonincreasing iff `K` is a contraction. -/
theorem isTNI_conj_iff {K : Matrix B A ℂ} : (conj K).IsTNI ↔ (1 - Kᴴ * K).PosSemidef := by
  simpa using isTNI_sum_conj_iff (K := fun _ : Unit ↦ K)

end Trace

/-- A completely positive trace-nonincreasing map has Kraus operators, indexed by `B × A`, with
`1 - ∑ k, (K k)ᴴ * K k` positive semidefinite. -/
theorem IsCP.exists_kraus_of_isTNI [Fintype A] [Fintype B] [DecidableEq A] {Φ : MatrixMap A B}
    (hΦ : Φ.IsCP) (htni : Φ.IsTNI) :
    ∃ K : B × A → Matrix B A ℂ, Φ = ∑ k, conj (K k) ∧ (1 - ∑ k, (K k)ᴴ * K k).PosSemidef := by
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  exact ⟨K, rfl, isTNI_sum_conj_iff.mp htni⟩

/-- A completely positive trace-preserving map has Kraus operators, indexed by `B × A`, with
`∑ k, (K k)ᴴ * K k = 1`. -/
theorem IsCP.exists_kraus_of_isTP [Fintype A] [Fintype B] [DecidableEq A] {Φ : MatrixMap A B}
    (hΦ : Φ.IsCP) (htp : Φ.IsTP) :
    ∃ K : B × A → Matrix B A ℂ, Φ = ∑ k, conj (K k) ∧ ∑ k, (K k)ᴴ * K k = 1 := by
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  exact ⟨K, rfl, isTP_sum_conj_iff.mp htp⟩

/-! ## Stinespring form -/

section Stinespring

/-- The Kraus operators `K i : Matrix B A ℂ` stacked into one operator from `A` to `B × ι`, which
records the Kraus index in an environment on the right: `stinespring K (b, i) a = K i b a`, so
`S ψ = ∑ i, (K i ψ) ⊗ |i⟩`. Discarding the environment after `ρ ↦ S ρ S†` gives back
`∑ i, K i * ρ * (K i)†` (`sum_conj_eq_traceRight_comp_conj`). No completeness is assumed; `S† S`
is `∑ i, (K i)† * K i` (`conjTranspose_stinespring_mul_stinespring`). -/
@[expose]
def stinespring (K : ι → Matrix B A ℂ) : Matrix (B × ι) A ℂ :=
  Matrix.of fun x a ↦ K x.2 x.1 a

/-- The entry of the Stinespring operator at `((b, i), a)` is `K i b a`. -/
@[simp]
theorem stinespring_apply (K : ι → Matrix B A ℂ) (x : B × ι) (a : A) :
    stinespring K x a = K x.2 x.1 a :=
  rfl

/-- The Gram matrix of the Stinespring operator is `∑ i, (K i)ᴴ * K i`. -/
theorem conjTranspose_stinespring_mul_stinespring [Fintype B] [Fintype ι]
    (K : ι → Matrix B A ℂ) : (stinespring K)ᴴ * stinespring K = ∑ i, (K i)ᴴ * K i := by
  ext a a'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespring_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- A sum of Kraus maps is the partial trace of conjugation by the Stinespring operator. -/
theorem sum_conj_apply_eq_traceRight [Fintype A] [Fintype ι] (K : ι → Matrix B A ℂ)
    (ρ : Matrix A A ℂ) : (∑ i, conj (K i)) ρ = traceRight B ι (conj (stinespring K) ρ) := by
  ext b b'
  simp [LinearMap.sum_apply, Matrix.sum_apply, Matrix.mul_apply]

/-- **Stinespring form** of a sum of Kraus maps: conjugation by the Stinespring operator, followed
by the partial trace over the Kraus index. -/
theorem sum_conj_eq_traceRight_comp_conj [Fintype A] [Fintype ι] (K : ι → Matrix B A ℂ) :
    ∑ i, conj (K i) = traceRight B ι ∘ₗ conj (stinespring K) :=
  LinearMap.ext (sum_conj_apply_eq_traceRight K)

variable [Fintype A] [Fintype B] [Fintype ι]

variable [DecidableEq A]

/-- A sum of Kraus maps is trace preserving iff its Stinespring operator is an isometry. -/
theorem isTP_sum_conj_iff_stinespring {K : ι → Matrix B A ℂ} :
    IsTP (∑ i, conj (K i)) ↔ (stinespring K)ᴴ * stinespring K = 1 := by
  rw [conjTranspose_stinespring_mul_stinespring, isTP_sum_conj_iff]

/-- A sum of Kraus maps is trace nonincreasing iff its Stinespring operator is a contraction. -/
theorem isTNI_sum_conj_iff_stinespring {K : ι → Matrix B A ℂ} :
    IsTNI (∑ i, conj (K i)) ↔ (1 - (stinespring K)ᴴ * stinespring K).PosSemidef := by
  rw [conjTranspose_stinespring_mul_stinespring, isTNI_sum_conj_iff]

end Stinespring

/-- **Stinespring form of a quantum operation.** A completely positive trace-nonincreasing map
`Φ : M_A → M_B` is `ρ ↦ tr_E (S ρ S†)` for a contraction `S : ℂ^A → ℂ^B ⊗ ℂ^E` (`S† S ≤ 1`), with
environment basis `E = B × A` on the right: a sufficient, possibly nonminimal environment. The
trace-preserving case is `exists_stinespring_of_isTP`. -/
theorem IsCP.exists_stinespring_of_isTNI [Fintype A] [Fintype B] [DecidableEq A]
    {Φ : MatrixMap A B} (hΦ : Φ.IsCP) (htni : Φ.IsTNI) :
    ∃ S : Matrix (B × (B × A)) A ℂ,
      Φ = traceRight B (B × A) ∘ₗ conj S ∧ (1 - Sᴴ * S).PosSemidef := by
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  exact ⟨stinespring K, sum_conj_eq_traceRight_comp_conj K,
    isTNI_sum_conj_iff_stinespring.mp htni⟩

/-- **Stinespring form of a quantum channel.** A completely positive trace-preserving map
`Φ : M_A → M_B` is `ρ ↦ tr_E (S ρ S†)` for an isometry `S : ℂ^A → ℂ^B ⊗ ℂ^E` (`S† S = 1`), with
environment basis `E = B × A` on the right (Watrous, Corollary 2.27,
printed p. 89 / full-book PDF p. 97; see the module references). This is a sufficient, possibly
nonminimal environment. -/
theorem IsCP.exists_stinespring_of_isTP [Fintype A] [Fintype B] [DecidableEq A]
    {Φ : MatrixMap A B} (hΦ : Φ.IsCP) (htp : Φ.IsTP) :
    ∃ S : Matrix (B × (B × A)) A ℂ, Φ = traceRight B (B × A) ∘ₗ conj S ∧ Sᴴ * S = 1 := by
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  exact ⟨stinespring K, sum_conj_eq_traceRight_comp_conj K,
    isTP_sum_conj_iff_stinespring.mp htp⟩

/-! ## Families -/

namespace IsCPTNIFamily

/-- For each fixed member `i` of a completely positive trace-nonincreasing family, `Φ i` is a
sum of Kraus maps. -/
theorem exists_kraus [Fintype A] {B : ι → Type*} [∀ i, Fintype (B i)]
    {Φ : (i : ι) → MatrixMap A (B i)} (h : IsCPTNIFamily Φ) (i : ι) :
    ∃ K : B i × A → Matrix (B i) A ℂ, Φ i = ∑ k, conj (K k) :=
  (h.isCP i).exists_kraus

/-- A finite completely positive trace-nonincreasing family has joint Kraus operators,
with `1 - ∑ i, ∑ k, (K i k)ᴴ * K i k` positive semidefinite, even for dependent outputs. -/
theorem exists_kraus_of_fintype [Fintype A] {B : ι → Type*} [∀ i, Fintype (B i)]
    [DecidableEq A] [Fintype ι] {Φ : (i : ι) → MatrixMap A (B i)} (h : IsCPTNIFamily Φ) :
    ∃ K : (i : ι) → B i × A → Matrix (B i) A ℂ,
      (∀ i, Φ i = ∑ k, conj (K i k)) ∧
      (1 - ∑ i, ∑ k, (K i k)ᴴ * K i k).PosSemidef := by
  classical
  choose K hK using h.exists_kraus
  refine ⟨K, hK, ?_⟩
  refine (isHermitian_one.sub (Matrix.posSemidef_sum _ fun i _ ↦
    posSemidef_sum_conjTranspose_mul_self (K i)).isHermitian
    ).posSemidef_of_trace_mul_re_nonneg fun ρ hρ ↦ ?_
  have ht := h.sum_trace_re_le Finset.univ ρ hρ
  simp only [hK, trace_sum_conj_apply] at ht
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  simpa only [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum] using sub_nonneg.mpr ht

end IsCPTNIFamily

/-- Members of a finite completely positive family whose sum is trace preserving have Kraus
operators for all members at once, with `∑ i, ∑ k, (K i k)ᴴ * K i k = 1`. -/
theorem exists_kraus_of_isTP_sum [Fintype A] [Fintype B] [DecidableEq A] [Fintype ι]
    {Φ : ι → MatrixMap A B} (hcp : ∀ i, (Φ i).IsCP) (htp : IsTP (∑ i, Φ i)) :
    ∃ K : ι → B × A → Matrix B A ℂ, (∀ i, Φ i = ∑ k, conj (K i k)) ∧
      ∑ i, ∑ k, (K i k)ᴴ * K i k = 1 := by
  let K i := krausOps (Φ i) (hcp i)
  have hK : ∀ i, Φ i = ∑ k, conj (K i k) := fun i ↦ (sum_conj_krausOps _ _).symm
  refine ⟨K, hK, ?_⟩
  rw [Finset.sum_congr rfl fun i _ ↦ hK i,
    ← Fintype.sum_prod_type' (f := fun i k ↦ conj (K i k))] at htp
  rw [← Fintype.sum_prod_type' (f := fun i k ↦ (K i k)ᴴ * K i k)]
  exact isTP_sum_conj_iff.mp htp

end MatrixMap

end Quantum
