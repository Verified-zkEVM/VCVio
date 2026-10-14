/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.Matrix.Hermitian
public import VCVio.Quantum.MatrixMap.Family

/-!
# Choi matrices and Kraus decompositions

Every completely positive map between matrix algebras is a finite sum of Kraus maps
`ρ ↦ K * ρ * Kᴴ` (Choi's theorem), and the trace conditions on the map are matrix inequalities on
its Kraus operators. Stacking the Kraus operators into one column gives a Stinespring operator: the
map becomes conjugation by one operator into an enlarged system, followed by a partial trace.

The Choi matrix of `Φ : MatrixMap A B` is indexed by `B × A`; its block at input indices
`(a, a')` is `Φ (single a a' 1)`. It is `Φ ⊗ id_A` applied to the unnormalized maximally entangled
matrix, so it is positive semidefinite when `Φ` is completely positive. A factorization
`choi Φ = Yᴴ * Y` with `Y : Matrix ι (B × A) ℂ` gives Kraus operators indexed by `ι`, one per row
of `Y`. A positive semidefinite matrix has such a factorization with `ι = B × A`.

## Main definitions

* `Quantum.MatrixMap.choi Φ`: the Choi matrix, and `Quantum.MatrixMap.ofChoi C` the matrix map
  with Choi matrix `C`; together they form the linear equivalence `Quantum.MatrixMap.choiEquiv`.
* `Quantum.MatrixMap.krausOfFactor Y`: the Kraus operators read off the rows of a factor `Y` of the
  Choi matrix.
* `Quantum.MatrixMap.krausOps Φ hΦ`: a chosen family of Kraus operators of a completely positive
  map, indexed by `B × A`.
* `Quantum.MatrixMap.stinespring K`: the Kraus operators `K i` stacked into one operator from `A`
  to `B × ι`.

## Main results

* `Quantum.MatrixMap.ofChoi_choi`, `Quantum.MatrixMap.apply_eq_sum_choi`: a matrix map is
  recovered from its Choi matrix.
* `Quantum.MatrixMap.IsCP.posSemidef_choi`: the Choi matrix of a completely positive map is
  positive semidefinite.
* `Quantum.MatrixMap.IsCP.exists_kraus`, `Quantum.MatrixMap.isCP_iff_exists_kraus`: Choi's
  theorem.
* `Quantum.MatrixMap.isTNI_sum_conj_iff`, `Quantum.MatrixMap.isTP_sum_conj_iff`: a sum of Kraus
  maps is trace nonincreasing iff `1 - ∑ i, (K i)ᴴ * K i` is positive semidefinite, and trace
  preserving iff `∑ i, (K i)ᴴ * K i = 1`.
* `Quantum.MatrixMap.sum_conj_eq_traceRight_comp_conj`,
  `Quantum.MatrixMap.IsCP.exists_stinespring_of_isTNI`: Stinespring form. A completely positive
  trace-nonincreasing map is conjugation by a contraction into `B × (B × A)` followed by the
  partial trace; the contraction is an isometry when the map is trace preserving.
* `Quantum.MatrixMap.IsCPTNIFamily.exists_kraus_of_fintype`: a finite completely positive family
  with trace-nonincreasing sum has Kraus operators for all members at once, with joint
  completeness inequality.

## Not covered

For a family with infinitely many members, such as the branches of an instrument with countably
many outcomes, each member still has Kraus operators
(`Quantum.MatrixMap.IsCPTNIFamily.exists_kraus`). A joint Stinespring operator for the whole
family is not built here. It would map into the infinite-dimensional space
`ℓ²(outcomes) ⊗ B ⊗ (B × A)`: it needs the convergence of `∑ i, ∑ k, (K i k)ᴴ * K i k` over the
countable support of the family, and a contraction into a Hilbert space rather than a matrix,
which is an isometry when the family is lossless.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra Appl. 10
  (1975), 285–290.
* K. Kraus, *States, Effects, and Operations*, Lecture Notes in Physics 190, Springer, 1983.
* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216.
-/

public section

open scoped ComplexOrder
open Matrix

/-! ## Positivity through the trace pairing -/

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A Hermitian complex matrix whose trace pairing with every positive semidefinite matrix has
nonnegative real part is positive semidefinite. -/
theorem IsHermitian.posSemidef_of_trace_mul_re_nonneg {N : Matrix n n ℂ} (hN : N.IsHermitian)
    (h : ∀ ρ : Matrix n n ℂ, ρ.PosSemidef → 0 ≤ (N * ρ).trace.re) : N.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hN fun v ↦ ?_
  have h1 := h _ (posSemidef_vecMulVec_self_star v)
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm] at h1
  refine Complex.nonneg_iff.mpr ⟨h1, ?_⟩
  simpa using (hN.im_star_dotProduct_mulVec_self v).symm

/-- A complex matrix is positive semidefinite iff it is Hermitian and its trace pairing with every
positive semidefinite matrix has nonnegative real part. -/
theorem posSemidef_iff_forall_trace_mul_re_nonneg {N : Matrix n n ℂ} :
    N.PosSemidef ↔ N.IsHermitian ∧ ∀ ρ : Matrix n n ℂ, ρ.PosSemidef → 0 ≤ (N * ρ).trace.re :=
  ⟨fun hN ↦ ⟨hN.isHermitian, fun _ hρ ↦ hN.trace_mul_re_nonneg hρ⟩,
    fun h ↦ h.1.posSemidef_of_trace_mul_re_nonneg h.2⟩

end Matrix

namespace Quantum

namespace MatrixMap

variable {A B ι : Type*}

/-! ## The Choi matrix -/

section Choi

/-- The Choi matrix of a matrix map: its entry at `((b, a), (b', a'))` is the entry at `(b, b')`
of the map applied to the matrix unit `single a a' 1`. -/
@[expose]
def choi [DecidableEq A] (Φ : MatrixMap A B) : Matrix (B × A) (B × A) ℂ :=
  Matrix.of fun x y ↦ Φ (single x.2 y.2 1) x.1 y.1

/-- The entry of the Choi matrix at `(x, y)` is the entry at `(x.1, y.1)` of the map applied to
the matrix unit `single x.2 y.2 1`. -/
@[simp]
theorem choi_apply [DecidableEq A] (Φ : MatrixMap A B) (x y : B × A) :
    choi Φ x y = Φ (single x.2 y.2 1) x.1 y.1 :=
  rfl

/-- The matrix map with Choi matrix `C`: it sends `ρ` to the matrix whose entry at `(b, b')` is
`∑ a, ∑ a', ρ a a' * C (b, a) (b', a')`. -/
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

/-- **Choi's theorem**: a matrix map is completely positive iff it is a finite sum of Kraus maps.
The index type of the Kraus operators may live in any universe. -/
theorem isCP_iff_exists_kraus [Fintype A] [Finite B] {Φ : MatrixMap A B} :
    Φ.IsCP ↔ ∃ (κ : Type*) (_ : Fintype κ) (K : κ → Matrix B A ℂ), Φ = ∑ i, conj (K i) := by
  refine ⟨fun hΦ ↦ ?_, fun ⟨κ, _, K, hK⟩ ↦ hK ▸ isCP_sum_conj K⟩
  cases nonempty_fintype B
  obtain ⟨K, hK⟩ := hΦ.exists_kraus
  let e := Equiv.ulift.trans (Fintype.equivFin (B × A)).symm
  exact ⟨ULift (Fin (Fintype.card (B × A))), inferInstance, K ∘ e,
    hK.trans (Fintype.sum_equiv e _ _ fun _ ↦ rfl).symm⟩

/-- A chosen family of Kraus operators of a completely positive map, indexed by `B × A`. -/
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

/-- A sum of Kraus maps is trace preserving iff its Kraus operators satisfy the completeness
relation `∑ i, (K i)ᴴ * K i = 1`. -/
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

/-- A sum of Kraus maps is trace nonincreasing iff `1 - ∑ i, (K i)ᴴ * K i` is positive
semidefinite. -/
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

/-- The Stinespring operator of a family of Kraus operators: the operators `K i` stacked into one
operator from `A` to `B × ι`, with entry `K i b a` at `((b, i), a)`. -/
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

/-- **Stinespring dilation** of a completely positive trace-nonincreasing map: conjugation by a
contraction `S` into `B × (B × A)`, followed by the partial trace over `B × A`. -/
theorem IsCP.exists_stinespring_of_isTNI [Fintype A] [Fintype B] [DecidableEq A]
    {Φ : MatrixMap A B} (hΦ : Φ.IsCP) (htni : Φ.IsTNI) :
    ∃ S : Matrix (B × (B × A)) A ℂ,
      Φ = traceRight B (B × A) ∘ₗ conj S ∧ (1 - Sᴴ * S).PosSemidef := by
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  exact ⟨stinespring K, sum_conj_eq_traceRight_comp_conj K,
    isTNI_sum_conj_iff_stinespring.mp htni⟩

/-- **Stinespring dilation** of a completely positive trace-preserving map: conjugation by an
isometry `S` into `B × (B × A)`, followed by the partial trace over `B × A`. -/
theorem IsCP.exists_stinespring_of_isTP [Fintype A] [Fintype B] [DecidableEq A]
    {Φ : MatrixMap A B} (hΦ : Φ.IsCP) (htp : Φ.IsTP) :
    ∃ S : Matrix (B × (B × A)) A ℂ, Φ = traceRight B (B × A) ∘ₗ conj S ∧ Sᴴ * S = 1 := by
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  exact ⟨stinespring K, sum_conj_eq_traceRight_comp_conj K,
    isTP_sum_conj_iff_stinespring.mp htp⟩

/-! ## Families -/

namespace IsCPTNIFamily

/-- Every member of a completely positive trace-nonincreasing family is a sum of Kraus maps. -/
theorem exists_kraus [Fintype A] {B : ι → Type*} [∀ i, Fintype (B i)]
    {Φ : (i : ι) → MatrixMap A (B i)} (h : IsCPTNIFamily Φ) (i : ι) :
    ∃ K : B i × A → Matrix (B i) A ℂ, Φ i = ∑ k, conj (K k) :=
  (h.isCP i).exists_kraus

/-- A finite completely positive trace-nonincreasing family with a common codomain has Kraus
operators for all members at once, with `1 - ∑ i, ∑ k, (K i k)ᴴ * K i k` positive semidefinite. -/
theorem exists_kraus_of_fintype [Fintype A] [Fintype B] [DecidableEq A] [Fintype ι]
    {Φ : ι → MatrixMap A B} (h : IsCPTNIFamily Φ) :
    ∃ K : ι → B × A → Matrix B A ℂ, (∀ i, Φ i = ∑ k, conj (K i k)) ∧
      (1 - ∑ i, ∑ k, (K i k)ᴴ * K i k).PosSemidef := by
  let K i := krausOps (Φ i) (h.isCP i)
  have hK : ∀ i, Φ i = ∑ k, conj (K i k) := fun i ↦ (sum_conj_krausOps _ _).symm
  refine ⟨K, hK, ?_⟩
  have htni := h.isTNI_sum Finset.univ
  rw [Finset.sum_congr rfl fun i _ ↦ hK i,
    ← Fintype.sum_prod_type' (f := fun i k ↦ conj (K i k))] at htni
  rw [← Fintype.sum_prod_type' (f := fun i k ↦ (K i k)ᴴ * K i k)]
  exact isTNI_sum_conj_iff.mp htni

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
