/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Observe

/-!
# Computational-basis gates, states and instruments

The building blocks of oracle algorithms on a register with basis `A`: gates given by isometries,
the matrices and states of the computational basis, and the instruments that read the register
in that basis.

## Main definitions

* `Quantum.SubInstrument.ofIsometry K hK`: the lossless one-outcome subinstrument
  `ρ ↦ K * ρ * Kᴴ` of an isometry `K`.
* `Quantum.basisMatrix f`: the matrix sending the basis vector `|a⟩` to `|f a⟩`.
* `Quantum.SubState.basis a`: the basis state `|a⟩⟨a|`.
* `Quantum.SubState.prod ρ σ` and `Quantum.SubState.traceRight ρ`: the product of substates of
  two registers, and the reduced substate of the left register of a joint substate.
* `Quantum.SubInstrument.relabel e`: the gate of a bijection `e` between bases, which moves a
  register to another basis without changing its state.
* `Quantum.SubInstrument.classical f g`: measure the register in the computational basis; on
  reading `a`, report `g a` and prepare `|f a⟩`.

Steps of an oracle algorithm report no classical value, so they have outcomes in `Unit`; the
lemmas `Quantum.SubInstrument.branch_bind_unit`, `Quantum.SubInstrument.post_bind_unit` and
`Quantum.SubInstrument.outcomeMeasure_bind_unit` sequence such steps without sums over outcomes.
-/

public section

open MeasureTheory Matrix
open scoped ComplexOrder Kronecker

namespace Quantum

variable {A B C : Type*} {α β : Type*}

/-! ## Relabelled outcomes and steps without outcome -/

namespace SubInstrument

section

variable [Fintype A] [Fintype B] [Fintype C]

/-- The branch of a relabelled subinstrument at `b` sums the branches of the outcomes sent to
`b`. -/
theorem branch_map_apply_univ [Fintype α] [DecidableEq β] (f : α → β) (p : SubInstrument A B α)
    (b : β) : (p.map f).branch b = ∑ a, if f a = b then p.branch a else 0 := by
  rw [map_eq_bind_pure, branch_bind_apply_univ]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  split_ifs with h
  · rw [h, branch_pure_self, LinearMap.id_comp]
  · rw [branch_pure_of_ne (Ne.symm h), LinearMap.zero_comp]

/-- The outcome measure of a relabelled subinstrument moves each point mass along the
relabelling. -/
theorem outcomeMeasure_map [MeasurableSpace β] (f : α → β)
    (p : SubInstrument A B α) (ρ : SubState A) :
    (p.map f).outcomeMeasure ρ =
      Measure.sum fun a ↦ ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac (f a) := by
  rw [map_eq_bind_pure, outcomeMeasure_bind]
  exact congrArg Measure.sum <| funext fun a ↦ by rw [outcomeMeasure_pure, matrix_post]

/-- The outcome measure of a relabelled subinstrument as a sum over a finite type of
outcomes. -/
theorem outcomeMeasure_map_univ [Fintype α] [MeasurableSpace β] (f : α → β)
    (p : SubInstrument A B α) (ρ : SubState A) :
    (p.map f).outcomeMeasure ρ =
      ∑ a, ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac (f a) := by
  rw [outcomeMeasure_map, Measure.sum_fintype]

/-- After a step without outcome, the branch of a composite at `b` is the branch of the
continuation at `b` after the unique branch of the step. -/
theorem branch_bind_unit (p : SubInstrument A B Unit) (k : Unit → SubInstrument B C β) (b : β) :
    (p.bind k).branch b = (k ()).branch b ∘ₗ p.branch () := by
  rw [branch_bind_apply_univ, Fintype.sum_unique]

/-- After a step without outcome, the post-branch substate of a composite is the post-branch
substate of the continuation on the substate left by the step. -/
theorem post_bind_unit (p : SubInstrument A B Unit) (k : Unit → SubInstrument B C β)
    (ρ : SubState A) (b : β) : (p.bind k).post ρ b = (k ()).post (p.post ρ ()) b :=
  SubState.ext <| by simp [branch_bind_unit]

/-- After a step without outcome, the outcome measure of a composite is the outcome measure of
the continuation on the substate left by the step. -/
theorem outcomeMeasure_bind_unit [MeasurableSpace β] (p : SubInstrument A B Unit)
    (k : Unit → SubInstrument B C β) (ρ : SubState A) :
    (p.bind k).outcomeMeasure ρ = (k ()).outcomeMeasure (p.post ρ ()) := by
  rw [outcomeMeasure_bind, Measure.sum_fintype, Fintype.sum_unique]

/-- A lossless step without outcome preserves the trace of the substate. -/
theorem Lossless.trace_post_unit {p : SubInstrument A B Unit} (hp : p.Lossless) (ρ : SubState A) :
    (p.post ρ ()).matrix.trace = ρ.matrix.trace := by
  rw [matrix_post, ← hp ρ.matrix, total_eq_sum_univ, Fintype.sum_unique]

end

/-! ## Isometries -/

section ofIsometry

variable [Fintype A] [Fintype B] [DecidableEq A]

/-- The gate of an isometry `K`: the one-outcome subinstrument `ρ ↦ K * ρ * Kᴴ`. A unitary on a
register is the case `A = B`. -/
@[expose]
noncomputable def ofIsometry (K : Matrix B A ℂ) (hK : Kᴴ * K = 1) : SubInstrument A B Unit :=
  ofMap (MatrixMap.conj K) (MatrixMap.isCP_conj K) (MatrixMap.isTP_conj hK).isTNI

/-- The unique branch of the gate of `K` is the Kraus map of `K`. -/
@[simp]
theorem branch_ofIsometry_apply (K : Matrix B A ℂ) (hK : Kᴴ * K = 1) (u : Unit) :
    (ofIsometry K hK).branch u = MatrixMap.conj K :=
  rfl

/-- The gate of an isometry is lossless. -/
theorem lossless_ofIsometry (K : Matrix B A ℂ) (hK : Kᴴ * K = 1) : (ofIsometry K hK).Lossless :=
  lossless_ofMap _ (MatrixMap.isTP_conj hK)

/-- The gate of the identity matrix returns without touching the state. -/
theorem ofIsometry_one :
    ofIsometry (1 : Matrix A A ℂ) (by simp) = SubInstrument.pure () :=
  SubInstrument.ext <| funext fun u ↦ by
    rw [branch_ofIsometry_apply, MatrixMap.conj_one, branch_pure_self]

/-- Sequencing the gates of two isometries is the gate of their product. -/
theorem ofIsometry_bind_ofIsometry [Fintype C] [DecidableEq B] (K : Matrix B A ℂ)
    (hK : Kᴴ * K = 1) (L : Matrix C B ℂ) (hL : Lᴴ * L = 1) :
    ((ofIsometry K hK).bind fun _ ↦ ofIsometry L hL) =
      ofIsometry (L * K) (by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ, hL,
          Matrix.one_mul, hK]) := by
  refine SubInstrument.ext <| funext fun u ↦ ?_
  rw [branch_bind_unit, branch_ofIsometry_apply, branch_ofIsometry_apply,
    branch_ofIsometry_apply, MatrixMap.conj_mul]

end ofIsometry

end SubInstrument

/-! ## Basis matrices -/

section basisMatrix

/-- The matrix of the linear map that sends the basis vector `|a⟩` to the basis vector
`|f a⟩`. For a bijection `f` it is a permutation matrix. -/
@[expose]
def basisMatrix [DecidableEq B] (f : A → B) : Matrix B A ℂ :=
  Matrix.of fun b a ↦ if b = f a then 1 else 0

/-- The entry of a basis matrix at `(b, a)` is one when `b = f a` and zero otherwise. -/
@[simp]
theorem basisMatrix_apply [DecidableEq B] (f : A → B) (b : B) (a : A) :
    basisMatrix f b a = if b = f a then 1 else 0 :=
  rfl

/-- The basis matrix of the identity function is the identity matrix. -/
@[simp]
theorem basisMatrix_id [DecidableEq A] : basisMatrix (id : A → A) = 1 := by
  ext a b
  simp [Matrix.one_apply]

/-- The basis matrix of a composite is the product of the basis matrices. -/
theorem basisMatrix_comp [Fintype B] [DecidableEq B] [DecidableEq C] (g : B → C) (f : A → B) :
    basisMatrix (g ∘ f) = basisMatrix g * basisMatrix f := by
  ext c a
  simp [Matrix.mul_apply]

/-- A basis matrix sends the basis vector at `a` to the basis vector at `f a`. -/
theorem basisMatrix_mulVec_single [Fintype A] [DecidableEq A] [DecidableEq B] (f : A → B)
    (a : A) : basisMatrix f *ᵥ Pi.single a 1 = Pi.single (f a) 1 := by
  ext b
  simp [Pi.single_apply]

/-- The basis matrix of an injective function is an isometry. -/
theorem conjTranspose_basisMatrix_mul_self [Fintype B] [DecidableEq A] [DecidableEq B]
    {f : A → B} (hf : Function.Injective f) : (basisMatrix f)ᴴ * basisMatrix f = 1 := by
  ext a a'
  simp [Matrix.mul_apply, Matrix.one_apply, hf.eq_iff, eq_comm]

/-- The adjoint of the basis matrix of a bijection is the basis matrix of its inverse. -/
theorem conjTranspose_basisMatrix_equiv [DecidableEq A] [DecidableEq B] (e : A ≃ B) :
    (basisMatrix e)ᴴ = basisMatrix e.symm := by
  ext a b
  simp [Equiv.eq_symm_apply, eq_comm]

/-- Conjugating by the basis matrix of a bijection relabels the rows and columns. -/
theorem conj_basisMatrix_equiv [Fintype A] [DecidableEq B] (e : A ≃ B) (ρ : Matrix A A ℂ) :
    MatrixMap.conj (basisMatrix e) ρ = ρ.submatrix e.symm e.symm := by
  ext b b'
  simp only [MatrixMap.conj_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    basisMatrix_apply, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single (e.symm b'), Finset.sum_eq_single (e.symm b)]
  · simp
  · exact fun a _ ha ↦ by simp [show b ≠ e a from fun h ↦ ha (by simp [h])]
  · simp
  · exact fun a _ ha ↦ by simp [show b' ≠ e a from fun h ↦ ha (by simp [h])]
  · simp

end basisMatrix

/-! ## Basis states -/

section basis

variable [Fintype A] [DecidableEq A]

/-- The basis state `|a⟩⟨a|` of a register. -/
@[expose]
def SubState.basis (a : A) : SubState A where
  matrix := Matrix.single a a 1
  posSemidef := by
    have h : (Matrix.single a a 1 : Matrix A A ℂ) =
        (Matrix.single a a (1 : ℂ))ᴴ * Matrix.single a a (1 : ℂ) := by
      simp
    rw [h]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_re_le_one := by simp

/-- The matrix of the basis state at `a` has a single nonzero entry, at `(a, a)`. -/
@[simp]
theorem SubState.matrix_basis (a : A) : (SubState.basis a).matrix = Matrix.single a a 1 :=
  rfl

/-- A basis state has trace one. -/
theorem SubState.trace_basis (a : A) : (SubState.basis a).matrix.trace = 1 := by
  simp

/-- The gate of the basis matrix of a bijection sends the basis state at `a` to the basis state
at `e a`. -/
theorem conj_basisMatrix_equiv_single [DecidableEq B] (e : A ≃ B) (a : A) :
    MatrixMap.conj (basisMatrix e) (Matrix.single a a 1) = Matrix.single (e a) (e a) 1 := by
  rw [conj_basisMatrix_equiv]
  ext b b'
  simp [Matrix.single_apply, Equiv.eq_symm_apply]

end basis

/-! ## Product and reduced substates -/

section prod

variable [Fintype A] [Fintype B]

/-- The product `ρ ⊗ σ` of substates of two registers, a substate of the joint register. -/
@[expose]
def SubState.prod (ρ : SubState A) (σ : SubState B) : SubState (A × B) where
  matrix := ρ.matrix ⊗ₖ σ.matrix
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_re_le_one := by
    have h₁ := Complex.nonneg_iff.mp ρ.posSemidef.trace_nonneg
    rw [Matrix.trace_kronecker, Complex.mul_re, ← h₁.2, zero_mul, sub_zero]
    calc ρ.matrix.trace.re * σ.matrix.trace.re ≤ 1 * 1 :=
          mul_le_mul ρ.trace_re_le_one σ.trace_re_le_one σ.trace_re_nonneg zero_le_one
      _ = 1 := one_mul 1

/-- The matrix of a product substate is the Kronecker product of the matrices. -/
@[simp]
theorem SubState.matrix_prod (ρ : SubState A) (σ : SubState B) :
    (ρ.prod σ).matrix = ρ.matrix ⊗ₖ σ.matrix :=
  rfl

/-- The trace of a product substate is the product of the traces. -/
theorem SubState.trace_re_prod (ρ : SubState A) (σ : SubState B) :
    (ρ.prod σ).matrix.trace.re = ρ.matrix.trace.re * σ.matrix.trace.re := by
  have h₁ := Complex.nonneg_iff.mp ρ.posSemidef.trace_nonneg
  rw [matrix_prod, Matrix.trace_kronecker, Complex.mul_re, ← h₁.2, zero_mul, sub_zero]

/-- The product of basis states is the basis state of the pair. -/
@[simp]
theorem SubState.basis_prod_basis [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    (SubState.basis a).prod (SubState.basis b) = SubState.basis (a, b) :=
  SubState.ext <| by
    ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    rw [matrix_prod, matrix_basis, matrix_basis, matrix_basis, Matrix.kroneckerMap_apply]
    simp only [Matrix.single_apply, Prod.mk.injEq]
    rw [ite_zero_mul_ite_zero, mul_one]
    exact if_congr (by tauto) rfl rfl

/-- The reduced substate of the left register: the partial trace over the right register. -/
@[expose]
def SubState.traceRight (ρ : SubState (A × B)) : SubState A where
  matrix := MatrixMap.traceRight A B ρ.matrix
  posSemidef := ρ.posSemidef.traceRight
  trace_re_le_one := by
    rw [MatrixMap.trace_traceRight]
    exact ρ.trace_re_le_one

/-- The matrix of a reduced substate is the partial trace of the matrix. -/
@[simp]
theorem SubState.matrix_traceRight (ρ : SubState (A × B)) :
    ρ.traceRight.matrix = MatrixMap.traceRight A B ρ.matrix :=
  rfl

/-- Tracing out a factor of trace one from a product substate recovers the other factor. -/
theorem SubState.traceRight_prod (ρ : SubState A) {σ : SubState B}
    (hσ : σ.matrix.trace = 1) : (ρ.prod σ).traceRight = ρ :=
  SubState.ext <| by simp [MatrixMap.traceRight_kronecker, hσ]

end prod

/-! ## Relabelling registers -/

namespace SubInstrument

section relabel

variable [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- The relabelling gate of a bijection `e : A ≃ B` between bases: the lossless one-outcome
subinstrument that moves the basis vector `|a⟩` to `|e a⟩`. An operator `ρ` on `A` becomes the
operator `ρ.submatrix e.symm e.symm` on `B` (`Quantum.SubInstrument.relabel_branch_apply`). -/
@[expose]
noncomputable def relabel (e : A ≃ B) : SubInstrument A B Unit :=
  ofIsometry (basisMatrix e) (conjTranspose_basisMatrix_mul_self e.injective)

/-- The unique branch of a relabelling gate is conjugation by the basis matrix. -/
theorem branch_relabel (e : A ≃ B) (u : Unit) :
    (relabel e).branch u = MatrixMap.conj (basisMatrix e) :=
  branch_ofIsometry_apply ..

/-- A relabelling gate moves the rows and columns of an operator along the bijection. -/
@[simp]
theorem relabel_branch_apply (e : A ≃ B) (u : Unit) (ρ : Matrix A A ℂ) :
    (relabel e).branch u ρ = ρ.submatrix e.symm e.symm := by
  rw [branch_relabel, conj_basisMatrix_equiv]

/-- A relabelling gate is lossless. -/
theorem lossless_relabel (e : A ≃ B) : (relabel e).Lossless :=
  lossless_ofIsometry (basisMatrix e) _

/-- Relabelling along the identity bijection returns without touching the state. -/
@[simp]
theorem relabel_refl : relabel (Equiv.refl A) = SubInstrument.pure () :=
  SubInstrument.ext <| funext fun u ↦ LinearMap.ext fun ρ ↦ by
    rw [relabel_branch_apply, branch_pure_self]
    rfl

/-- Relabelling along `e` and then along `f` is relabelling along the composite bijection. -/
theorem relabel_bind_relabel (e : A ≃ B) (f : B ≃ C) :
    ((relabel e).bind fun _ ↦ relabel f) = relabel (e.trans f) :=
  SubInstrument.ext <| funext fun u ↦ LinearMap.ext fun ρ ↦ by
    rw [branch_bind_unit, LinearMap.comp_apply, relabel_branch_apply, relabel_branch_apply,
      relabel_branch_apply, Matrix.submatrix_submatrix]
    rfl

/-- A relabelling gate sends the basis state at `a` to the basis state at `e a`. -/
theorem post_relabel_basis (e : A ≃ B) (a : A) :
    (relabel e).post (SubState.basis a) () = SubState.basis (e a) :=
  SubState.ext <| by
    rw [matrix_post, branch_relabel, SubState.matrix_basis, conj_basisMatrix_equiv_single]
    rfl

end relabel

end SubInstrument

/-! ## Classical instruments -/

namespace SubInstrument

section classical

variable [Fintype A] [DecidableEq A] [DecidableEq B]

variable [Fintype B]

/-- The operators `|f a⟩⟨a|` satisfy the completeness relation. -/
theorem sum_conjTranspose_single_mul_single (f : A → B) :
    ∑ a, (Matrix.single (f a) a (1 : ℂ))ᴴ * Matrix.single (f a) a (1 : ℂ) = 1 := by
  ext a a'
  simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, mul_one,
    Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single a (fun x _ hx ↦ by simp [hx]) (by simp)]
  simp

/-- The classical instrument of `f` and `g`: measure the register in the computational basis
and, on reading `a`, report `g a` and prepare the basis state at `f a`. Its Kraus operators are
`|f a⟩⟨a|`. -/
@[expose]
noncomputable def classical (f : A → B) (g : A → α) : SubInstrument A B α :=
  (ofKraus (fun a ↦ Matrix.single (f a) a 1) (sum_conjTranspose_single_mul_single f)).map g

/-- A classical instrument is lossless. -/
theorem lossless_classical (f : A → B) (g : A → α) : (classical f g).Lossless :=
  (lossless_ofKraus _ _).map g

/-- On the basis state at `a`, a classical instrument reports `g a` with weight one and leaves
the basis state at `f a`. -/
theorem branch_classical_basis [DecidableEq α] (f : A → B) (g : A → α) (a : A) (c : α) :
    (classical f g).branch c (Matrix.single a a 1) =
      if g a = c then Matrix.single (f a) (f a) 1 else 0 := by
  rw [classical, branch_map_apply_univ, LinearMap.sum_apply,
    Finset.sum_eq_single a (fun a' _ ha' ↦ ?_) (by simp)]
  · split_ifs <;> simp
  · split_ifs <;> simp [ha']

/-- A classical step without outcome sends the basis state at `a` to the basis state at
`f a`. -/
theorem post_classical_basis (f : A → B) (a : A) :
    (classical f fun _ ↦ ()).post (SubState.basis a) () = SubState.basis (f a) :=
  SubState.ext <| by simp [branch_classical_basis]

/-- On the basis state at `a`, a classical instrument reports `g a` with certainty. -/
theorem outcomeMeasure_classical_basis [MeasurableSpace α] (f : A → B) (g : A → α) (a : A) :
    (classical f g).outcomeMeasure (SubState.basis a) = Measure.dirac (g a) := by
  rw [classical, outcomeMeasure_map_univ, Finset.sum_eq_single a (fun a' _ ha' ↦ ?_) (by simp)]
  · simp
  · simp [ha']

omit [DecidableEq B] in
/-- A framed subinstrument acts on a product basis state through its first factor. -/
theorem branch_frame_single {R : Type*} [Fintype R] [DecidableEq R] (p : SubInstrument A B α)
    (c : α) (a : A) (r : R) :
    (p.frame R).branch c (Matrix.single (a, r) (a, r) 1) =
      p.branch c (Matrix.single a a 1) ⊗ₖ Matrix.single r r 1 := by
  rw [branch_frame_apply, ← MatrixMap.amplify_kronecker, Matrix.single_kronecker_single, one_mul]

end classical

end SubInstrument

end Quantum
