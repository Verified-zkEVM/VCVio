/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Basic

/-!
# The purified standard oracle and the compressed oracle

The register of a query against a random function with a purified database is
`(X × Y) × Database X Y`: the query register `X × Y` of the program and the database register of
the oracle.

* A **table oracle** `Quantum.tableOracle read` on `(X × Y) × T` reads a function `read t` off
  the basis state `|t⟩` of a table register and adds its value into the response register. It is
  block diagonal in the table. Two instances matter: the database register with
  `Quantum.Database.lookup`, and the register of total functions `X → Y` with the identity (the
  purified random oracle of `Quantum.purifiedRuntime`).
* The **standard oracle** `Quantum.standardOracle X Y` sends `|x, y⟩|D⟩` to
  `|x, y + D x⟩|D⟩` when the cell `D x` holds a value and fixes it when the cell is empty. It is
  block diagonal in the database: on the block of `D` it acts as the oracle unitary of the
  function `Quantum.Database.lookup D`.
* The **compressed oracle** `Quantum.compressedOracle X Y` is the standard oracle conjugated by
  the compression of every cell, `(1 ⊗ S^{⊗X}) StO (1 ⊗ S^{⊗X})`.

Since the compression of a cell other than the queried one commutes with the standard oracle and
squares to the identity, the compressed oracle is also the standard oracle conjugated by the
compression of the queried cell only (`Quantum.compressedOracle_eq_controlled`): this is
Zhandry's description, in which a query decompresses the queried cell, applies the standard
oracle, and compresses the cell again.

## Main definitions

* `Quantum.tableOracle read`, with `Quantum.tableOracle_mul_one_kronecker_basisMatrix`: a
  relabelling of the table register that preserves the function read off it intertwines the table
  oracles.
* `Quantum.standardOracle X Y` and `Quantum.compressedOracle X Y`, unitary matrices on
  `(X × Y) × Database X Y`, with the one-query subinstruments `Quantum.standardQuery X Y` and
  `Quantum.compressedQuery X Y`.
* `Quantum.controlled A`: the operator applying `A x` to the database register when the query
  input is `x`.

## Main results

* `Quantum.compressedOracle_eq_controlled`: the two descriptions of the compressed oracle agree.
* `Quantum.one_kronecker_compressAll_mul_compressedOracle`: compressing every cell intertwines the
  compressed oracle with the standard oracle.
* `Quantum.submatrix_conj_standardOracle`: on the diagonal block of a database `D`, the standard
  oracle acts as the oracle unitary of `Quantum.Database.lookup D`.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

variable {X Y : Type*}

/-! ## Matrices controlled by the query input -/

section controlled

/-- A product with a basis matrix on the right reads a column of the left factor. -/
theorem mul_basisMatrix_apply {A B C : Type*} [Fintype B] [DecidableEq B] (K : Matrix C B ℂ)
    (f : A → B) (c : C) (a : A) : (K * basisMatrix f) c a = K c (f a) := by
  simp [Matrix.mul_apply]

variable {C : Type*} [DecidableEq X] [DecidableEq Y]

/-- The operator on `(X × Y) × C` that applies `A x` to the register `C` when the query input
is `x`. -/
@[expose]
def controlled (A : X → Matrix C C ℂ) : Matrix ((X × Y) × C) ((X × Y) × C) ℂ :=
  Matrix.of fun p p' ↦ if p.1 = p'.1 then A p.1.1 p.2 p'.2 else 0

@[simp]
theorem controlled_apply (A : X → Matrix C C ℂ) (p p' : (X × Y) × C) :
    controlled A p p' = if p.1 = p'.1 then A p.1.1 p.2 p'.2 else 0 :=
  rfl

/-- An operator on the second register alone is controlled by the query input in a constant
way. -/
theorem one_kronecker_eq_controlled (K : Matrix C C ℂ) :
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ K = controlled fun _ ↦ K := by
  ext ⟨m, c⟩ ⟨m', c'⟩
  simp [Matrix.one_apply]

end controlled

/-! ## Oracles that read a function off a table register -/

section table

variable {T T' : Type*} [AddCommGroup Y]

/-- The permutation of the basis of `(X × Y) × T` that reads a function off the table register
through `read` and adds its value into the response register:
`|x, y⟩|t⟩ ↦ |x, y + read t x⟩|t⟩`. -/
@[expose]
def tableOracleEquiv (read : T → X → Y) : (X × Y) × T ≃ (X × Y) × T where
  toFun p := (oracleEquiv (read p.2) p.1, p.2)
  invFun p := ((oracleEquiv (read p.2)).symm p.1, p.2)
  left_inv _ := Prod.ext ((oracleEquiv _).symm_apply_apply _) rfl
  right_inv _ := Prod.ext ((oracleEquiv _).apply_symm_apply _) rfl

@[simp]
theorem tableOracleEquiv_apply (read : T → X → Y) (m : X × Y) (t : T) :
    tableOracleEquiv read (m, t) = (oracleEquiv (read t) m, t) :=
  rfl

/-- The identity on the query register next to a basis matrix is the basis matrix of the
product map. -/
theorem one_kronecker_basisMatrix {A : Type*} [DecidableEq A] [DecidableEq T'] (g : T → T') :
    (1 : Matrix A A ℂ) ⊗ₖ basisMatrix g = basisMatrix (Prod.map id g) := by
  ext ⟨a, t'⟩ ⟨a', t⟩
  by_cases h : a = a' <;> simp [h]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq T] [DecidableEq T']

/-- The oracle that reads a function off the table register: the permutation matrix of
`Quantum.tableOracleEquiv read`. On the block of the table `t` it is the oracle unitary of
`read t` (`Quantum.submatrix_conj_tableOracle`). -/
@[expose]
def tableOracle (read : T → X → Y) : Matrix ((X × Y) × T) ((X × Y) × T) ℂ :=
  basisMatrix (tableOracleEquiv read)

theorem tableOracle_apply (read : T → X → Y) (p p' : (X × Y) × T) :
    tableOracle read p p' = if p = tableOracleEquiv read p' then 1 else 0 :=
  rfl

variable [Fintype X] [Fintype Y] [Fintype T] [Fintype T']

/-- The table oracle is an isometry. -/
theorem conjTranspose_tableOracle_mul_self (read : T → X → Y) :
    (tableOracle read)ᴴ * tableOracle read = 1 :=
  conjTranspose_basisMatrix_mul_self (tableOracleEquiv read).injective

/-- On the diagonal block of a table `t`, conjugation by the table oracle is conjugation by the
oracle unitary of `read t`. -/
theorem submatrix_conj_tableOracle (read : T → X → Y) (ρ : Matrix ((X × Y) × T) ((X × Y) × T) ℂ)
    (t : T) :
    (MatrixMap.conj (tableOracle read) ρ).submatrix (·, t) (·, t) =
      MatrixMap.conj (oracleUnitary (read t)) (ρ.submatrix (·, t) (·, t)) := by
  rw [tableOracle, conj_basisMatrix_equiv, oracleUnitary, conj_basisMatrix_equiv]
  rfl

/-- Relabelling the table register along a map `g` that preserves the function read off it
intertwines the two table oracles. -/
theorem tableOracle_mul_one_kronecker_basisMatrix {read : T → X → Y} {read' : T' → X → Y}
    {g : T → T'} (hg : ∀ t, read' (g t) = read t) :
    tableOracle read' * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix g) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix g) * tableOracle read := by
  rw [one_kronecker_basisMatrix, tableOracle, tableOracle, ← basisMatrix_comp,
    ← basisMatrix_comp]
  congr 1
  funext ⟨m, t⟩
  simp [hg]

end table

/-! ## The standard oracle -/

section standard

variable [AddCommGroup Y]

/-- The permutation of the basis of `(X × Y) × Database X Y` performed by the standard
oracle: `|x, y⟩|D⟩ ↦ |x, y + D x⟩|D⟩`, where an empty cell reads as `0`. -/
@[expose]
def standardOracleEquiv : (X × Y) × Database X Y ≃ (X × Y) × Database X Y :=
  tableOracleEquiv Database.lookup

@[simp]
theorem standardOracleEquiv_apply (m : X × Y) (D : Database X Y) :
    standardOracleEquiv (m, D) = (oracleEquiv (Database.lookup D) m, D) :=
  rfl

/-- The standard oracle fixes a basis state whose queried cell is empty. -/
theorem standardOracleEquiv_of_eq_none {m : X × Y} {D : Database X Y} (h : D m.1 = none) :
    standardOracleEquiv (m, D) = (m, D) := by
  simp [h]

/-- The standard oracle adds the content of a nonempty queried cell into the response register. -/
theorem standardOracleEquiv_of_eq_some {m : X × Y} {D : Database X Y} {u : Y}
    (h : D m.1 = some u) : standardOracleEquiv (m, D) = ((m.1, m.2 + u), D) := by
  simp [h]

variable [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

variable (X Y) in
/-- The standard oracle on `(X × Y) × Database X Y`, the permutation matrix sending
`|x, y⟩|D⟩` to `|x, y + u⟩|D⟩` when `D x = some u` and fixing it when `D x = none`. It is the
table oracle of `Quantum.Database.lookup`. -/
@[expose]
def standardOracle : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  tableOracle Database.lookup

omit [Fintype Y] in
theorem standardOracle_apply (p p' : (X × Y) × Database X Y) :
    standardOracle X Y p p' = if p = standardOracleEquiv p' then 1 else 0 :=
  rfl

/-- The standard oracle is an isometry. -/
theorem conjTranspose_standardOracle_mul_self :
    (standardOracle X Y)ᴴ * standardOracle X Y = 1 :=
  conjTranspose_tableOracle_mul_self _

/-- The standard oracle is unitary. -/
theorem standardOracle_mem_unitaryGroup :
    standardOracle X Y ∈ unitaryGroup ((X × Y) × Database X Y) ℂ :=
  mem_unitaryGroup_iff'.mpr conjTranspose_standardOracle_mul_self

/-- On the diagonal block of a database `D`, conjugation by the standard oracle is conjugation by
the oracle unitary of the function `Quantum.Database.lookup D`. -/
theorem submatrix_conj_standardOracle
    (ρ : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)
    (D : Database X Y) :
    (MatrixMap.conj (standardOracle X Y) ρ).submatrix (·, D) (·, D) =
      MatrixMap.conj (oracleUnitary (Database.lookup D)) (ρ.submatrix (·, D) (·, D)) :=
  submatrix_conj_tableOracle _ ρ D

variable (X Y) in
/-- One query to the standard oracle on the joint register, a lossless subinstrument. -/
@[expose]
noncomputable def standardQuery :
    SubInstrument ((X × Y) × Database X Y) ((X × Y) × Database X Y) Unit :=
  SubInstrument.ofIsometry (standardOracle X Y) conjTranspose_standardOracle_mul_self

@[simp]
theorem branch_standardQuery_apply (u : Unit) :
    (standardQuery X Y).branch u = MatrixMap.conj (standardOracle X Y) :=
  SubInstrument.branch_ofIsometry_apply ..

theorem lossless_standardQuery : (standardQuery X Y).Lossless :=
  SubInstrument.lossless_ofIsometry _ _

/-- On the diagonal block of a database `D`, a standard query acts as a query to the function
`Quantum.Database.lookup D`. -/
theorem submatrix_branch_standardQuery
    (ρ : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)
    (D : Database X Y) :
    ((standardQuery X Y).branch () ρ).submatrix (·, D) (·, D) =
      (oracleQuery (Database.lookup D)).branch () (ρ.submatrix (·, D) (·, D)) := by
  rw [branch_standardQuery_apply, branch_oracleQuery_apply, submatrix_conj_standardOracle]

/-- The entry of the standard oracle between two controlled operators. Only the intermediate
databases `D₁` whose cell at the query input moves the response register from `m'` to `m`
contribute. -/
theorem controlled_mul_standardOracle_mul_controlled_apply
    (A B : X → Matrix (Database X Y) (Database X Y) ℂ) (m m' : X × Y)
    (D D' : Database X Y) :
    (controlled A * standardOracle X Y * controlled B :
        Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) (m, D) (m', D') =
      ∑ D₁, if m = oracleEquiv (Database.lookup D₁) m' then A m'.1 D D₁ * B m'.1 D₁ D'
        else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single m']
  · refine Finset.sum_congr rfl fun D₁ _ ↦ ?_
    rw [standardOracle, tableOracle, mul_basisMatrix_apply, tableOracleEquiv_apply,
      controlled_apply, controlled_apply]
    split_ifs with h
    · subst h
      rfl
    all_goals simp_all
  · intro m₂ _ hm
    refine Finset.sum_eq_zero fun D₂ _ ↦ ?_
    simp [hm]
  · simp

end standard

/-! ## The compressed oracle -/

section compressed

variable [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- Compressing every cell of the database register is Hermitian on the joint register. -/
theorem conjTranspose_one_kronecker_compressAll :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y)ᴴ =
      (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y := by
  rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressAll]

/-- For nonempty `Y`, compressing every cell of the database register is an involution on the
joint register. -/
theorem one_kronecker_compressAll_mul_self [Nonempty Y] :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) = 1 := by
  rw [← mul_kronecker_mul, Matrix.one_mul, compressAll_mul_self, one_kronecker_one]

variable [AddCommGroup Y]

variable (X Y) in
/-- The compressed oracle on `(X × Y) × Database X Y`: the standard oracle conjugated by the
compression of every cell of the database register. -/
@[expose]
noncomputable def compressedOracle :
    Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) * standardOracle X Y *
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y)

/-- **Zhandry's form of the compressed oracle.** The compressed oracle is the standard oracle
conjugated by the compression of the queried cell only. -/
theorem compressedOracle_eq_controlled :
    compressedOracle X Y =
      controlled (compressAt Y) * standardOracle X Y * controlled (compressAt Y) := by
  ext ⟨m, D⟩ ⟨⟨x, y⟩, D'⟩
  have key (A : X → Matrix (Option Y) (Option Y) ℂ) :
      (∑ D₁ : Database X Y, if m = oracleEquiv (Database.lookup D₁) (x, y) then
          piKron A D D₁ * piKron A D₁ D' else 0) =
        ∏ j, ∑ z, (if j = x then (if m = (x, y + z.getD 0) then 1 else 0) else 1) *
          (A j (D j) z * A j z (D' j)) := by
    rw [← sum_mul_piKron_mul_piKron A A x (fun u ↦ if m = (x, y + u.getD 0) then 1 else 0)]
    refine Finset.sum_congr rfl fun D₁ _ ↦ ?_
    simp only [oracleEquiv_apply, Database.lookup_apply, boole_mul]
    exact if_congr Iff.rfl rfl rfl
  rw [compressedOracle, one_kronecker_eq_controlled,
    controlled_mul_standardOracle_mul_controlled_apply,
    controlled_mul_standardOracle_mul_controlled_apply]
  simp only [compressAll, compressAt]
  rw [key, key]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  by_cases hj : j = x
  · subst hj
    simp only [Pi.mulSingle_eq_same]
  · simp only [hj, ↓reduceIte, one_mul, Pi.mulSingle_eq_of_ne hj]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, cellCompress_mul_self, Matrix.mul_one]

/-- The compressed oracle is an isometry. -/
theorem conjTranspose_compressedOracle_mul_self :
    (compressedOracle X Y)ᴴ * compressedOracle X Y = 1 := by
  rw [compressedOracle, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_one_kronecker_compressAll]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y)
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y),
    one_kronecker_compressAll_mul_self, Matrix.one_mul, ← Matrix.mul_assoc (standardOracle X Y)ᴴ,
    conjTranspose_standardOracle_mul_self, Matrix.one_mul, one_kronecker_compressAll_mul_self]

/-- The compressed oracle is unitary. -/
theorem compressedOracle_mem_unitaryGroup :
    compressedOracle X Y ∈ unitaryGroup ((X × Y) × Database X Y) ℂ :=
  mem_unitaryGroup_iff'.mpr conjTranspose_compressedOracle_mul_self

/-- Compressing every cell intertwines the compressed oracle with the standard oracle:
`(1 ⊗ S^{⊗X}) cO = StO (1 ⊗ S^{⊗X})`. -/
theorem one_kronecker_compressAll_mul_compressedOracle :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) * compressedOracle X Y =
      standardOracle X Y * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) := by
  rw [compressedOracle, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    one_kronecker_compressAll_mul_self, Matrix.one_mul]

variable (X Y) in
/-- One query to the compressed oracle on the joint register, a lossless subinstrument. -/
@[expose]
noncomputable def compressedQuery :
    SubInstrument ((X × Y) × Database X Y) ((X × Y) × Database X Y) Unit :=
  SubInstrument.ofIsometry (compressedOracle X Y) conjTranspose_compressedOracle_mul_self

@[simp]
theorem branch_compressedQuery_apply (u : Unit) :
    (compressedQuery X Y).branch u = MatrixMap.conj (compressedOracle X Y) :=
  SubInstrument.branch_ofIsometry_apply ..

theorem lossless_compressedQuery : (compressedQuery X Y).Lossless :=
  SubInstrument.lossless_ofIsometry _ _

/-- Compressing every cell after a compressed query is the same as compressing every cell before
a standard query. -/
theorem branch_standardQuery_conj_one_kronecker_compressAll
    (ρ : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) :
    (standardQuery X Y).branch ()
        (MatrixMap.conj ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) ρ) =
      MatrixMap.conj ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y)
        ((compressedQuery X Y).branch () ρ) := by
  rw [branch_standardQuery_apply, branch_compressedQuery_apply, ← LinearMap.comp_apply,
    ← MatrixMap.conj_mul, ← one_kronecker_compressAll_mul_compressedOracle, MatrixMap.conj_mul,
    LinearMap.comp_apply]

end compressed

end Quantum
