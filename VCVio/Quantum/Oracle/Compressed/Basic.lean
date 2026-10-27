/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.Quantum.Oracle.Unitary

/-!
# Databases and the one-cell compression

The compressed oracle for a function `H : X → Y` keeps a purification of the random function in a
database register. Its computational basis is indexed by the partial tables
`Quantum.Database X Y := X → Option Y`, where `none` marks an empty cell. A query compresses and
decompresses the queried cell with the matrix `Quantum.cellCompress Y` on `ℂ^(Option Y)`. For
nonempty `Y` it is a unitary that swaps the empty cell `|⊥⟩` with the uniform superposition
`|φ₀⟩ = |Y|^(-1/2) ∑ y, |y⟩` and fixes every vector orthogonal to both.

This file follows the compressed oracle of Zhandry, *How to Record Quantum Queries, and
Applications to Quantum Indifferentiability* (Crypto 2019), in the presentation of Chiesa,
Di, Hu and Zheng, *How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions*
(ePrint 2025/2166), §4.3.

Operators on the whole database register that act cell by cell are pi-tensor products
`Quantum.piKron A`, with entries `∏ x, A x (D x) (D' x)`.

## Main definitions

* `Quantum.Database X Y`, with `Quantum.Database.empty`, `Quantum.Database.ofFun`,
  `Quantum.Database.lookup`, `Quantum.Database.size`, and the equivalence
  `Quantum.Database.equivQueryCache` with VCVio's `OracleSpec.QueryCache (X →ₒ Y)`.
* `Quantum.cellCompress Y`: the one-cell compression, Hermitian, and for nonempty `Y` a unitary
  involution (`Quantum.cellCompress_mul_self`, `Quantum.conjTranspose_cellCompress`).
* `Quantum.piKron A`: the pi-tensor product of a family of operators on one cell.
* `Quantum.compressAll X Y`: the compression of every cell; `Quantum.compressAt x`: the
  compression of the cell `x` only.

## Main results

* `Quantum.cellCompress_mulVec_bot`, `Quantum.cellCompress_mulVec_cellUniform`,
  `Quantum.cellCompress_mulVec_of_orthogonal`: for nonempty `Y`, the compression swaps `|⊥⟩` and
  `|φ₀⟩` and fixes their orthogonal complement.
* `Quantum.compressAll_mulVec_single_empty`: compressing every cell of the empty database gives
  the uniform superposition over the tables of total functions.
-/

public section

open Matrix
open scoped ComplexOrder

namespace Quantum

/-! ## The database register -/

/-- A database for functions `X → Y`: a partial table, with `none` at the empty cells. Databases
index the computational basis of the database register of the compressed oracle.

A database is the same data as VCVio's query cache `OracleSpec.QueryCache (X →ₒ Y)` for the single
oracle `X →ₒ Y`, the partial answer table of the classical lazy random oracle; the identification
is `Quantum.Database.equivQueryCache`. -/
abbrev Database (X Y : Type*) := X → Option Y

namespace Database

variable {X Y : Type*}

/-- The database with every cell empty. -/
@[expose]
def empty : Database X Y := fun _ ↦ none

/-- The total database that tabulates the function `H`. -/
@[expose]
def ofFun (H : X → Y) : Database X Y := fun x ↦ some (H x)

/-- The function read off a database, with value `0` at the empty cells. -/
@[expose]
def lookup [Zero Y] (D : Database X Y) (x : X) : Y := (D x).getD 0

/-- The number of nonempty cells of a database. -/
@[expose]
def size [Fintype X] (D : Database X Y) : ℕ := (Finset.univ.filter fun x ↦ (D x).isSome).card

@[simp]
theorem empty_apply (x : X) : (empty : Database X Y) x = none :=
  rfl

@[simp]
theorem ofFun_apply (H : X → Y) (x : X) : ofFun H x = some (H x) :=
  rfl

@[simp]
theorem lookup_apply [Zero Y] (D : Database X Y) (x : X) : D.lookup x = (D x).getD 0 :=
  rfl

/-- Reading a total database gives back the tabulated function. -/
@[simp]
theorem lookup_ofFun [Zero Y] (H : X → Y) : (ofFun H).lookup = H :=
  rfl

/-- Tabulation is injective. -/
theorem ofFun_injective : Function.Injective (ofFun : (X → Y) → Database X Y) :=
  fun _ _ h ↦ funext fun x ↦ Option.some_injective _ (congrFun h x)

/-- A database with no empty cell is the table of a function. -/
theorem exists_ofFun_eq {D : Database X Y} (hD : ∀ x, D x ≠ none) : ∃ H, ofFun H = D :=
  ⟨fun x ↦ (D x).get (Option.isSome_iff_ne_none.mpr (hD x)), funext fun x ↦ by simp [ofFun]⟩

/-- The empty database has size zero. -/
@[simp]
theorem size_empty [Fintype X] : (empty : Database X Y).size = 0 := by
  simp [size, empty]

/-- Changing one cell increases the size by at most one. -/
theorem size_update_le [Fintype X] [DecidableEq X] (D : Database X Y) (x : X) (u : Option Y) :
    size (Function.update D x u) ≤ D.size + 1 := by
  refine (Finset.card_le_card fun x' hx' ↦ ?_).trans (Finset.card_insert_le x _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hx' ⊢
  by_cases h : x' = x
  · exact Or.inl h
  · rw [Function.update_of_ne h] at hx'
    exact Or.inr hx'

/-- The number of nonempty cells is the cardinality of the database support. -/
theorem ncard_support_eq_size [Fintype X] (D : Database X Y) :
    {x | D x ≠ none}.ncard = D.size := by
  classical
  rw [size, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [Option.isSome_iff_ne_none]

/-- Databases are VCVio's query caches for the oracle `X →ₒ Y`, the partial answer tables of the
classical lazy random oracle. -/
@[expose]
def equivQueryCache {X Y : Type} : Database X Y ≃ OracleSpec.QueryCache (X →ₒ Y) :=
  OracleSpec.QueryCache.equivFn.symm

@[simp]
theorem equivQueryCache_apply {X Y : Type} (D : Database X Y) (x : X) :
    equivQueryCache D x = D x :=
  rfl

/-- The empty database is the empty cache. -/
@[simp]
theorem equivQueryCache_empty {X Y : Type} :
    equivQueryCache (empty : Database X Y) = ∅ :=
  rfl

end Database

/-! ## The one-cell compression -/

section cell

variable (Y : Type*) [Fintype Y]

/-- The amplitude `|Y|^(-1/2)` of each value in the uniform superposition over `Y`. -/
@[expose]
noncomputable def cellAmp : ℂ := ((Real.sqrt (Fintype.card Y))⁻¹ : ℝ)

/-- The amplitude is real. -/
@[simp]
theorem star_cellAmp : star (cellAmp Y) = cellAmp Y :=
  Complex.conj_ofReal _

/-- The square of the amplitude is `1 / |Y|`. -/
theorem cellAmp_mul_self : cellAmp Y * cellAmp Y = (Fintype.card Y : ℂ)⁻¹ := by
  rw [cellAmp, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- The uniform superposition `|φ₀⟩ = |Y|^(-1/2) ∑ y, |y⟩` on one cell, as a vector of
amplitudes. -/
@[expose]
noncomputable def cellUniform : Option Y → ℂ :=
  fun u ↦ u.elim 0 fun _ ↦ cellAmp Y

@[simp]
theorem cellUniform_none : cellUniform Y none = 0 :=
  rfl

@[simp]
theorem cellUniform_some (y : Y) : cellUniform Y (some y) = cellAmp Y :=
  rfl

variable [DecidableEq Y]

/-- The one-cell compression on `ℂ^(Option Y)`: the real symmetric matrix that, for nonempty `Y`,
swaps `|⊥⟩` with the uniform superposition `|φ₀⟩ = |Y|^(-1/2) ∑ y, |y⟩` and is the identity on
the orthogonal complement of both. Its entries are `0` at `(⊥, ⊥)`, `|Y|^(-1/2)` between `⊥` and
a value, and `δ y y' - 1 / |Y|` between two values. -/
@[expose]
noncomputable def cellCompress : Matrix (Option Y) (Option Y) ℂ :=
  Matrix.of fun u v ↦ match u, v with
    | none, none => 0
    | none, some _ => cellAmp Y
    | some _, none => cellAmp Y
    | some y, some y' => (if y = y' then 1 else 0) - (Fintype.card Y : ℂ)⁻¹

@[simp]
theorem cellCompress_none_none : cellCompress Y none none = 0 :=
  rfl

@[simp]
theorem cellCompress_none_some (y : Y) : cellCompress Y none (some y) = cellAmp Y :=
  rfl

@[simp]
theorem cellCompress_some_none (y : Y) : cellCompress Y (some y) none = cellAmp Y :=
  rfl

@[simp]
theorem cellCompress_some_some (y y' : Y) :
    cellCompress Y (some y) (some y') = (if y = y' then 1 else 0) - (Fintype.card Y : ℂ)⁻¹ :=
  rfl

/-- The one-cell compression is Hermitian. -/
theorem conjTranspose_cellCompress : (cellCompress Y)ᴴ = cellCompress Y := by
  ext u v
  rcases u with _ | y <;> rcases v with _ | y' <;>
    simp [Matrix.conjTranspose_apply, apply_ite (starRingEnd ℂ), eq_comm]

/-- For nonempty `Y`, the one-cell compression is an involution. -/
theorem cellCompress_mul_self [Nonempty Y] : cellCompress Y * cellCompress Y = 1 := by
  have hN : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc := cellAmp_mul_self Y
  ext u v
  rcases u with _ | y <;> rcases v with _ | y'
  · simp [Matrix.mul_apply, Fintype.sum_option, hc, hN]
  · simp only [Matrix.mul_apply, Fintype.sum_option, cellCompress_none_none,
      cellCompress_none_some, cellCompress_some_some, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, zero_mul, zero_add, Matrix.one_apply, reduceCtorEq,
      ite_false]
    rw [mul_left_comm, mul_inv_cancel₀ hN, mul_one, sub_self]
  · simp only [Matrix.mul_apply, Fintype.sum_option, cellCompress_none_none,
      cellCompress_some_none, cellCompress_some_some, sub_mul, Finset.sum_sub_distrib, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_zero, zero_add, Matrix.one_apply, reduceCtorEq,
      ite_false]
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul, sub_self]
  · simp only [Matrix.mul_apply, Fintype.sum_option, cellCompress_some_none,
      cellCompress_none_some, cellCompress_some_some, hc, Matrix.one_apply, Option.some.injEq]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, one_mul, mul_one,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    split_ifs <;> ring

/-- For nonempty `Y`, the one-cell compression is unitary. -/
theorem cellCompress_mem_unitaryGroup [Nonempty Y] :
    cellCompress Y ∈ Matrix.unitaryGroup (Option Y) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr <| by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_cellCompress, cellCompress_mul_self]

/-- The one-cell compression sends the empty cell to the uniform superposition. -/
theorem cellCompress_mulVec_bot :
    cellCompress Y *ᵥ Pi.single none 1 = cellUniform Y := by
  ext u
  rcases u with _ | y <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- For nonempty `Y`, the one-cell compression sends the uniform superposition to the empty
cell. -/
theorem cellCompress_mulVec_cellUniform [Nonempty Y] :
    cellCompress Y *ᵥ cellUniform Y = Pi.single none 1 := by
  have hN : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext u
  rcases u with _ | y
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_option, cellAmp_mul_self, hN]
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_option, sub_mul,
      Finset.sum_sub_distrib, hN]

/-- The one-cell compression fixes every vector orthogonal to `|⊥⟩` and to `|φ₀⟩`: a vector with
no `⊥` component whose values sum to zero. -/
theorem cellCompress_mulVec_of_orthogonal {ψ : Option Y → ℂ}
    (h₀ : ψ none = 0) (h₁ : ∑ y, ψ (some y) = 0) : cellCompress Y *ᵥ ψ = ψ := by
  ext u
  rcases u with _ | y
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_option, h₀, ← Finset.mul_sum,
      h₁]
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_option, h₀, sub_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, h₁]

end cell

/-! ## Pi-tensor products of one-cell operators -/

section piKron

variable {ι Z : Type*} [Fintype ι]

/-- The pi-tensor product `⨂ i, A i` of a family of operators on one cell, acting on the tables
`ι → Z`: its entry at `(D, D')` is `∏ i, A i (D i) (D' i)`. -/
@[expose]
def piKron (A : ι → Matrix Z Z ℂ) : Matrix (ι → Z) (ι → Z) ℂ :=
  Matrix.of fun D D' ↦ ∏ i, A i (D i) (D' i)

@[simp]
theorem piKron_apply (A : ι → Matrix Z Z ℂ) (D D' : ι → Z) :
    piKron A D D' = ∏ i, A i (D i) (D' i) :=
  rfl

/-- A sum over tables of a product of factors, one per cell, is the product over cells of the
sums of the factors. -/
theorem sum_prod_apply [DecidableEq ι] [Fintype Z] (F : ι → Z → ℂ) :
    ∑ D : ι → Z, ∏ i, F i (D i) = ∏ i, ∑ z, F i z :=
  (Fintype.prod_sum F).symm

/-- A product of pi-tensor products is the pi-tensor product of the products. -/
theorem piKron_mul [DecidableEq ι] [Fintype Z] (A B : ι → Matrix Z Z ℂ) :
    piKron A * piKron B = piKron fun i ↦ A i * B i := by
  ext D D''
  simp only [Matrix.mul_apply, piKron_apply, ← Finset.prod_mul_distrib]
  exact sum_prod_apply fun i z ↦ A i (D i) z * B i z (D'' i)

/-- The pi-tensor product of identities is the identity. -/
@[simp]
theorem piKron_one [DecidableEq Z] : piKron (fun _ : ι ↦ (1 : Matrix Z Z ℂ)) = 1 := by
  ext D D'
  simp only [piKron_apply, Matrix.one_apply, Fintype.prod_boole, funext_iff]

/-- The conjugate transpose of a pi-tensor product is the pi-tensor product of the conjugate
transposes. -/
theorem conjTranspose_piKron (A : ι → Matrix Z Z ℂ) :
    (piKron A)ᴴ = piKron fun i ↦ (A i)ᴴ := by
  ext D D'
  simp [Matrix.conjTranspose_apply, star_prod]

/-- The pi-tensor product of unitaries is unitary. -/
theorem piKron_mem_unitaryGroup [DecidableEq ι] [Fintype Z] [DecidableEq Z]
    {A : ι → Matrix Z Z ℂ}
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup Z ℂ) : piKron A ∈ Matrix.unitaryGroup (ι → Z) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr <| by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_piKron, piKron_mul]
    simp_rw [← Matrix.star_eq_conjTranspose, fun i ↦ Matrix.mem_unitaryGroup_iff.mp (hA i)]
    exact piKron_one

/-- The entry of a product of two pi-tensor products, weighted by a function of one cell of the
intermediate table, is a product over cells of one-cell sums. -/
theorem sum_mul_piKron_mul_piKron [DecidableEq ι] [Fintype Z] (A B : ι → Matrix Z Z ℂ) (i : ι)
    (g : Z → ℂ) (D D' : ι → Z) :
    ∑ D₁ : ι → Z, g (D₁ i) * (piKron A D D₁ * piKron B D₁ D') =
      ∏ j, ∑ z, (if j = i then g z else 1) * (A j (D j) z * B j z (D' j)) := by
  rw [← sum_prod_apply]
  refine Finset.sum_congr rfl fun D₁ _ ↦ ?_
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', piKron_apply, piKron_apply,
    ← Finset.prod_mul_distrib]

end piKron

/-! ## Compression of the database register -/

section compress

variable (X Y : Type*) [Fintype X] [Fintype Y] [DecidableEq Y]

/-- The compression of every cell of the database register: the pi-tensor product of copies of
`Quantum.cellCompress Y`. -/
@[expose]
noncomputable def compressAll : Matrix (Database X Y) (Database X Y) ℂ :=
  piKron fun _ : X ↦ cellCompress Y

variable {X} in
/-- The compression of the cell `x` of the database register, leaving the other cells
untouched. -/
@[expose]
noncomputable def compressAt [DecidableEq X] (x : X) : Matrix (Database X Y) (Database X Y) ℂ :=
  piKron (Pi.mulSingle x (cellCompress Y))

/-- Compressing every cell is Hermitian. -/
theorem conjTranspose_compressAll : (compressAll X Y)ᴴ = compressAll X Y := by
  rw [compressAll, conjTranspose_piKron]
  simp_rw [conjTranspose_cellCompress]

/-- For nonempty `Y`, compressing every cell is an involution. -/
theorem compressAll_mul_self [DecidableEq X] [Nonempty Y] :
    compressAll X Y * compressAll X Y = 1 := by
  rw [compressAll, piKron_mul]
  simp_rw [cellCompress_mul_self]
  exact piKron_one

/-- For nonempty `Y`, compressing every cell is unitary. -/
theorem compressAll_mem_unitaryGroup [DecidableEq X] [Nonempty Y] :
    compressAll X Y ∈ Matrix.unitaryGroup (Database X Y) ℂ :=
  piKron_mem_unitaryGroup fun _ ↦ cellCompress_mem_unitaryGroup Y

variable {X} in
/-- Compressing one cell is Hermitian. -/
theorem conjTranspose_compressAt [DecidableEq X] (x : X) : (compressAt Y x)ᴴ = compressAt Y x := by
  rw [compressAt, conjTranspose_piKron]
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp [conjTranspose_cellCompress]
  · simp [Pi.mulSingle_eq_of_ne h]

variable {X} in
/-- For nonempty `Y`, compressing one cell is an involution. -/
theorem compressAt_mul_self [DecidableEq X] [Nonempty Y] (x : X) :
    compressAt Y x * compressAt Y x = 1 := by
  rw [compressAt, piKron_mul]
  convert piKron_one (ι := X) (Z := Option Y) using 2
  funext x'
  by_cases h : x' = x
  · subst h
    simp [cellCompress_mul_self]
  · simp [Pi.mulSingle_eq_of_ne h]

variable {X} in
/-- For nonempty `Y`, compressing one cell is unitary. -/
theorem compressAt_mem_unitaryGroup [DecidableEq X] [Nonempty Y] (x : X) :
    compressAt Y x ∈ Matrix.unitaryGroup (Database X Y) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr <| by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_compressAt, compressAt_mul_self]

/-- The column of `compressAll` at the empty database: the amplitude of the table `D` is
`|Y|^(-|X|/2)` when `D` has no empty cell and `0` otherwise. -/
theorem compressAll_apply_empty (D : Database X Y) :
    compressAll X Y D Database.empty =
      if ∀ x, D x ≠ none then cellAmp Y ^ Fintype.card X else 0 := by
  rw [compressAll, piKron_apply]
  split_ifs with h
  · rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (h x)
    simp [hy]
  · simp only [not_forall, not_not] at h
    obtain ⟨x, hx⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

/-- The column of `compressAll` at the empty database, at a total table. -/
theorem compressAll_ofFun_empty (H : X → Y) :
    compressAll X Y (Database.ofFun H) Database.empty = cellAmp Y ^ Fintype.card X := by
  simp [compressAll_apply_empty]

/-- Compressing every cell of the empty database gives the uniform superposition over the tables
of total functions, `|Y|^(-|X|/2) ∑ H, |H⟩`. -/
theorem compressAll_mulVec_single_empty [DecidableEq X] :
    compressAll X Y *ᵥ Pi.single Database.empty 1 =
      ∑ H : X → Y, cellAmp Y ^ Fintype.card X • Pi.single (Database.ofFun H) 1 := by
  ext D
  rw [Matrix.mulVec_single_one, Matrix.col_apply, compressAll_apply_empty, Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · obtain ⟨H, rfl⟩ := Database.exists_ofFun_eq h
    simp [Database.ofFun_injective.eq_iff]
  · refine (Finset.sum_eq_zero fun H _ ↦ ?_).symm
    split_ifs with hH
    · exact absurd (fun x ↦ by simp [hH]) h
    · rfl

end compress

end Quantum
