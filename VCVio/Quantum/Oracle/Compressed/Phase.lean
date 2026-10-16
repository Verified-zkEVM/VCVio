/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import VCVio.Quantum.Oracle.Compressed.Truncation

/-!
# The compressed phase oracle

The compressed phase oracle is the compressed oracle seen through the Fourier transform of the
response register. Chiesa, Di, Hu and Zheng (*How to Prove Post-Quantum Security for Succinct
Non-Interactive Reductions*, ePrint 2025/2166, §4.3) take `Y = {0,1}^σ` and the Hadamard
transform `H_Y`. Here `Y` is any finite abelian group: the Fourier transform
`Quantum.fourierMatrix Y` sends `ℂ^Y` onto `ℂ^Ŷ`, where the Pontryagin dual `Ŷ = AddChar Y ℂ`
indexes the response register in the phase basis. Its entries are `|Y|^(-1/2) χ y`, and it is
unitary by the two orthogonality relations of characters. For `Y = (ZMod 2)^σ` the dual is
`Y` again and the transform is the Hadamard transform.

With `H = 1_X ⊗ F_Y ⊗ 1_D` (`Quantum.queryFourier X Y`), the phase oracle is
`O_ph = H O_std H†` (`Quantum.phaseOracle X Y`). It is block diagonal in the query register
`(x, χ)`, and on that block it acts on the cell `x` of the database alone, by the matrix
`Quantum.phaseCell Y χ = S diag(χ) S`, where `S` is the one-cell compression and an empty cell
carries the phase `1` (`Quantum.phaseOracle_apply`). Spelling out `phaseCell` gives
Lemma 4.5 of ePrint 2025/2166 (after Zhandry, Crypto 2019, and Chiesa, Manohar and Spooner, TCC
2019) for a general finite abelian group, with `N = |Y|`:

* for the trivial character, `O_ph |x, 0, D⟩ = |x, 0, D⟩`;
* for `χ ≠ 0` and `D x = ⊥`, `O_ph |x, χ, D⟩ = ∑ y, N^(-1/2) χ y • |x, χ, D[x ↦ y]⟩`;
* for `χ ≠ 0` and `D x = w`, `O_ph |x, χ, D⟩ = χ w • |x, χ, D⟩ + N^(-1/2) χ w • |x, χ, D - x⟩
  + ∑ y, N⁻¹ (1 - χ y - χ w) • |x, χ, D[x ↦ y]⟩`.

The truncated phase oracle `O_ph^(t) = P_size^(t) O_ph P_size^(t)` satisfies equation (4) of the
paper, `O_ph^(t) = H O_std^(t) H†` (`Quantum.truncatedPhaseOracle_eq`), because `P_size^(t)` acts
on the database register only.

## Main definitions

* `Quantum.fourierMatrix Y`, `Quantum.queryFourier X Y`.
* `Quantum.phaseCell Y χ`, `Quantum.phaseOracle X Y`.
* `Quantum.phaseSizeProjector X Y t`, `Quantum.truncatedPhaseOracle X Y t`.

## Main results

* `Quantum.fourierMatrix_mul_conjTranspose`, `Quantum.conjTranspose_fourierMatrix_mul`.
* `Quantum.phaseOracle_apply`, `Quantum.phaseOracle_mulVec_single`, and the three cases
  `Quantum.phaseOracle_mulVec_single_zero`, `Quantum.phaseOracle_mulVec_single_of_eq_none`,
  `Quantum.phaseOracle_mulVec_single_of_eq_some` (Lemma 4.5).
* `Quantum.truncatedPhaseOracle_eq` (equation (4)) and `Quantum.truncatedOracle_eq`.
-/

public section

open Matrix
open scoped Kronecker ComplexConjugate

namespace Quantum

/-! ## The Fourier transform of a finite abelian group -/

section fourier

variable (Y : Type*) [Fintype Y] [AddCommGroup Y]

/-- The Fourier transform of `ℂ^Y` onto `ℂ^Ŷ`, with `Ŷ = AddChar Y ℂ` the Pontryagin dual: the
entry at `(χ, y)` is `|Y|^(-1/2) χ y`. -/
@[expose]
noncomputable def fourierMatrix : Matrix (AddChar Y ℂ) Y ℂ :=
  of fun χ y ↦ cellAmp Y * χ y

@[simp]
theorem fourierMatrix_apply (χ : AddChar Y ℂ) (y : Y) :
    fourierMatrix Y χ y = cellAmp Y * χ y :=
  rfl

/-- The rows of the Fourier transform are orthonormal: the characters are orthogonal. -/
theorem fourierMatrix_mul_conjTranspose : fourierMatrix Y * (fourierMatrix Y)ᴴ = 1 := by
  have hN : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext χ ψ
  have hsum : ∑ y, χ y * conj (ψ y) = if χ = ψ then (Fintype.card Y : ℂ) else 0 := by
    simp_rw [← AddChar.map_neg_eq_conj, ← AddChar.inv_apply, ← AddChar.mul_apply]
    rw [AddChar.sum_eq_ite]
    congr 1
    exact propext ⟨fun h ↦ mul_inv_eq_one.mp h, fun h ↦ mul_inv_eq_one.mpr h⟩
  simp only [mul_apply, conjTranspose_apply, fourierMatrix_apply, star_mul', star_cellAmp,
    RCLike.star_def]
  calc ∑ y, cellAmp Y * χ y * (cellAmp Y * conj (ψ y))
      = cellAmp Y * cellAmp Y * ∑ y, χ y * conj (ψ y) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ by ring
    _ = (1 : Matrix (AddChar Y ℂ) (AddChar Y ℂ) ℂ) χ ψ := by
        rw [hsum, cellAmp_mul_self, one_apply]
        split_ifs <;> simp [hN]

/-- The columns of the Fourier transform are orthonormal: the characters separate the points of
`Y`, and there are `|Y|` of them. -/
theorem conjTranspose_fourierMatrix_mul [DecidableEq Y] :
    (fourierMatrix Y)ᴴ * fourierMatrix Y = 1 := by
  have hN : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext y y'
  have hsum : ∑ χ : AddChar Y ℂ, conj (χ y) * χ y' =
      if y = y' then (Fintype.card Y : ℂ) else 0 := by
    simp_rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    rw [AddChar.sum_apply_eq_ite]
    congr 1
    exact propext ⟨fun h ↦ (neg_add_eq_zero.mp h), fun h ↦ neg_add_eq_zero.mpr h⟩
  simp only [mul_apply, conjTranspose_apply, fourierMatrix_apply, star_mul', star_cellAmp,
    RCLike.star_def]
  calc ∑ χ : AddChar Y ℂ, cellAmp Y * conj (χ y) * (cellAmp Y * χ y')
      = cellAmp Y * cellAmp Y * ∑ χ : AddChar Y ℂ, conj (χ y) * χ y' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ ↦ by ring
    _ = (1 : Matrix Y Y ℂ) y y' := by
        rw [hsum, cellAmp_mul_self, one_apply]
        split_ifs <;> simp [hN]

end fourier

/-! ## The Fourier transform of the query register -/

section query

variable (X Y : Type*) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The Fourier transform `H = 1_X ⊗ F_Y ⊗ 1_D` of the response register of the joint register
`(X × Y) × Database X Y`, onto `(X × Ŷ) × Database X Y`. -/
@[expose]
noncomputable def queryFourier :
    Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  ((1 : Matrix X X ℂ) ⊗ₖ fourierMatrix Y) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ)

theorem queryFourier_apply (x' : X) (χ : AddChar Y ℂ) (D' : Database X Y) (x : X) (y : Y)
    (D : Database X Y) :
    queryFourier X Y ((x', χ), D') ((x, y), D) =
      if x' = x ∧ D' = D then cellAmp Y * χ y else 0 := by
  simp only [queryFourier, kroneckerMap_apply, one_apply, fourierMatrix_apply]
  split_ifs <;> simp_all

theorem queryFourier_mul_conjTranspose : queryFourier X Y * (queryFourier X Y)ᴴ = 1 := by
  rw [queryFourier, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    fourierMatrix_mul_conjTranspose, Matrix.one_mul, one_kronecker_one, one_kronecker_one]

theorem conjTranspose_queryFourier_mul : (queryFourier X Y)ᴴ * queryFourier X Y = 1 := by
  rw [queryFourier, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    conjTranspose_fourierMatrix_mul, Matrix.one_mul, one_kronecker_one, one_kronecker_one]

variable {X Y}

/-- The Fourier transform of the response register commutes with every operator on the database
register. -/
theorem queryFourier_mul_one_kronecker (K : Matrix (Database X Y) (Database X Y) ℂ) :
    queryFourier X Y * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ K) =
      ((1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ K) * queryFourier X Y := by
  rw [queryFourier, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- The inverse Fourier transform of the response register commutes with every operator on the
database register. -/
theorem one_kronecker_mul_conjTranspose_queryFourier
    (K : Matrix (Database X Y) (Database X Y) ℂ) :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ K) * (queryFourier X Y)ᴴ =
      (queryFourier X Y)ᴴ * ((1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ K) := by
  rw [queryFourier, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

variable (X Y) in
/-- The phase that the standard oracle imprints on a basis state of the phase basis:
`|x, χ⟩|D⟩ ↦ χ (D x) |x, χ⟩|D⟩`, where an empty cell reads as `0`. -/
@[expose]
noncomputable def phaseDiagonal :
    Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ :=
  diagonal fun p ↦ p.1.2 (p.2.lookup p.1.1)

/-- In the phase basis the standard oracle is diagonal: adding `D x` to the response register
multiplies the character `χ` by `χ (D x)`. -/
theorem queryFourier_mul_standardOracle :
    queryFourier X Y * standardOracle X Y = phaseDiagonal X Y * queryFourier X Y := by
  ext ⟨⟨x', χ⟩, D'⟩ ⟨⟨x, y⟩, D⟩
  rw [standardOracle, tableOracle, mul_basisMatrix_apply, phaseDiagonal, diagonal_mul,
    tableOracleEquiv_apply, oracleEquiv_apply, queryFourier_apply, queryFourier_apply]
  simp only
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [AddChar.map_add_eq_mul]
    ring
  · simp

/-- Conjugating the standard oracle by the Fourier transform gives the phase diagonal. -/
theorem queryFourier_mul_standardOracle_mul_conjTranspose :
    queryFourier X Y * standardOracle X Y * (queryFourier X Y)ᴴ = phaseDiagonal X Y := by
  rw [queryFourier_mul_standardOracle, Matrix.mul_assoc, queryFourier_mul_conjTranspose,
    Matrix.mul_one]

end query

/-! ## The phase oracle -/

section phase

variable (Y : Type*) [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The action of the phase oracle on the queried cell for the character `χ`: the one-cell
compression `S`, then the phase `χ` of the cell content (an empty cell carries the phase `1`),
then `S` again. -/
@[expose]
noncomputable def phaseCell (χ : AddChar Y ℂ) : Matrix (Option Y) (Option Y) ℂ :=
  cellCompress Y * diagonal (fun a ↦ χ (a.getD 0)) * cellCompress Y

theorem phaseCell_apply (χ : AddChar Y ℂ) (a' a : Option Y) :
    phaseCell Y χ a' a = ∑ b, cellCompress Y a' b * χ (b.getD 0) * cellCompress Y b a := by
  rw [phaseCell, mul_apply]
  simp_rw [mul_diagonal]

/-- For the trivial character the phase cell is the identity. -/
@[simp]
theorem phaseCell_zero : phaseCell Y 0 = 1 := by
  rw [phaseCell]
  simp only [AddChar.zero_apply, diagonal_one, Matrix.mul_one, cellCompress_mul_self]

variable {Y}

omit [DecidableEq Y] in
/-- The values of a nontrivial character sum to zero. -/
theorem sum_apply_eq_zero_of_ne_zero {χ : AddChar Y ℂ} (hχ : χ ≠ 0) : ∑ y, χ y = 0 := by
  rw [AddChar.sum_eq_ite]
  simp [hχ]

theorem phaseCell_none_none {χ : AddChar Y ℂ} (hχ : χ ≠ 0) : phaseCell Y χ none none = 0 := by
  have hs := sum_apply_eq_zero_of_ne_zero hχ
  rw [phaseCell_apply, Fintype.sum_option]
  simp only [cellCompress_none_none, cellCompress_none_some, cellCompress_some_none, zero_mul,
    zero_add]
  calc ∑ y, cellAmp Y * χ ((some y : Option Y).getD 0) * cellAmp Y
      = cellAmp Y * cellAmp Y * ∑ y, χ y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ by simp only [Option.getD_some]; ring
    _ = 0 := by rw [hs, mul_zero]

theorem phaseCell_some_none {χ : AddChar Y ℂ} (hχ : χ ≠ 0) (u : Y) :
    phaseCell Y χ (some u) none = cellAmp Y * χ u := by
  have hs := sum_apply_eq_zero_of_ne_zero hχ
  rw [phaseCell_apply, Fintype.sum_option]
  simp only [cellCompress_none_none, cellCompress_some_none, cellCompress_some_some, mul_zero,
    zero_add, Option.getD_some, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hs]
  ring

theorem phaseCell_none_some {χ : AddChar Y ℂ} (hχ : χ ≠ 0) (w : Y) :
    phaseCell Y χ none (some w) = cellAmp Y * χ w := by
  have hs := sum_apply_eq_zero_of_ne_zero hχ
  rw [phaseCell_apply, Fintype.sum_option]
  simp only [cellCompress_none_none, cellCompress_none_some, cellCompress_some_some, zero_mul,
    zero_add, Option.getD_some, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hs]
  ring

theorem phaseCell_some_some {χ : AddChar Y ℂ} (hχ : χ ≠ 0) (u w : Y) :
    phaseCell Y χ (some u) (some w) =
      (if u = w then χ u else 0) + (Fintype.card Y : ℂ)⁻¹ * (1 - χ u - χ w) := by
  have hs := sum_apply_eq_zero_of_ne_zero hχ
  rw [phaseCell_apply, Fintype.sum_option]
  simp only [cellCompress_some_none, cellCompress_none_some, cellCompress_some_some,
    Option.getD_none, AddChar.map_zero_eq_one, mul_one, cellAmp_mul_self, Option.getD_some]
  have e : ∀ y, ((if u = y then 1 else 0) - (Fintype.card Y : ℂ)⁻¹) * χ y *
      ((if y = w then 1 else 0) - (Fintype.card Y : ℂ)⁻¹) =
      (if u = y then (if y = w then χ y else 0) else 0) -
        (Fintype.card Y : ℂ)⁻¹ * (if u = y then χ y else 0) -
        (Fintype.card Y : ℂ)⁻¹ * (if y = w then χ y else 0) +
        (Fintype.card Y : ℂ)⁻¹ * (Fintype.card Y : ℂ)⁻¹ * χ y := by
    intro y
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun y _ ↦ e y]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_zero, add_zero]
  split_ifs with h
  · subst h
    ring
  · ring

end phase

/-- An entry of `(1 ⊗ A) diag(d) (1 ⊗ B)`: the first register is kept, and the second is
summed over the intermediate states. -/
theorem one_kronecker_mul_diagonal_mul_one_kronecker_apply {Q Z : Type*} [Fintype Q]
    [DecidableEq Q] [Fintype Z] [DecidableEq Z] (A B : Matrix Z Z ℂ) (d : Q × Z → ℂ)
    (q' : Q) (z' : Z) (q : Q) (z : Z) :
    (((1 : Matrix Q Q ℂ) ⊗ₖ A) * diagonal d * ((1 : Matrix Q Q ℂ) ⊗ₖ B)) (q', z') (q, z) =
      if q' = q then ∑ z₁, A z' z₁ * d (q, z₁) * B z₁ z else 0 := by
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single q]
  · simp only [mul_diagonal, kroneckerMap_apply, one_apply, ↓reduceIte, one_mul]
    split_ifs with h
    · subst h
      simp only [one_mul]
    · simp
  · intro b _ hb
    simp [hb]
  · simp

section phaseOracle

variable (X Y : Type*) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The compressed phase oracle `O_ph = H O_std H†` of ePrint 2025/2166, §4.3, on the joint
register `(X × Ŷ) × Database X Y`, with `H` the Fourier transform of the response register. -/
@[expose]
noncomputable def phaseOracle :
    Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ :=
  queryFourier X Y * compressedOracle X Y * (queryFourier X Y)ᴴ

/-- The phase oracle is the phase diagonal conjugated by the compression of every cell. -/
theorem phaseOracle_eq :
    phaseOracle X Y =
      ((1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ compressAll X Y) *
        phaseDiagonal X Y *
          ((1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ compressAll X Y) := by
  have h₁ := queryFourier_mul_one_kronecker (compressAll X Y)
  have h₂ := one_kronecker_mul_conjTranspose_queryFourier (compressAll X Y)
  calc phaseOracle X Y
      = (queryFourier X Y * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y)) *
          standardOracle X Y *
            (((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) * (queryFourier X Y)ᴴ) := by
        simp only [phaseOracle, compressedOracle, Matrix.mul_assoc]
    _ = _ := by
        rw [h₁, h₂, ← queryFourier_mul_standardOracle_mul_conjTranspose]
        simp only [Matrix.mul_assoc]

/-- **Entries of the phase oracle.** The phase oracle keeps the query register `(x, χ)` and every
cell of the database other than `x`, and acts on the cell `x` by `Quantum.phaseCell Y χ`. -/
theorem phaseOracle_apply (x' : X) (χ' : AddChar Y ℂ) (D' : Database X Y) (x : X)
    (χ : AddChar Y ℂ) (D : Database X Y) :
    phaseOracle X Y ((x', χ'), D') ((x, χ), D) =
      if (x', χ') = (x, χ) ∧ ∀ j ≠ x, D' j = D j then phaseCell Y χ (D' x) (D x) else 0 := by
  rw [phaseOracle_eq, phaseDiagonal, one_kronecker_mul_diagonal_mul_one_kronecker_apply]
  by_cases hm : (x', χ') = (x, χ)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
    have key := sum_mul_piKron_mul_piKron (fun _ : X ↦ cellCompress Y)
      (fun _ : X ↦ cellCompress Y) x' (fun z ↦ χ' (z.getD 0)) D' D
    have hsum : ∑ D₁ : Database X Y,
        compressAll X Y D' D₁ * χ' (D₁.lookup x') * compressAll X Y D₁ D =
          ∑ D₁ : X → Option Y, (fun z ↦ χ' (z.getD 0)) (D₁ x') *
            (piKron (fun _ ↦ cellCompress Y) D' D₁ * piKron (fun _ ↦ cellCompress Y) D₁ D) :=
      Finset.sum_congr rfl fun D₁ _ ↦ by rw [compressAll, Database.lookup_apply]; ring
    have hprod : ∀ j ∈ Finset.univ.erase x', (∑ z, (if j = x' then χ' (z.getD 0) else 1) *
        (cellCompress Y (D' j) z * cellCompress Y z (D j))) = if D' j = D j then 1 else 0 := by
      intro j hj
      simp only [Finset.ne_of_mem_erase hj, ↓reduceIte, one_mul]
      rw [← mul_apply, cellCompress_mul_self, one_apply]
    simp only [true_and, ↓reduceIte]
    rw [hsum, key, ← Finset.mul_prod_erase _ _ (Finset.mem_univ x'), Finset.prod_congr rfl hprod,
      Finset.prod_boole]
    simp only [↓reduceIte, Finset.mem_erase, Finset.mem_univ, and_true, phaseCell_apply]
    split_ifs
    · rw [mul_one]
      exact Finset.sum_congr rfl fun z _ ↦ by ring
    · rw [mul_zero]
  · simp [hm]

/-- **The phase oracle on a basis state.** A query of `|x, χ⟩|D⟩` replaces the cell `x` by the
column of `Quantum.phaseCell Y χ` at `D x`. -/
theorem phaseOracle_mulVec_single (x : X) (χ : AddChar Y ℂ) (D : Database X Y) :
    phaseOracle X Y *ᵥ Pi.single ((x, χ), D) 1 =
      ∑ a, phaseCell Y χ a (D x) • Pi.single ((x, χ), Function.update D x a) 1 := by
  ext ⟨⟨x', χ'⟩, D'⟩
  rw [mulVec_single_one, col_apply, phaseOracle_apply, Finset.sum_apply,
    Finset.sum_eq_single (D' x)]
  · simp only [Pi.smul_apply, Pi.single_apply, Prod.mk.injEq, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Function.eq_update_iff]
    by_cases hm : x' = x ∧ χ' = χ
    · obtain ⟨rfl, rfl⟩ := hm
      simp
    · simp only [hm, false_and, ite_false]
  · intro u _ hu
    simp [Function.eq_update_iff, Ne.symm hu]
  · simp

variable {X Y}

/-- **Lemma 4.5 of ePrint 2025/2166, trivial character.** The phase oracle fixes a basis state
whose phase register holds the trivial character. -/
theorem phaseOracle_mulVec_single_zero (x : X) (D : Database X Y) :
    phaseOracle X Y *ᵥ Pi.single ((x, 0), D) 1 = Pi.single ((x, 0), D) 1 := by
  rw [phaseOracle_mulVec_single, phaseCell_zero, Finset.sum_eq_single (D x)]
  · simp
  · intro a _ ha
    simp [one_apply_ne ha]
  · simp

/-- **Lemma 4.5 of ePrint 2025/2166, empty cell.** For a nontrivial character `χ`, querying an
empty cell superposes the values `y` with amplitudes `|Y|^(-1/2) χ y`. -/
theorem phaseOracle_mulVec_single_of_eq_none {χ : AddChar Y ℂ} (hχ : χ ≠ 0) {x : X}
    {D : Database X Y} (h : D x = none) :
    phaseOracle X Y *ᵥ Pi.single ((x, χ), D) 1 =
      ∑ y, (cellAmp Y * χ y) • Pi.single ((x, χ), Function.update D x (some y)) 1 := by
  rw [phaseOracle_mulVec_single, Fintype.sum_option, h, phaseCell_none_none hχ, zero_smul,
    zero_add]
  exact Finset.sum_congr rfl fun y _ ↦ by rw [phaseCell_some_none hχ]

/-- **Lemma 4.5 of ePrint 2025/2166, nonempty cell.** For a nontrivial character `χ`, querying a
cell holding `w` gives `χ w |D⟩ + |Y|^(-1/2) χ w |D - x⟩ + |Y|⁻¹ ∑ y, (1 - χ y - χ w) |D[x ↦ y]⟩`.
-/
theorem phaseOracle_mulVec_single_of_eq_some {χ : AddChar Y ℂ} (hχ : χ ≠ 0) {x : X}
    {D : Database X Y} {w : Y} (h : D x = some w) :
    phaseOracle X Y *ᵥ Pi.single ((x, χ), D) 1 =
      χ w • Pi.single ((x, χ), D) 1 +
        (cellAmp Y * χ w) • Pi.single ((x, χ), Function.update D x none) 1 +
          ∑ y, ((Fintype.card Y : ℂ)⁻¹ * (1 - χ y - χ w)) •
            Pi.single ((x, χ), Function.update D x (some y)) 1 := by
  have hD : Function.update D x (some w) = D := by
    rw [← h, Function.update_eq_self]
  rw [phaseOracle_mulVec_single, Fintype.sum_option, h, phaseCell_none_some hχ]
  simp only [phaseCell_some_some hχ, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hD]
  abel

/-! ## Truncation in the phase basis -/

variable (X Y) in
/-- The projector `P_size^(t)` onto databases with at most `t` nonempty cells, on the joint
register `(X × Ŷ) × Database X Y` of the phase basis. -/
@[expose]
noncomputable def phaseSizeProjector (t : ℕ) :
    Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ :=
  diagonal fun m ↦ if m.2.size ≤ t then 1 else 0

variable (X Y) in
/-- The truncated compressed phase oracle `O_ph^(t) = P_size^(t) O_ph P_size^(t)` of
ePrint 2025/2166, §4.3. -/
@[expose]
noncomputable def truncatedPhaseOracle (t : ℕ) :
    Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ :=
  phaseSizeProjector X Y t * phaseOracle X Y * phaseSizeProjector X Y t

omit [Fintype Y] [AddCommGroup Y] in
/-- The size projector of the standard basis acts on the database register only. -/
theorem sizeProjector_eq_one_kronecker (t : ℕ) :
    sizeProjector X Y t = (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      diagonal (fun D : Database X Y ↦ if D.size ≤ t then 1 else 0) := by
  ext ⟨m, D⟩ ⟨m', D'⟩
  simp only [sizeProjector, diagonal_apply, kroneckerMap_apply, one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype Y] in
/-- The size projector of the phase basis acts on the database register only. -/
theorem phaseSizeProjector_eq_one_kronecker (t : ℕ) :
    phaseSizeProjector X Y t = (1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ
      diagonal (fun D : Database X Y ↦ if D.size ≤ t then 1 else 0) := by
  ext ⟨m, D⟩ ⟨m', D'⟩
  simp only [phaseSizeProjector, diagonal_apply, kroneckerMap_apply, one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The entries of the truncated phase oracle: the entries of the phase oracle, kept when both
databases have at most `t` nonempty cells. -/
theorem truncatedPhaseOracle_apply (t : ℕ) (m' m : (X × AddChar Y ℂ) × Database X Y) :
    truncatedPhaseOracle X Y t m' m =
      (if m'.2.size ≤ t then 1 else 0) * phaseOracle X Y m' m *
        (if m.2.size ≤ t then 1 else 0) := by
  simp only [truncatedPhaseOracle, phaseSizeProjector, mul_diagonal, diagonal_mul]

/-- **Equation (4) of ePrint 2025/2166.** The truncated phase oracle is the truncated standard
oracle conjugated by the Fourier transform of the response register: `O_ph^(t) = H O^(t) H†`. -/
theorem truncatedPhaseOracle_eq (t : ℕ) :
    truncatedPhaseOracle X Y t =
      queryFourier X Y * truncatedOracle X Y t * (queryFourier X Y)ᴴ := by
  rw [truncatedPhaseOracle, truncatedOracle, phaseOracle, phaseSizeProjector_eq_one_kronecker,
    sizeProjector_eq_one_kronecker]
  simp only [← Matrix.mul_assoc]
  rw [← queryFourier_mul_one_kronecker]
  simp only [Matrix.mul_assoc]
  rw [one_kronecker_mul_conjTranspose_queryFourier]

/-- The truncated standard oracle is the truncated phase oracle conjugated back by the inverse
Fourier transform. -/
theorem truncatedOracle_eq (t : ℕ) :
    truncatedOracle X Y t =
      (queryFourier X Y)ᴴ * truncatedPhaseOracle X Y t * queryFourier X Y := by
  rw [truncatedPhaseOracle_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    conjTranspose_queryFourier_mul, Matrix.one_mul, Matrix.mul_assoc,
    conjTranspose_queryFourier_mul, Matrix.mul_one]

end phaseOracle

end Quantum
