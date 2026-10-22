/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.CheckedRead
public import VCVio.Quantum.Oracle.Compressed.CommutatorSharp
import Mathlib.Analysis.Matrix.Order

/-!
# Signed character blocks of a checked read

The validity response contributes a sign to each filled-cell phase. The empty-cell phase
remains one, including for the negative trivial character.
-/

public section

open Matrix
open scoped ComplexConjugate Matrix.Norms.L2Operator Kronecker

namespace Quantum

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The compressed empty-sector projector on one cell. -/
noncomputable def checkedReadEmptyCell : Matrix (Option Y) (Option Y) ℂ :=
  cellCompress Y * diagonal (fun a ↦ if a = none then 1 else 0) * cellCompress Y

/-- The signed character block of the read dilation. -/
noncomputable def checkedReadPhaseCell (χ : AddChar Y ℂ) (ε : ℂ) :
    Matrix (Option Y) (Option Y) ℂ :=
  ε • phaseCell Y χ + (1 - ε) • checkedReadEmptyCell

omit [AddCommGroup Y] in
/-- The compressed empty projector is the filled uniform projector. -/
theorem checkedReadEmptyCell_apply (a b : Option Y) :
    checkedReadEmptyCell a b = cellUniform Y a * cellUniform Y b := by
  rw [checkedReadEmptyCell, Matrix.mul_apply]
  simp only [mul_diagonal]
  rw [Finset.sum_eq_single none]
  · cases a <;> cases b <;> simp
  · intro c _ hc
    simp [hc]
  · simp

/-- The signed block is the compression of the diagonal phases `1, ε χ(y)`. -/
theorem checkedReadPhaseCell_eq (χ : AddChar Y ℂ) (ε : ℂ) :
    checkedReadPhaseCell χ ε = cellCompress Y *
      diagonal (fun a ↦ a.elim 1 (fun y ↦ ε * χ y)) * cellCompress Y := by
  have hd : diagonal (fun a : Option Y ↦ a.elim 1 (fun y ↦ ε * χ y)) =
      ε • diagonal (fun a ↦ χ (a.getD 0)) +
        (1 - ε) • diagonal (fun a ↦ if a = none then 1 else 0) := by
    ext a b
    by_cases h : a = b
    · subst b
      cases a <;> simp
    · simp [h]
  rw [hd]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    checkedReadPhaseCell, phaseCell, checkedReadEmptyCell]

/-- The negative trivial character is a reflection in the filled uniform vector. -/
theorem checkedReadPhaseCell_zero_neg_one :
    checkedReadPhaseCell (0 : AddChar Y ℂ) (-1) =
      (2 : ℂ) • checkedReadEmptyCell - 1 := by
  rw [checkedReadPhaseCell, phaseCell_zero]
  norm_num
  abel

/-- The positive trivial character acts identically. -/
theorem checkedReadPhaseCell_zero_one :
    checkedReadPhaseCell (0 : AddChar Y ℂ) 1 = 1 := by
  simp [checkedReadPhaseCell]

/-- A nontrivial signed block has an empty-column entry `ε χ(u) / √N`. -/
theorem checkedReadPhaseCell_some_none {χ : AddChar Y ℂ} (hχ : χ ≠ 0)
    (ε : ℂ) (u : Y) :
    checkedReadPhaseCell χ ε (some u) none = cellAmp Y * (ε * χ u) := by
  simp [checkedReadPhaseCell, checkedReadEmptyCell_apply, phaseCell_some_none hχ]
  ring

/-- The residual filled-row entries of a nontrivial signed block. -/
theorem checkedReadPhaseCell_some_some {χ : AddChar Y ℂ} (hχ : χ ≠ 0)
    (ε : ℂ) (u w : Y) :
    checkedReadPhaseCell χ ε (some u) (some w) =
      (if u = w then ε * χ u else 0) +
        (Fintype.card Y : ℂ)⁻¹ * (1 - ε * χ u - ε * χ w) := by
  simp only [checkedReadPhaseCell, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    checkedReadEmptyCell_apply, cellUniform_some, cellAmp_mul_self, phaseCell_some_some hχ]
  split_ifs <;> ring

omit [DecidableEq Y] in
/-- A unit-modulus multiple of a nontrivial character has the same quadratic sum law. -/
theorem sum_norm_sub_signed_char_sq {χ : AddChar Y ℂ} (hχ : χ ≠ 0)
    {ε : ℂ} (hε : ‖ε‖ = 1) (c : ℂ) :
    ∑ w, ‖c - ε * χ w‖ ^ 2 = Fintype.card Y * (‖c‖ ^ 2 + 1) := by
  have hs := sum_apply_eq_zero_of_ne_zero hχ
  have e : ∀ w, ‖c - ε * χ w‖ ^ 2 =
      (‖c‖ ^ 2 + 1) - 2 * (c * conj (ε * χ w)).re := fun w ↦ by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub,
      ← Complex.sq_norm (ε * χ w), norm_mul, hε, AddChar.norm_apply]
    ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum, ← map_sum,
    ← Finset.mul_sum, hs]
  simp

/-- The squared residual row norm for every nontrivial character and unit sign. -/
theorem sum_norm_checkedReadPhaseCell_sub_sq {χ : AddChar Y ℂ} (hχ : χ ≠ 0)
    {ε : ℂ} (hε : ‖ε‖ = 1) (u : Y) :
    ∑ a, ‖checkedReadPhaseCell χ ε (some u) a -
      if a = some u then ε * χ u else 0‖ ^ 2 =
        (4 - 2 * (ε * χ u).re) / Fintype.card Y := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∀ w : Y, checkedReadPhaseCell χ ε (some u) (some w) -
      (if some w = some u then ε * χ u else 0) =
        (Fintype.card Y : ℂ)⁻¹ * ((1 - ε * χ u) - ε * χ w) := fun w ↦ by
    rw [checkedReadPhaseCell_some_some hχ]
    by_cases h : u = w
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Fintype.sum_option]
  simp only [hw, reduceCtorEq, ite_false, sub_zero, checkedReadPhaseCell_some_none hχ,
    norm_mul, hε, AddChar.norm_apply, mul_one, norm_cellAmp_sq, mul_pow,
    ← Finset.mul_sum, sum_norm_sub_signed_char_sq hχ hε, norm_inv, Complex.norm_natCast]
  have h1 : ‖(1 : ℂ) - ε * χ u‖ ^ 2 = 2 - 2 * (ε * χ u).re := by
    rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm (ε * χ u),
      norm_mul, hε, AddChar.norm_apply]
    simp
    ring
  rw [h1]
  field_simp
  ring

/-- The negative trivial character has squared residual row norm `4 / N`. -/
theorem sum_norm_checkedReadPhaseCell_zero_neg_one_sub_sq (u : Y) :
    ∑ a, ‖checkedReadPhaseCell (0 : AddChar Y ℂ) (-1) (some u) a -
      if a = some u then -1 else 0‖ ^ 2 = 4 / Fintype.card Y := by
  have hN : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : ∀ a : Option Y, checkedReadPhaseCell (0 : AddChar Y ℂ) (-1) (some u) a -
      (if a = some u then -1 else 0) =
        match a with
        | none => 0
        | some _ => 2 * (Fintype.card Y : ℂ)⁻¹ := by
    intro a
    rw [checkedReadPhaseCell_zero_neg_one]
    cases a with
    | none => simp [checkedReadEmptyCell_apply]
    | some w =>
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        checkedReadEmptyCell_apply, cellUniform_some, cellAmp_mul_self,
        Matrix.one_apply, Option.some.injEq]
      by_cases h : u = w
      · subst w; simp
      · simp [h, Ne.symm h]
  simp_rw [he]
  rw [Fintype.sum_option]
  simp [norm_inv]
  field_simp
  norm_num

/-- Every signed character block has squared residual row norm at most `6 / N`. -/
theorem sum_norm_checkedReadPhaseCell_sub_sq_le (χ : AddChar Y ℂ)
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (u : Y) :
    ∑ a, ‖checkedReadPhaseCell χ ε (some u) a -
      if a = some u then ε * χ u else 0‖ ^ 2 ≤ 6 / Fintype.card Y := by
  by_cases hχ : χ = 0
  · subst χ
    rcases hε with rfl | rfl
    · simp only [checkedReadPhaseCell_zero_one, AddChar.zero_apply, mul_one,
        Matrix.one_apply]
      have hz : ∀ a : Option Y,
          (if some u = a then (1 : ℂ) else 0) - (if a = some u then 1 else 0) = 0 := by
        intro a
        simp [eq_comm]
      simp only [hz, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero]
      positivity
    · simpa only [AddChar.zero_apply, mul_one, sum_norm_checkedReadPhaseCell_zero_neg_one_sub_sq]
        using (show (4 : ℝ) / Fintype.card Y ≤ 6 / Fintype.card Y by gcongr; norm_num)
  · have hn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
    rw [sum_norm_checkedReadPhaseCell_sub_sq hχ hn]
    have hr : -1 ≤ (ε * χ u).re := by
      have h := Complex.abs_re_le_norm (ε * χ u)
      rw [norm_mul, hn, AddChar.norm_apply, mul_one] at h
      linarith [neg_abs_le (ε * χ u).re]
    gcongr
    linarith

/-- Signed phase cells are symmetric matrices. -/
theorem checkedReadPhaseCell_comm (χ : AddChar Y ℂ) (ε : ℂ) (a b : Option Y) :
    checkedReadPhaseCell χ ε a b = checkedReadPhaseCell χ ε b a := by
  simp only [checkedReadPhaseCell, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    checkedReadEmptyCell_apply, phaseCell_comm χ a b, mul_comm (cellUniform Y a)]

/-- Validity blocks have residual rows bounded by `4/N`. -/
theorem sum_norm_validityPhaseCell_sub_sq_le {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (u : Y) :
    ∑ a, ‖checkedReadPhaseCell (0 : AddChar Y ℂ) ε (some u) a -
      if a = some u then ε else 0‖ ^ 2 ≤ 4 / Fintype.card Y := by
  rcases hε with rfl | rfl
  · rw [checkedReadPhaseCell_zero_one]
    have he : ∀ a : Option Y,
        (1 : Matrix (Option Y) (Option Y) ℂ) (some u) a - (if a = some u then 1 else 0) = 0 :=
      fun a ↦ by simp [Matrix.one_apply, eq_comm]
    simp only [he, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero]
    positivity
  · exact (sum_norm_checkedReadPhaseCell_zero_neg_one_sub_sq u).le

section fourier

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Fourier transform of the response pair, with the original database as a spectator. -/
noncomputable def checkedReadFourier :
    Matrix ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y)
      ((X × (Y × ZMod 2)) × Database X Y) ℂ :=
  ((1 : Matrix X X ℂ) ⊗ₖ fourierMatrix (Y × ZMod 2)) ⊗ₖ
    (1 : Matrix (Database X Y) (Database X Y) ℂ)

/-- Entries of the response-pair Fourier transform. -/
theorem checkedReadFourier_apply (x' : X) (χ : AddChar (Y × ZMod 2) ℂ)
    (D' : Database X Y) (x : X) (z : Y × ZMod 2) (D : Database X Y) :
    checkedReadFourier ((x', χ), D') ((x, z), D) =
      if x' = x ∧ D' = D then cellAmp (Y × ZMod 2) * χ z else 0 := by
  simp only [checkedReadFourier, kroneckerMap_apply, one_apply, fourierMatrix_apply]
  split_ifs <;> simp_all

/-- The response-pair Fourier transform is a coisometry. -/
theorem checkedReadFourier_mul_conjTranspose :
    checkedReadFourier (X := X) (Y := Y) * (checkedReadFourier (X := X) (Y := Y))ᴴ = 1 := by
  rw [checkedReadFourier, conjTranspose_kronecker, conjTranspose_kronecker,
    conjTranspose_one, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, fourierMatrix_mul_conjTranspose, Matrix.one_mul,
    one_kronecker_one, one_kronecker_one]

/-- The response-pair Fourier transform is an isometry. -/
theorem conjTranspose_checkedReadFourier_mul :
    (checkedReadFourier (X := X) (Y := Y))ᴴ * checkedReadFourier (X := X) (Y := Y) = 1 := by
  rw [checkedReadFourier, conjTranspose_kronecker, conjTranspose_kronecker,
    conjTranspose_one, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, conjTranspose_fourierMatrix_mul, Matrix.one_mul,
    one_kronecker_one, one_kronecker_one]

/-- Fourier transformation diagonalizes a response translation on each table. -/
theorem checkedReadFourier_mul_tableOracle (f : Option Y → Y × ZMod 2) :
    checkedReadFourier (X := X) * tableOracle (fun D x ↦ f (D x)) =
      diagonal (fun p ↦ p.1.2 (f (p.2 p.1.1))) * checkedReadFourier := by
  ext ⟨⟨x', χ⟩, D'⟩ ⟨⟨x, z⟩, D⟩
  rw [tableOracle, mul_basisMatrix_apply, diagonal_mul, tableOracleEquiv_apply,
    oracleEquiv_apply, checkedReadFourier_apply, checkedReadFourier_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [AddChar.map_add_eq_mul]
    ring
  · simp

/-- In the Fourier basis, a compressed response translation is a compressed phase diagonal. -/
theorem checkedReadFourier_conj_translation (f : Option Y → Y × ZMod 2) :
    checkedReadFourier (X := X) * compressedReadTranslation f *
      (checkedReadFourier (X := X) (Y := Y))ᴴ =
      (1 ⊗ₖ compressAll X Y) *
        diagonal (fun p : (X × AddChar (Y × ZMod 2) ℂ) × Database X Y ↦
          p.1.2 (f (p.2 p.1.1))) * (1 ⊗ₖ compressAll X Y) := by
  have h₁ : checkedReadFourier (X := X) * (1 ⊗ₖ compressAll X Y) =
      (1 ⊗ₖ compressAll X Y) * checkedReadFourier := by
    simp only [checkedReadFourier, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have h₂ : (1 ⊗ₖ compressAll X Y) * (checkedReadFourier (X := X))ᴴ =
      (checkedReadFourier (X := X) (Y := Y))ᴴ * (1 ⊗ₖ compressAll X Y) := by
    simp only [checkedReadFourier, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [compressedReadTranslation_eq,
    ← Matrix.mul_assoc (checkedReadFourier (X := X) (Y := Y)),
    ← Matrix.mul_assoc (checkedReadFourier (X := X) (Y := Y)), h₁]
  simp only [Matrix.mul_assoc]
  rw [h₂, ← Matrix.mul_assoc (checkedReadFourier (X := X) (Y := Y)),
    checkedReadFourier_mul_tableOracle]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (checkedReadFourier (X := X) (Y := Y)),
    checkedReadFourier_mul_conjTranspose, Matrix.one_mul]

/-- Restriction of a response-pair character to the answer coordinate. -/
def checkedReadAnswerChar (χ : AddChar (Y × ZMod 2) ℂ) : AddChar Y ℂ :=
  χ.compAddMonoidHom (AddMonoidHom.inl Y (ZMod 2))

omit [Fintype Y] [DecidableEq Y] in
/-- The validity-coordinate character is a sign, including for a trivial answer character. -/
theorem checkedReadChar_sign (χ : AddChar (Y × ZMod 2) ℂ) :
    χ (0, 1) = 1 ∨ χ (0, 1) = -1 := by
  apply mul_self_eq_one_iff.mp
  rw [← AddChar.map_add_eq_mul]
  have he : ((0, 1) + (0, 1) : Y × ZMod 2) = 0 := by
    apply Prod.ext
    · simp
    · change (1 : ZMod 2) + 1 = 0
      decide
  rw [he, AddChar.map_zero_eq_one]

omit [Fintype Y] [DecidableEq Y] in
/-- The filled phase separates into an answer character and a validity sign. -/
theorem checkedReadChar_value (χ : AddChar (Y × ZMod 2) ℂ) (a : Option Y) :
    χ (checkedReadValue a) = a.elim 1 (fun y ↦ χ (0, 1) * checkedReadAnswerChar χ y) := by
  cases a with
  | none => exact χ.map_zero_eq_one
  | some y =>
    change χ (y, 1) = χ (0, 1) * χ (y, 0)
    rw [← AddChar.map_add_eq_mul]
    simp

/-- Fourier entries of a compressed response translation act on only the queried cell. -/
theorem checkedReadFourier_conj_translation_apply (f : Option Y → Y × ZMod 2)
    (x' : X) (χ' : AddChar (Y × ZMod 2) ℂ)
    (D' : Database X Y) (x : X) (χ : AddChar (Y × ZMod 2) ℂ) (D : Database X Y) :
    (checkedReadFourier (X := X) (Y := Y) * compressedReadTranslation f *
      (checkedReadFourier (X := X) (Y := Y))ᴴ :
        Matrix ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y)
          ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y) ℂ)
      ((x', χ'), D') ((x, χ), D) =
      if (x', χ') = (x, χ) ∧ ∀ j ≠ x, D' j = D j then
        (cellCompress Y * diagonal (fun a ↦ χ (f a)) * cellCompress Y :
          Matrix (Option Y) (Option Y) ℂ) (D' x) (D x) else 0 := by
  rw [checkedReadFourier_conj_translation,
    one_kronecker_mul_diagonal_mul_one_kronecker_apply]
  by_cases hm : (x', χ') = (x, χ)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
    have key := sum_mul_piKron_mul_piKron (fun _ : X ↦ cellCompress Y)
      (fun _ : X ↦ cellCompress Y) x' (fun z ↦ χ' (f z)) D' D
    have hsum : ∑ E : Database X Y,
        compressAll X Y D' E * χ' (f (E x')) * compressAll X Y E D =
          ∑ E : X → Option Y, χ' (f (E x')) *
            (piKron (fun _ ↦ cellCompress Y) D' E * piKron (fun _ ↦ cellCompress Y) E D) :=
      Finset.sum_congr rfl fun E _ ↦ by rw [compressAll]; ring
    have hprod : ∀ j ∈ Finset.univ.erase x',
        (∑ z, (if j = x' then χ' (f z) else 1) *
          (cellCompress Y (D' j) z * cellCompress Y z (D j))) =
            if D' j = D j then 1 else 0 := by
      intro j hj
      simp only [Finset.ne_of_mem_erase hj, ite_false, one_mul]
      rw [← mul_apply, cellCompress_mul_self, one_apply]
    simp only [true_and, ite_true]
    rw [hsum, key, ← Finset.mul_prod_erase _ _ (Finset.mem_univ x'),
      Finset.prod_congr rfl hprod, Finset.prod_boole]
    simp only [ite_true, Finset.mem_erase, Finset.mem_univ, and_true]
    split_ifs
    · rw [mul_one, Matrix.mul_apply]
      simp only [mul_diagonal]
      exact Finset.sum_congr rfl fun z _ ↦ by ring
    · rw [mul_zero]
  · simp [hm]

/-- Fourier entries of the checked-read dilation are the signed one-cell matrices. -/
theorem checkedReadFourier_conj_apply (x' : X) (χ' : AddChar (Y × ZMod 2) ℂ)
    (D' : Database X Y) (x : X) (χ : AddChar (Y × ZMod 2) ℂ) (D : Database X Y) :
    (checkedReadFourier (X := X) (Y := Y) * checkedReadUnitary *
      (checkedReadFourier (X := X) (Y := Y))ᴴ :
        Matrix ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y)
          ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y) ℂ)
      ((x', χ'), D') ((x, χ), D) =
      if (x', χ') = (x, χ) ∧ ∀ j ≠ x, D' j = D j then
        checkedReadPhaseCell (checkedReadAnswerChar χ) (χ (0, 1)) (D' x) (D x) else 0 := by
  rw [checkedReadUnitary_eq, checkedReadFourier_conj_translation_apply]
  split_ifs
  · rw [checkedReadPhaseCell_eq]
    simp only [checkedReadChar_value]
  · rfl

end fourier

section cellBlocks

variable {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]
variable {Q : Type*} [Fintype Q] [DecidableEq Q] {ι : Type*} [DecidableEq ι]

/-- Basis states in a cell block are parameterized by the cell content. -/
theorem sum_ite_checkedReadBlock {M : Type*} [AddCommMonoid M] (x : X) (q : Q)
    {r : Database X Y} (hr : r x = none) (g : (X × Q) × Database X Y → M) :
    ∑ m : (X × Q) × Database X Y,
      (if (m.1, Function.update m.2 m.1.1 none) = ((x, q), r) then g m else 0) =
      ∑ a, g ((x, q), Function.update r x a) :=
  sum_ite_cellBlock x q hr g

/-- Filled states whose labels differ from the erased database, below the cutoff. -/
private def ReadBad (π : Database X Y → ι) (t : ℕ) (m : (X × Q) × Database X Y) : Prop :=
  Database.size (Function.update m.2 m.1.1 none) < t ∧
    π m.2 ≠ π (Function.update m.2 m.1.1 none)

private noncomputable instance (π : Database X Y → ι) (t : ℕ) :
    DecidablePred (ReadBad (Q := Q) π t) := Classical.decPred _

omit [DecidableEq ι] in
/-- The norm of the label-changing rows is controlled by the instability and a cell row bound. -/
private theorem readBad_rows_le [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (t : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {A : Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ}
    (hA : ∀ i j, A i j ≠ 0 →
      (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none))
    (hrow : ∀ x q (r : Database X Y), r x = none → r.size < t → ∀ u,
      ∑ m, ‖A ((x, q), Function.update r x (some u)) m‖ ^ 2 ≤ c / Fintype.card Y) :
    ‖diagonal (fun m ↦ if ReadBad π t m then (1 : ℂ) else 0) * A‖ ≤
      √(c * (Database.instability π t).toReal) := by
  classical
  convert l2_opNorm_labelChangingRows_le π t (fun _ _ ↦ True) hc hA
    (fun x q r hr hs _ u ↦ hrow x q r hr hs u) using 1
  congr 2
  congr 1
  funext m
  simp only [ReadBad, true_and]
  split_ifs with h
  · exact ite_eq_left h
  · exact ite_eq_right h

/-- Symmetric cell blocks have a label-preserving approximation from their residual row bound. -/
private theorem exists_readApprox [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (t : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (A : Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ)
    (d : (X × Q) × Database X Y → ℂ)
    (hA : ∀ i j, A i j ≠ 0 →
      (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none))
    (hsym : ∀ i j, A i j = A j i)
    (hinactive : ∀ i j, A i j ≠ 0 →
      ¬ Database.size (Function.update j.2 j.1.1 none) < t → i = j)
    (hrow : ∀ x q (r : Database X Y), r x = none → r.size < t → ∀ u,
      ∑ m, ‖(A - diagonal d) ((x, q), Function.update r x (some u)) m‖ ^ 2 ≤
        c / Fintype.card Y) :
    ∃ S, pinch (fun m ↦ π m.2) S = S ∧
      ‖A - S‖ ^ 2 ≤ c * (Database.instability π t).toReal := by
  classical
  have hM : ∀ i j, (A - diagonal d) i j ≠ 0 →
      (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none) := by
    intro i j hij
    by_cases he : i = j
    · simp [he]
    · exact hA i j (by simpa [Matrix.sub_apply, diagonal_apply_ne _ he] using hij)
  have hmSym : ∀ i j, (A - diagonal d) i j = (A - diagonal d) j i := by
    intro i j
    by_cases he : i = j
    · simp [he]
    · simp [Matrix.sub_apply, diagonal_apply_ne _ he, diagonal_apply_ne _ (Ne.symm he), hsym]
  have hr := readBad_rows_le π t hc hM hrow
  have hl : ‖(A - diagonal d) *
      diagonal (fun m ↦ if ReadBad π t m then (1 : ℂ) else 0)‖ ≤
        √(c * (Database.instability π t).toReal) := by
    have hp : (diagonal (fun m : (X × Q) × Database X Y ↦
        if ReadBad π t m then (1 : ℂ) else 0))ᴴ =
        diagonal (fun m ↦ if ReadBad π t m then (1 : ℂ) else 0) := by
      rw [diagonal_conjTranspose]
      congr 1
      funext m
      by_cases h : ReadBad π t m <;> simp [h]
    rw [← l2_opNorm_conjTranspose, conjTranspose_mul, hp]
    refine readBad_rows_le (Q := Q) π t hc (A := (A - diagonal d)ᴴ) ?_ ?_
    · intro i j hij
      exact (hM j i (by simpa only [conjTranspose_apply, star_ne_zero] using hij)).symm
    · intro x q r hr hs u
      simpa only [conjTranspose_apply, norm_star, hmSym] using hrow x q r hr hs u
  let γ : (X × Q) × Database X Y →
      ((X × Q) × Database X Y) ⊕ ((X × Q) × Database X Y) := fun m ↦
    if Database.size (Function.update m.2 m.1.1 none) < t then
      Sum.inl (m.1, Function.update m.2 m.1.1 none) else Sum.inr m
  refine exists_pinch_eq_sub_sq_le_of_completion
    (fun m ↦ π m.2) γ (ReadBad π t) A d (mul_nonneg hc ENNReal.toReal_nonneg) hr hl ?_ ?_
  · intro i j hij hne
    have hb := hA i j hij
    by_cases hs : Database.size (Function.update j.2 j.1.1 none) < t
    · have hi : Database.size (Function.update i.2 i.1.1 none) < t := by
        rw [(Prod.mk.inj hb).2]
        exact hs
      simp only [γ, hi, hs, ite_true, hb]
    · exact False.elim (hne (hinactive i j hij hs))
  · intro i j hij hne hi hj
    dsimp only [γ] at hij
    split_ifs at hij with hi' hj'
    · have hb := Sum.inl_injective hij
      have hei : π i.2 = π (Function.update i.2 i.1.1 none) := by
        by_contra h
        exact hi ⟨hi', h⟩
      have hej : π j.2 = π (Function.update j.2 j.1.1 none) := by
        by_contra h
        exact hj ⟨hj', h⟩
      rw [hei, hej, (Prod.mk.inj hb).2]
    · exact False.elim (hne (Sum.inr_injective hij))

/-- A population-truncated operator that acts on one cell in each response block. -/
noncomputable def readCellTruncation
    (K : Q → Matrix (Option Y) (Option Y) ℂ) (t : ℕ) :
    Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ :=
  fun i j ↦ if i.2.size ≤ t ∧ j.2.size ≤ t ∧ i.1 = j.1 ∧
    ∀ z ≠ j.1.1, i.2 z = j.2 z then K j.1.2 (i.2 j.1.1) (j.2 j.1.1) else 0

omit [Fintype Y] [Fintype Q] in
private theorem readCellTruncation_block (K : Q → Matrix (Option Y) (Option Y) ℂ) (t : ℕ)
    {i j : (X × Q) × Database X Y} (h : readCellTruncation K t i j ≠ 0) :
    (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none) := by
  dsimp only [readCellTruncation] at h
  split_ifs at h with hc
  · refine Prod.ext ?_ ?_
    · exact hc.2.2.1
    rw [hc.2.2.1]
    funext z
    by_cases hz : z = j.1.1
    · simp [hz]
    · simp [Function.update_of_ne hz, hc.2.2.2 z hz]
  · exact False.elim (h rfl)

omit [Fintype Y] [Fintype Q] in
private theorem readCellTruncation_inactive (K : Q → Matrix (Option Y) (Option Y) ℂ) (t : ℕ)
    {i j : (X × Q) × Database X Y} (h : readCellTruncation K t i j ≠ 0)
    (hs : ¬Database.size (Function.update j.2 j.1.1 none) < t) : i = j := by
  have hb := readCellTruncation_block K t h
  have hn : ∀ D : Database X Y,
      Function.update D j.1.1 none = Function.update j.2 j.1.1 none →
      D.size ≤ t → D j.1.1 = none := by
    intro D hd ht
    by_contra hne
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne
    have he := Database.size_eq_size_update_none_add_one hu
    rw [hd] at he
    omega
  dsimp only [readCellTruncation] at h
  split_ifs at h with hc
  · apply Prod.ext hc.2.2.1
    have hei : i.2 j.1.1 = none := hn i.2 (by simpa [hc.2.2.1] using congrArg Prod.snd hb) hc.1
    have hej : j.2 j.1.1 = none := hn j.2 rfl hc.2.1
    funext z
    by_cases hz : z = j.1.1
    · simp [hz, hei, hej]
    · exact hc.2.2.2 z hz
  · exact False.elim (h rfl)

omit [Fintype Y] [Fintype Q] in
private theorem readCellTruncation_update (K : Q → Matrix (Option Y) (Option Y) ℂ)
    {t : ℕ} (x : X) (q : Q) {r : Database X Y} (hs : r.size < t) (a b : Option Y) :
    readCellTruncation K t ((x, q), Function.update r x a) ((x, q), Function.update r x b) =
      K q a b := by
  have hm : ∀ a, Database.size (Function.update r x a) ≤ t := fun a ↦
    (Database.size_update_le r x a).trans hs
  have he : ∀ z ≠ x, Function.update r x a z = Function.update r x b z := by
    intro z hz
    rw [Function.update_of_ne hz, Function.update_of_ne hz]
  rw [readCellTruncation, ite_eq_left ⟨hm a, hm b, rfl, he⟩]
  simp only [Function.update_self]

/-- A symmetric cell operator with residual rows bounded by `c/N` has a global
label-preserving approximation at squared distance at most `c I`. -/
theorem exists_pinch_eq_readCellTruncation_sub_sq_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (t : ℕ) (K : Q → Matrix (Option Y) (Option Y) ℂ)
    (d : Q → Option Y → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hK : ∀ q a b, K q a b = K q b a)
    (hrow : ∀ q u, ∑ a, ‖K q (some u) a -
      if a = some u then d q (some u) else 0‖ ^ 2 ≤ c / Fintype.card Y) :
    ∃ S, pinch (fun m : (X × Q) × Database X Y ↦ π m.2) S = S ∧
      ‖readCellTruncation K t - S‖ ^ 2 ≤ c * (Database.instability π t).toReal := by
  classical
  refine exists_readApprox π t hc (readCellTruncation K t)
    (fun m ↦ d m.1.2 (m.2 m.1.1))
    (fun _ _ h ↦ readCellTruncation_block K t h) ?_
    (fun _ _ h hs ↦ readCellTruncation_inactive K t h hs) ?_
  · rintro ⟨⟨x, q⟩, D⟩ ⟨⟨x', q'⟩, D'⟩
    by_cases hq : (x, q) = (x', q')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      simp [readCellTruncation, hK, and_left_comm, eq_comm]
    · simp [readCellTruncation, hq, Ne.symm hq]
  · intro x q r hr hs u
    let A : Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ :=
      readCellTruncation (X := X) K t -
      diagonal (fun m : (X × Q) × Database X Y ↦ d m.1.2 (m.2 m.1.1))
    have hb : ∀ m, A ((x, q), Function.update r x (some u)) m ≠ 0 →
        (m.1, Function.update m.2 m.1.1 none) = ((x, q), r) := by
      intro m hm
      by_cases he : ((x, q), Function.update r x (some u)) = m
      · rw [← he]
        simp [Function.update_idem, Database.update_none_of_eq_none hr]
      have hA : readCellTruncation K t ((x, q), Function.update r x (some u)) m ≠ 0 := by
        simpa [A, Matrix.sub_apply, diagonal_apply_ne _ he] using hm
      have h := readCellTruncation_block K t hA
      simpa [Function.update_idem, Database.update_none_of_eq_none hr] using h.symm
    have hsum : ∑ m, ‖A ((x, q), Function.update r x (some u)) m‖ ^ 2 =
        ∑ a, ‖A ((x, q), Function.update r x (some u)) ((x, q), Function.update r x a)‖ ^ 2 := by
      refine Eq.trans ?_ (sum_ite_checkedReadBlock x q hr
        (fun m ↦ ‖A ((x, q), Function.update r x (some u)) m‖ ^ 2))
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      split_ifs with h
      · rfl
      · have hz : A ((x, q), Function.update r x (some u)) m = 0 := by
          by_contra hn
          exact h (hb m hn)
        simp [hz]
    change ∑ m, ‖A ((x, q), Function.update r x (some u)) m‖ ^ 2 ≤ _
    rw [hsum]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ ↦ ?_) (hrow q u)
    have he : ((x, q), Function.update r x (some u)) =
        ((x, q), Function.update r x a) ↔ a = some u := by
      constructor
      · intro h
        simpa using (congrFun (congrArg Prod.snd h) x).symm
      · rintro rfl; rfl
    simp only [A, Matrix.sub_apply, readCellTruncation_update K x q hs, diagonal_apply, he]
    split_ifs with h
    · subst a
      simp
    · simp

variable [AddCommGroup Y]

/-- The checked-read phase operator restricted to databases of population at most `t`. -/
noncomputable def truncatedCheckedReadPhase (t : ℕ) :
    Matrix ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y)
      ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y) ℂ :=
  readCellTruncation (fun χ ↦ checkedReadPhaseCell (checkedReadAnswerChar χ) (χ (0, 1))) t

/-- The validity phase operator restricted to databases of population at most `t`. -/
noncomputable def truncatedValidityPhase (t : ℕ) :
    Matrix ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y)
      ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y) ℂ :=
  readCellTruncation (fun χ ↦ checkedReadPhaseCell (0 : AddChar Y ℂ) (χ (0, 1))) t

/-- A label-preserving approximation to the checked-read phase operator has squared error `6 I`. -/
theorem exists_pinch_eq_truncatedCheckedReadPhase_sub_sq_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)] (π : Database X Y → ι) (t : ℕ) :
    ∃ S, pinch (fun m : (X × AddChar (Y × ZMod 2) ℂ) × Database X Y ↦ π m.2) S = S ∧
      ‖truncatedCheckedReadPhase t - S‖ ^ 2 ≤ 6 * (Database.instability π t).toReal := by
  apply exists_pinch_eq_readCellTruncation_sub_sq_le π t _
    (fun χ a ↦ a.elim 1 (fun y ↦ χ (0, 1) * checkedReadAnswerChar χ y)) (by norm_num)
  · exact fun χ a b ↦ checkedReadPhaseCell_comm _ _ a b
  · exact fun χ u ↦ sum_norm_checkedReadPhaseCell_sub_sq_le _ (checkedReadChar_sign χ) u

/-- A label-preserving approximation to validity has squared error `4 I`. -/
theorem exists_pinch_eq_truncatedValidityPhase_sub_sq_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)] (π : Database X Y → ι) (t : ℕ) :
    ∃ S, pinch (fun m : (X × AddChar (Y × ZMod 2) ℂ) × Database X Y ↦ π m.2) S = S ∧
      ‖truncatedValidityPhase t - S‖ ^ 2 ≤ 4 * (Database.instability π t).toReal := by
  apply exists_pinch_eq_readCellTruncation_sub_sq_le π t _
    (fun χ a ↦ a.elim 1 (fun _ ↦ χ (0, 1))) (by norm_num)
  · exact fun χ a b ↦ checkedReadPhaseCell_comm _ _ a b
  · exact fun χ u ↦ sum_norm_validityPhaseCell_sub_sq_le (checkedReadChar_sign χ) u

/-- The truncated checked read in the response basis. -/
noncomputable def truncatedCheckedRead (t : ℕ) :
    Matrix ((X × (Y × ZMod 2)) × Database X Y)
      ((X × (Y × ZMod 2)) × Database X Y) ℂ :=
  (checkedReadFourier (X := X) (Y := Y))ᴴ * truncatedCheckedReadPhase t * checkedReadFourier

/-- The truncated validity operation in the response basis. -/
noncomputable def truncatedValidity (t : ℕ) :
    Matrix ((X × (Y × ZMod 2)) × Database X Y)
      ((X × (Y × ZMod 2)) × Database X Y) ℂ :=
  (checkedReadFourier (X := X) (Y := Y))ᴴ * truncatedValidityPhase t * checkedReadFourier

/-- Population projection for an arbitrary response register over the original database. -/
noncomputable def readPopulationProjector (t : ℕ) :
    Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ :=
  diagonal (fun m ↦ if m.2.size ≤ t then 1 else 0)

private theorem checkedReadFourier_mul_population (t : ℕ) :
    checkedReadFourier (X := X) (Y := Y) * readPopulationProjector t =
      readPopulationProjector t * checkedReadFourier (X := X) (Y := Y) := by
  ext ⟨⟨x', χ⟩, D'⟩ ⟨⟨x, z⟩, D⟩
  simp only [readPopulationProjector, mul_diagonal, diagonal_mul, checkedReadFourier_apply]
  by_cases h : x' = x ∧ D' = D
  · simp [h, mul_comm]
  · simp [h]

private theorem readCellTruncation_fourier (f : Option Y → Y × ZMod 2) (t : ℕ) :
    readCellTruncation (X := X)
      (fun χ : AddChar (Y × ZMod 2) ℂ ↦ cellCompress Y *
        diagonal (fun a ↦ χ (f a)) * cellCompress Y) t =
      readPopulationProjector t *
        (checkedReadFourier * compressedReadTranslation f *
          (checkedReadFourier (X := X) (Y := Y))ᴴ) *
          readPopulationProjector t := by
  ext ⟨⟨x', χ'⟩, D'⟩ ⟨⟨x, χ⟩, D⟩
  rw [readPopulationProjector, mul_diagonal, diagonal_mul,
    checkedReadFourier_conj_translation_apply]
  simp only [readCellTruncation]
  split_ifs <;> simp_all

private theorem readCellTruncation_unfourier (f : Option Y → Y × ZMod 2) (t : ℕ) :
    (checkedReadFourier (X := X) (Y := Y))ᴴ *
        readCellTruncation (fun χ : AddChar (Y × ZMod 2) ℂ ↦ cellCompress Y *
          diagonal (fun a ↦ χ (f a)) * cellCompress Y) t * checkedReadFourier =
      readPopulationProjector t * compressedReadTranslation f * readPopulationProjector t := by
  have h := checkedReadFourier_mul_population (X := X) (Y := Y) t
  have hp : (readPopulationProjector (X := X) (Y := Y) (Q := Y × ZMod 2) t)ᴴ =
      readPopulationProjector t := by
    rw [readPopulationProjector, diagonal_conjTranspose]
    congr 1
    funext m
    split_ifs <;> simp_all
  have hp' : (readPopulationProjector (X := X) (Y := Y)
      (Q := AddChar (Y × ZMod 2) ℂ) t)ᴴ = readPopulationProjector t := by
    rw [readPopulationProjector, diagonal_conjTranspose]
    congr 1
    funext m
    split_ifs <;> simp_all
  have h' := congrArg Matrix.conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, hp, hp'] at h'
  rw [readCellTruncation_fourier]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (checkedReadFourier (X := X) (Y := Y))ᴴ,
    ← h', Matrix.mul_assoc, ← Matrix.mul_assoc (checkedReadFourier (X := X) (Y := Y))ᴴ,
    conjTranspose_checkedReadFourier_mul, Matrix.one_mul]
  have ht : (checkedReadFourier (X := X) (Y := Y))ᴴ *
      (readPopulationProjector t * checkedReadFourier) = readPopulationProjector t := by
    calc _ = (checkedReadFourier (X := X) (Y := Y))ᴴ *
        (checkedReadFourier * readPopulationProjector t) := congrArg _ h.symm
      _ = _ := by rw [← Matrix.mul_assoc, conjTranspose_checkedReadFourier_mul, Matrix.one_mul]
  rw [ht]

/-- The response-basis truncation is exactly population projection before and after the dilation. -/
theorem truncatedCheckedRead_eq (t : ℕ) :
    truncatedCheckedRead (X := X) (Y := Y) t =
      readPopulationProjector t * checkedReadUnitary * readPopulationProjector t := by
  have hK : (fun χ : AddChar (Y × ZMod 2) ℂ ↦
      checkedReadPhaseCell (checkedReadAnswerChar χ) (χ (0, 1))) =
      (fun χ ↦ cellCompress Y * diagonal (fun a ↦ χ (checkedReadValue a)) * cellCompress Y) := by
    funext χ
    rw [checkedReadPhaseCell_eq]
    simp only [checkedReadChar_value]
  rw [truncatedCheckedRead, truncatedCheckedReadPhase, hK, readCellTruncation_unfourier,
    checkedReadUnitary_eq]

/-- Validity truncation is population projection before and after the validity translation. -/
theorem truncatedValidity_eq (t : ℕ) :
    truncatedValidity (X := X) (Y := Y) t =
      readPopulationProjector t * checkedReadValidity * readPopulationProjector t := by
  have hv : ∀ (χ : AddChar (Y × ZMod 2) ℂ) (a : Option Y),
      χ (0, (checkedReadValue a).2) = a.elim 1 (fun _ ↦ χ (0, 1)) := by
    intro χ a
    cases a with
    | none => exact χ.map_zero_eq_one
    | some y => rfl
  have hK : (fun χ : AddChar (Y × ZMod 2) ℂ ↦
      checkedReadPhaseCell (0 : AddChar Y ℂ) (χ (0, 1))) =
      (fun χ ↦ cellCompress Y *
        diagonal (fun a ↦ χ (0, (checkedReadValue a).2)) * cellCompress Y) := by
    funext χ
    rw [checkedReadPhaseCell_eq]
    simp only [hv, AddChar.zero_apply, mul_one]
  rw [truncatedValidity, truncatedValidityPhase, hK, readCellTruncation_unfourier,
    checkedReadValidity_eq]

private theorem readApprox_fourier (π : Database X Y → ι)
    {A S : Matrix ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y)
      ((X × AddChar (Y × ZMod 2) ℂ) × Database X Y) ℂ}
    (hS : pinch (fun m ↦ π m.2) S = S) {c : ℝ} (hc : ‖A - S‖ ^ 2 ≤ c) :
    ∃ T, pinch (fun m : (X × (Y × ZMod 2)) × Database X Y ↦ π m.2) T = T ∧
      ‖(checkedReadFourier (X := X) (Y := Y))ᴴ * A * checkedReadFourier - T‖ ^ 2 ≤ c := by
  have hU : ∀ a b, (checkedReadFourier (X := X) (Y := Y))ᴴ a b ≠ 0 → π a.2 = π b.2 := by
    rintro ⟨⟨x, y⟩, D⟩ ⟨⟨x', χ⟩, D'⟩ h
    rw [conjTranspose_apply, checkedReadFourier_apply] at h
    by_cases he : x' = x ∧ D' = D
    · simp [he.2]
    · simp [he] at h
  have he := mul_pinch_mul_conjTranspose
    (fun m : (X × (Y × ZMod 2)) × Database X Y ↦ π m.2)
    (fun m : (X × AddChar (Y × ZMod 2) ℂ) × Database X Y ↦ π m.2) hU S
  rw [conjTranspose_conjTranspose, hS] at he
  refine ⟨(checkedReadFourier (X := X) (Y := Y))ᴴ * S * checkedReadFourier, he.symm, ?_⟩
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_conjTranspose_mul_mul_le
    (checkedReadFourier_mul_conjTranspose (X := X) (Y := Y)) _) 2).trans hc

/-- The complete read has a label-preserving approximation of squared error at most `6 I`. -/
theorem exists_pinch_eq_truncatedCheckedRead_sub_sq_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)] (π : Database X Y → ι) (t : ℕ) :
    ∃ S, pinch (fun m : (X × (Y × ZMod 2)) × Database X Y ↦ π m.2) S = S ∧
      ‖truncatedCheckedRead t - S‖ ^ 2 ≤ 6 * (Database.instability π t).toReal := by
  obtain ⟨S, hS, hc⟩ := exists_pinch_eq_truncatedCheckedReadPhase_sub_sq_le π t
  exact readApprox_fourier π hS hc

/-- Validity has a label-preserving approximation of squared error at most `4 I`. -/
theorem exists_pinch_eq_truncatedValidity_sub_sq_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)] (π : Database X Y → ι) (t : ℕ) :
    ∃ S, pinch (fun m : (X × (Y × ZMod 2)) × Database X Y ↦ π m.2) S = S ∧
      ‖truncatedValidity t - S‖ ^ 2 ≤ 4 * (Database.instability π t).toReal := by
  obtain ⟨S, hS, hc⟩ := exists_pinch_eq_truncatedValidityPhase_sub_sq_le π t
  exact readApprox_fourier π hS hc

omit [DecidableEq ι] in
/-- The truncated complete read has label-controlled squared commutator bound `24 I`. -/
theorem l2_opNorm_commutator_checkedRead_sq_le_twentyFour_mul
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    {E : Type*} [Fintype E] [DecidableEq E] (π : Database X Y → ι) (t : ℕ)
    {W : ι → Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2)
    (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1.2) W‖ ^ 2 ≤
      24 * (Database.instability π t).toReal := by
  classical
  obtain ⟨S, hS, hd⟩ := exists_pinch_eq_truncatedCheckedRead_sub_sq_le π t
  have h := l2_opNorm_commutator_labelControlled_kronecker_one_le hS hW hU hA
  calc _ ≤ (2 * ‖truncatedCheckedRead t - S‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖truncatedCheckedRead t - S‖ ^ 2 := by ring
    _ ≤ 4 * (6 * (Database.instability π t).toReal) := by gcongr
    _ = 24 * (Database.instability π t).toReal := by ring

omit [DecidableEq ι] in
/-- The truncated validity operation has label-controlled squared commutator bound `16 I`. -/
theorem l2_opNorm_commutator_validity_sq_le_sixteen_mul
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    {E : Type*} [Fintype E] [DecidableEq E] (π : Database X Y → ι) (t : ℕ)
    {W : ι → Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2)
    (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedValidity t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedValidity t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedValidity t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedValidity t ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1.2) W‖ ^ 2 ≤
      16 * (Database.instability π t).toReal := by
  classical
  obtain ⟨S, hS, hd⟩ := exists_pinch_eq_truncatedValidity_sub_sq_le π t
  have h := l2_opNorm_commutator_labelControlled_kronecker_one_le hS hW hU hA
  calc _ ≤ (2 * ‖truncatedValidity t - S‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖truncatedValidity t - S‖ ^ 2 := by ring
    _ ≤ 4 * (4 * (Database.instability π t).toReal) := by gcongr
    _ = 16 * (Database.instability π t).toReal := by ring


open scoped ComplexOrder

private theorem read_trace_rectangular_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (σ : Matrix n n ℂ) (hσ : σ.PosSemidef) :
    (A * σ * Aᴴ).trace.re ≤ ‖A‖ ^ 2 * σ.trace.re := by
  open scoped MatrixOrder in
    have hh := (posSemidef_conjTranspose_mul_self A).isHermitian
    have h := (Matrix.le_iff.mp (IsSelfAdjoint.le_algebraMap_norm_self (Aᴴ * A)
      hh)).trace_mul_re_nonneg hσ
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h
    rw [Matrix.trace_mul_cycle]
    simpa [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.trace_smul,
      l2_opNorm_conjTranspose_mul_self, ← Complex.ofReal_mul, pow_two] using h

private theorem read_sum_trace_diagonal {n α : Type*} [Fintype n] [DecidableEq n]
    [Fintype α] [DecidableEq α] (f : n → α) (B : Matrix n n ℂ) :
    ∑ a, (diagonal (fun i ↦ if f i = a then (1 : ℂ) else 0) * B *
      diagonal (fun i ↦ if f i = a then (1 : ℂ) else 0)).trace = B.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp


/-- Decode a retained response into the classical outcome of the checked read. -/
def checkedReadOutcome (z : Y × ZMod 2) : Option Y :=
  if z.2 = 0 then none else some z.1

/-- Orthogonal output projection retaining a checked-read outcome. -/
noncomputable def checkedReadOutcomeProjector {E : Type*} [DecidableEq E]
    (a : Option Y) : Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ :=
  diagonal (fun i ↦ if checkedReadOutcome i.1.1.2 = a then 1 else 0)

/-- The retained-outcome branch of the truncated read commutator. -/
noncomputable def truncatedCheckedReadDefect {E : Type*} [Fintype E] [DecidableEq E]
    (t : ℕ) (U : Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ) (a : Option Y) :=
  checkedReadOutcomeProjector a *
    ((truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * U -
      U * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)))

/-- Retaining the orthogonal outcomes preserves the sum of defect traces exactly. -/
theorem sum_trace_truncatedCheckedReadDefect_eq {E : Type*} [Fintype E] [DecidableEq E]
    (t : ℕ) (U σ : Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ) :
    ∑ a, (truncatedCheckedReadDefect t U a * σ *
      (truncatedCheckedReadDefect t U a)ᴴ).trace =
    (((truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * U -
      U * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ))) * σ *
      ((truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * U -
      U * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)))ᴴ).trace := by
  have hp : ∀ a : Option Y,
      (checkedReadOutcomeProjector (X := X) (E := E) a)ᴴ = checkedReadOutcomeProjector a := by
    intro a
    rw [checkedReadOutcomeProjector, diagonal_conjTranspose]
    congr 1
    funext i
    split_ifs <;> simp_all
  simp only [truncatedCheckedReadDefect, conjTranspose_mul, hp]
  simp only [Matrix.mul_assoc]
  convert read_sum_trace_diagonal (fun i ↦ checkedReadOutcome i.1.1.2)
    (((truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * U -
      U * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ))) * σ *
      ((truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * U -
      U * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)))ᴴ) using 1 <;>
    simp only [checkedReadOutcomeProjector, Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- The sum over retained read outcomes costs `24 I`, independently of their number.
The address register and its correlations with the state remain arbitrary. -/
theorem sum_trace_truncatedCheckedReadDefect_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    {E : Type*} [Fintype E] [DecidableEq E] (π : Database X Y → ι) (t : ℕ)
    {W : ι → Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2)
    (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ)) * W k)
    (σ : Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ) (hσ : σ.PosSemidef) :
    ∑ a, (truncatedCheckedReadDefect t (labelControlled (fun i ↦ π i.1.2) W) a * σ *
      (truncatedCheckedReadDefect t (labelControlled (fun i ↦ π i.1.2) W) a)ᴴ).trace.re ≤
      24 * (Database.instability π t).toReal * σ.trace.re := by
  rw [← Complex.re_sum, sum_trace_truncatedCheckedReadDefect_eq]
  refine (read_trace_rectangular_le _ _ hσ).trans ?_
  rw [norm_sub_rev]
  exact mul_le_mul_of_nonneg_right
    (l2_opNorm_commutator_checkedRead_sq_le_twentyFour_mul π t hW hU hA) hσ.trace_re_nonneg


private theorem read_controlled_commutator_apply {n E κ : Type*}
    [Fintype n] [DecidableEq n] [Fintype E] [DecidableEq E]
    (A : Matrix n n ℂ) (π : n → κ) (U : κ → Matrix E E ℂ)
    (i j : n) (e f : E) :
    (((A ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1)
      (fun k ↦ (1 : Matrix n n ℂ) ⊗ₖ U k) -
      labelControlled (fun a ↦ π a.1) (fun k ↦ (1 : Matrix n n ℂ) ⊗ₖ U k) *
      (A ⊗ₖ (1 : Matrix E E ℂ))) : Matrix (n × E) (n × E) ℂ) (i, e) (j, f) =
      A i j * (U (π j) e f - U (π i) e f) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, labelControlled_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_sub, mul_comm]

/-- A checked projector with its query address retained as a classical control. -/
noncomputable def selectedCheckedReadProjector (a : Option Y) :
    Matrix (X × Database X Y) (X × Database X Y) ℂ :=
  fun i j ↦ if i.1 = j.1 then checkedReadProjector i.1 a i.2 j.2 else 0

omit [AddCommGroup Y] in
/-- Selecting an address preserves its classical control and applies its checked projector. -/
theorem selectedCheckedReadProjector_apply (a : Option Y)
    (i j : X × Database X Y) :
    selectedCheckedReadProjector a i j =
      if i.1 = j.1 then checkedReadProjector i.1 a i.2 j.2 else 0 := by
  unfold selectedCheckedReadProjector
  rfl

/-- The defect of the checked instrument against a database-label-controlled auxiliary unitary. -/
noncomputable def checkedReadDefect {E : Type*} [Fintype E] [DecidableEq E]
    (π : Database X Y → ι) (U : ι → Matrix E E ℂ) (a : Option Y) :
    Matrix ((X × Database X Y) × E) ((X × Database X Y) × E) ℂ :=
  (selectedCheckedReadProjector a ⊗ₖ (1 : Matrix E E ℂ)) *
    labelControlled (fun i ↦ π i.1.2)
      (fun k ↦ (1 : Matrix (X × Database X Y) (X × Database X Y) ℂ) ⊗ₖ U k) -
  labelControlled (fun i ↦ π i.1.2)
      (fun k ↦ (1 : Matrix (X × Database X Y) (X × Database X Y) ℂ) ⊗ₖ U k) *
    (selectedCheckedReadProjector a ⊗ₖ (1 : Matrix E E ℂ))


private theorem read_embedding_norm_le {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a → b) (hi : Function.Injective e) :
    ‖(1 : Matrix b b ℂ).submatrix id e‖ ≤ 1 := by
  apply l2_opNorm_le_one_of_conjTranspose_mul_self
  rw [conjTranspose_submatrix, conjTranspose_one]
  simpa using (one_submatrix_mul e (Equiv.refl b)
    ((1 : Matrix b b ℂ).submatrix id e)).trans (submatrix_one e hi)

private theorem read_submatrix_norm_le {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q]
    (A : Matrix m n ℂ) (f : p → m) (g : q → n)
    (hf : Function.Injective f) (hg : Function.Injective g) : ‖A.submatrix f g‖ ≤ ‖A‖ := by
  classical
  have hid : A.submatrix f g = ((1 : Matrix m m ℂ).submatrix id f)ᴴ * A *
      (1 : Matrix n n ℂ).submatrix id g := by
    rw [conjTranspose_submatrix, conjTranspose_one]
    have h1 : (1 : Matrix m m ℂ).submatrix f id * A = A.submatrix f id := by
      simpa using one_submatrix_mul f (Equiv.refl m) A
    rw [h1]
    simpa using (mul_submatrix_one (Equiv.refl n) g (A.submatrix f id)).symm
  rw [hid]
  calc _ ≤ (‖((1 : Matrix m m ℂ).submatrix id f)ᴴ‖ * ‖A‖) *
        ‖(1 : Matrix n n ℂ).submatrix id g‖ :=
      (l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * ‖A‖) * 1 := by
      rw [l2_opNorm_conjTranspose]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (read_embedding_norm_le f hf) (norm_nonneg _))
        (read_embedding_norm_le g hg) (norm_nonneg _) (by positivity)
    _ = _ := by ring


private theorem truncatedCheckedRead_fresh (t : ℕ) (a : Option Y)
    (x x' : X) (D D' : Database X Y) :
    truncatedCheckedRead t ((x, checkedReadValue a), D) ((x', 0), D') =
      if D.size ≤ t ∧ D'.size ≤ t then
        selectedCheckedReadProjector a (x, D) (x', D') else 0 := by
  have he : checkedReadUnitary ((x, checkedReadValue a), D) ((x', 0), D') =
      selectedCheckedReadProjector a (x, D) (x', D') := by
    by_cases hx : x = x'
    · subst x'
      simp only [selectedCheckedReadProjector]
      cases a with
      | none => exact checkedReadUnitary_fresh_none x D D'
      | some y => exact checkedReadUnitary_fresh_some x y D D'
    · rw [checkedReadUnitary_fresh_of_ne _ _ _ _ _ hx]
      simp [selectedCheckedReadProjector, hx]
  rw [truncatedCheckedRead_eq]
  simp only [readPopulationProjector, mul_diagonal, diagonal_mul, he]
  split_ifs <;> simp_all

private theorem selectedCheckedReadProjector_growth (a : Option Y)
    (i j : X × Database X Y) (h : selectedCheckedReadProjector a i j ≠ 0) :
    i.2.size ≤ j.2.size + 1 := by
  simp only [selectedCheckedReadProjector] at h
  split_ifs at h with hx
  · exact size_le_of_checkedReadProjector_ne_zero i.1 a h
  · exact (h rfl).elim

private theorem read_stinespring_trace {n α : Type*} [Fintype n] [Fintype α]
    (D : α → Matrix n n ℂ) (σ : Matrix n n ℂ) :
    (MatrixMap.stinespring D * σ * (MatrixMap.stinespring D)ᴴ).trace =
      ∑ a, (D a * σ * (D a)ᴴ).trace := by
  rw [Matrix.trace_mul_cycle, MatrixMap.conjTranspose_stinespring_mul_stinespring,
    Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (Matrix.trace_mul_cycle _ _ _).symm


private def readResponseIndex {E : Type*} (a : Option Y)
    (i : (X × Database X Y) × E) : ((X × (Y × ZMod 2)) × Database X Y) × E :=
  (((i.1.1, checkedReadValue a), i.1.2), i.2)

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
private theorem readResponseIndex_injective {E : Type*} :
    Function.Injective (fun i : ((X × Database X Y) × E) × Option Y ↦
      readResponseIndex i.2 i.1) := by
  rintro ⟨⟨⟨x, D⟩, e⟩, a⟩ ⟨⟨⟨x', D'⟩, e'⟩, a'⟩ h
  simp only [readResponseIndex, Prod.mk.injEq] at h
  have ha := checkedReadValue_injective h.1.1.2
  simp [h.1.1.1, h.1.2, h.2, ha]

private noncomputable def readInputCutoff {E : Type*} [DecidableEq E] (p : ℕ) :
    Matrix ((X × Database X Y) × E) ((X × Database X Y) × E) ℂ :=
  diagonal (fun i ↦ if i.1.2.size ≤ p then 1 else 0)

omit [AddCommGroup Y] in
private theorem readInputCutoff_norm_le {E : Type*} [Fintype E] [DecidableEq E] (p : ℕ) :
    ‖readInputCutoff (X := X) (Y := Y) (E := E) p‖ ≤ 1 := by
  rw [readInputCutoff, l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  split_ifs <;> simp

private noncomputable def readFullDefect {E : Type*} [Fintype E] [DecidableEq E]
    (π : Database X Y → ι) (U : ι → Matrix E E ℂ) (t : ℕ) :
    Matrix (((X × (Y × ZMod 2)) × Database X Y) × E)
      (((X × (Y × ZMod 2)) × Database X Y) × E) ℂ :=
  (truncatedCheckedRead (X := X) (Y := Y) t ⊗ₖ (1 : Matrix E E ℂ)) *
    labelControlled (fun i ↦ π i.1.2)
      (fun k ↦ (1 : Matrix ((X × (Y × ZMod 2)) × Database X Y)
        ((X × (Y × ZMod 2)) × Database X Y) ℂ) ⊗ₖ U k) -
  labelControlled (fun i ↦ π i.1.2)
      (fun k ↦ (1 : Matrix ((X × (Y × ZMod 2)) × Database X Y)
        ((X × (Y × ZMod 2)) × Database X Y) ℂ) ⊗ₖ U k) *
    (truncatedCheckedRead t ⊗ₖ (1 : Matrix E E ℂ))

omit [DecidableEq ι] [AddCommGroup Y] in
/-- Each defect entry is the checked projector entry times the difference of label unitaries. -/
theorem checkedReadDefect_apply {E : Type*} [Fintype E] [DecidableEq E]
    (π : Database X Y → ι) (U : ι → Matrix E E ℂ) (a : Option Y)
    (i j : X × Database X Y) (e f : E) :
    checkedReadDefect π U a (i, e) (j, f) =
      selectedCheckedReadProjector a i j * (U (π j.2) e f - U (π i.2) e f) := by
  unfold checkedReadDefect
  exact read_controlled_commutator_apply (selectedCheckedReadProjector a)
    (fun i : X × Database X Y ↦ π i.2) U i j e f

omit [DecidableEq ι] in
private theorem readFullDefect_apply {E : Type*} [Fintype E] [DecidableEq E]
    (π : Database X Y → ι) (U : ι → Matrix E E ℂ) (t : ℕ)
    (i j : (X × (Y × ZMod 2)) × Database X Y) (e f : E) :
    readFullDefect π U t (i, e) (j, f) =
      truncatedCheckedRead t i j * (U (π j.2) e f - U (π i.2) e f) := by
  unfold readFullDefect
  exact read_controlled_commutator_apply (truncatedCheckedRead t)
    (fun i : (X × (Y × ZMod 2)) × Database X Y ↦ π i.2) U i j e f

omit [DecidableEq ι] in
private theorem readDefectStack_eq {E : Type*} [Fintype E] [DecidableEq E]
    (π : Database X Y → ι) (U : ι → Matrix E E ℂ) (p : ℕ) :
    MatrixMap.stinespring (checkedReadDefect π U) * readInputCutoff p =
      (readFullDefect π U (p + 1)).submatrix
        (fun i : ((X × Database X Y) × E) × Option Y ↦ readResponseIndex i.2 i.1)
        (readResponseIndex none) * readInputCutoff p := by
  ext ⟨⟨⟨x, D⟩, e⟩, a⟩ ⟨⟨x', D'⟩, e'⟩
  simp only [readInputCutoff, mul_diagonal, MatrixMap.stinespring_apply,
    Matrix.submatrix_apply, readResponseIndex, checkedReadDefect_apply, readFullDefect_apply]
  rw [show checkedReadValue (none : Option Y) = 0 from rfl, truncatedCheckedRead_fresh]
  by_cases hj : D'.size ≤ p
  · have hj' : D'.size ≤ p + 1 := by omega
    by_cases hJ : selectedCheckedReadProjector a (x, D) (x', D') = 0
    · simp [hj, hJ]
    · have hi := selectedCheckedReadProjector_growth a (x, D) (x', D') hJ
      change D.size ≤ D'.size + 1 at hi
      have hi' : D.size ≤ p + 1 := by omega
      simp [hj, hi', hj']
  · simp [hj]


omit [DecidableEq ι] in
/-- All checked-outcome defects, stacked together and restricted to population at most `p`,
have squared norm at most `24 I(π,p+1)`. The address register may be correlated with the input. -/
theorem l2_opNorm_checkedReadDefectStack_sq_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    {E : Type*} [Fintype E] [DecidableEq E] (π : Database X Y → ι)
    (U : ι → Matrix E E ℂ) (hU : ∀ k, U k ∈ unitaryGroup E ℂ) (p : ℕ) :
    ‖MatrixMap.stinespring (checkedReadDefect π U) *
      diagonal (fun i : (X × Database X Y) × E ↦
        if i.1.2.size ≤ p then (1 : ℂ) else 0)‖ ^ 2 ≤
      24 * (Database.instability π (p + 1)).toReal := by
  classical
  have hn : ‖readFullDefect π U (p + 1)‖ ^ 2 ≤
      24 * (Database.instability π (p + 1)).toReal := by
    obtain ⟨S, hS, hd⟩ := exists_pinch_eq_truncatedCheckedRead_sub_sq_le π (p + 1)
    have h := l2_opNorm_commutator_labelControlled_one_kronecker_le
      (A := truncatedCheckedRead (p + 1)) hS hU
    rw [readFullDefect, norm_sub_rev]
    calc _ ≤ (2 * ‖truncatedCheckedRead (p + 1) - S‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = 4 * ‖truncatedCheckedRead (p + 1) - S‖ ^ 2 := by ring
      _ ≤ 4 * (6 * (Database.instability π (p + 1)).toReal) := by gcongr
      _ = _ := by ring
  have hi : Function.Injective (readResponseIndex (X := X) (Y := Y) (E := E) none) := by
    intro i j h
    have heq : (i, (none : Option Y)) = (j, none) := readResponseIndex_injective h
    exact congrArg Prod.fst heq
  have hs : ‖MatrixMap.stinespring (checkedReadDefect π U) * readInputCutoff p‖ ≤
      ‖readFullDefect π U (p + 1)‖ := by
    rw [readDefectStack_eq]
    exact (l2_opNorm_mul _ _).trans <| calc
      _ ≤ ‖readFullDefect π U (p + 1)‖ * 1 := mul_le_mul
        (read_submatrix_norm_le _ _ _ readResponseIndex_injective hi)
        (readInputCutoff_norm_le p) (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _
  exact (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans hn

omit [DecidableEq ι] in
/-- The sum of the checked-instrument defects is bounded without a factor for the outcomes.
The input may be a subnormalized mixed state with arbitrary address correlations, including
an address selected adaptively before the read. One final read uses population cutoff `p+1`. -/
theorem sum_trace_checkedReadDefect_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    {E : Type*} [Fintype E] [DecidableEq E] (π : Database X Y → ι)
    (U : ι → Matrix E E ℂ) (hU : ∀ k, U k ∈ unitaryGroup E ℂ) (p : ℕ)
    (σ : Matrix ((X × Database X Y) × E) ((X × Database X Y) × E) ℂ)
    (hσ : σ.PosSemidef)
    (hpop : QuerySupportedOn (fun i : (X × Database X Y) × E ↦ i.1.2.size) (Set.Iic p) σ) :
    ∑ a, (checkedReadDefect π U a * σ * (checkedReadDefect π U a)ᴴ).trace.re ≤
      24 * (Database.instability π (p + 1)).toReal * σ.trace.re := by
  let P : Matrix ((X × Database X Y) × E) ((X × Database X Y) × E) ℂ := readInputCutoff p
  have hc : P * σ * Pᴴ = σ := by
    ext i j
    simp only [P, readInputCutoff, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
    by_cases hz : σ i j = 0
    · simp [hz]
    · obtain ⟨hi, hj⟩ := hpop i j hz
      simp only [Set.mem_Iic] at hi hj
      simp [hi, hj]
  let S : Matrix (((X × Database X Y) × E) × Option Y) ((X × Database X Y) × E) ℂ :=
    MatrixMap.stinespring (checkedReadDefect π U)
  have he : (S * P) * σ * (S * P)ᴴ = S * σ * Sᴴ := by
    calc _ = S * (P * σ * Pᴴ) * Sᴴ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hc]
  rw [← Complex.re_sum, ← read_stinespring_trace]
  change (S * σ * Sᴴ).trace.re ≤ _
  rw [← he]
  exact (read_trace_rectangular_le _ _ hσ).trans
    (mul_le_mul_of_nonneg_right (l2_opNorm_checkedReadDefectStack_sq_le π U hU p)
      hσ.trace_re_nonneg)


/-- A read with a retained, possibly adaptive address increases database population
by at most one. -/
theorem QuerySupportedOn.conj_selectedCheckedReadProjector
    {E : Type*} [Fintype E] [DecidableEq E] {p : ℕ}
    {σ : Matrix ((X × Database X Y) × E) ((X × Database X Y) × E) ℂ}
    (h : QuerySupportedOn (fun i : (X × Database X Y) × E ↦ i.1.2.size) (Set.Iic p) σ)
    (a : Option Y) :
    QuerySupportedOn (fun i : (X × Database X Y) × E ↦ i.1.2.size) (Set.Iic (p + 1))
      (MatrixMap.conj (selectedCheckedReadProjector a ⊗ₖ (1 : Matrix E E ℂ)) σ) := by
  refine h.conj ?_
  intro i j hij hj
  have hn : selectedCheckedReadProjector a i.1 j.1 ≠ 0 := left_ne_zero_of_mul hij
  exact (selectedCheckedReadProjector_growth a i.1 j.1 hn).trans (Nat.add_le_add_right hj 1)

end cellBlocks

end Quantum
