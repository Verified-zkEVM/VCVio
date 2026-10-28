/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Size
public import Mathlib.Data.ZMod.Basic

/-!
# A unitary dilation of a checked classical read

The response contains an answer and a validity bit. The database remains a partial table
with values in `Y`. Conjugating table translations by compression gives a proof-only dilation;
this construction does not change the adversary's oracle.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- A table translation, conjugated by compression of the original database. -/
noncomputable def compressedReadTranslation (f : Option Y → Y × ZMod 2) :
    Matrix ((X × (Y × ZMod 2)) × Database X Y)
      ((X × (Y × ZMod 2)) × Database X Y) ℂ :=
  (1 ⊗ₖ compressAll X Y) * tableOracle (fun D x ↦ f (D x)) * (1 ⊗ₖ compressAll X Y)

/-- The translation recording an answer and whether the cell is populated. -/
@[expose]
def checkedReadValue : Option Y → Y × ZMod 2
  | none => (0, 0)
  | some y => (y, 1)

/-- The proof-only checked-read dilation on the original database. -/
noncomputable def checkedReadUnitary :
    Matrix ((X × (Y × ZMod 2)) × Database X Y)
      ((X × (Y × ZMod 2)) × Database X Y) ℂ :=
  compressedReadTranslation (X := X) (Y := Y) checkedReadValue

/-- The ordinary response translation with a spectator bit. -/
noncomputable def ordinaryReadWithBit :
    Matrix ((X × (Y × ZMod 2)) × Database X Y)
      ((X × (Y × ZMod 2)) × Database X Y) ℂ :=
  compressedReadTranslation (X := X) (Y := Y) (fun a ↦ (a.getD 0, 0))

/-- The validity translation, leaving the answer register unchanged. -/
noncomputable def checkedReadValidity :
    Matrix ((X × (Y × ZMod 2)) × Database X Y)
      ((X × (Y × ZMod 2)) × Database X Y) ℂ :=
  compressedReadTranslation (X := X) (Y := Y) (fun a ↦ (0, (checkedReadValue a).2))

/-- Compression conjugates the table translation on the original database. -/
theorem compressedReadTranslation_eq (f : Option Y → Y × ZMod 2) :
    compressedReadTranslation (X := X) f =
      (1 ⊗ₖ compressAll X Y) * tableOracle (fun D x ↦ f (D x)) *
        (1 ⊗ₖ compressAll X Y) := by
  unfold compressedReadTranslation
  rfl

/-- The dilation uses the answer-and-validity table translation. -/
theorem checkedReadUnitary_eq : checkedReadUnitary (X := X) (Y := Y) =
    compressedReadTranslation checkedReadValue := by
  unfold checkedReadUnitary
  rfl

/-- Validity translates only the bit coordinate. -/
theorem checkedReadValidity_eq : checkedReadValidity (X := X) (Y := Y) =
    compressedReadTranslation (fun a ↦ (0, (checkedReadValue a).2)) := by
  unfold checkedReadValidity
  rfl

/-- Compressed translations compose by adding their table values. -/
theorem compressedReadTranslation_mul (f g : Option Y → Y × ZMod 2) :
    compressedReadTranslation (X := X) f * compressedReadTranslation g =
      compressedReadTranslation (fun a ↦ f a + g a) := by
  have hc : ((1 : Matrix (X × (Y × ZMod 2)) (X × (Y × ZMod 2)) ℂ) ⊗ₖ
      compressAll X Y) * (1 ⊗ₖ compressAll X Y) = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressAll_mul_self, one_kronecker_one]
  have ht : tableOracle (fun (D : Database X Y) x ↦ f (D x)) *
      tableOracle (fun (D : Database X Y) x ↦ g (D x)) =
      tableOracle (fun (D : Database X Y) x ↦ f (D x) + g (D x)) := by
    rw [tableOracle, tableOracle, tableOracle, ← basisMatrix_comp]
    congr 1
    funext p
    rcases p with ⟨⟨x, y⟩, D⟩
    simp only [Function.comp_apply, tableOracleEquiv_apply, oracleEquiv_apply]
    congr 2
    abel
  simp only [compressedReadTranslation, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 ⊗ₖ compressAll X Y) (1 ⊗ₖ compressAll X Y), hc, Matrix.one_mul,
    ← Matrix.mul_assoc (tableOracle _), ht]

/-- The ordinary translation followed by validity is the complete read. -/
theorem ordinaryReadWithBit_mul_validity :
    ordinaryReadWithBit (X := X) (Y := Y) * checkedReadValidity = checkedReadUnitary := by
  rw [ordinaryReadWithBit, checkedReadValidity, compressedReadTranslation_mul, checkedReadUnitary]
  congr 1
  funext a
  cases a <;> simp [checkedReadValue]

/-- The validity translation commutes with the ordinary translation. -/
theorem validity_mul_ordinaryReadWithBit :
    checkedReadValidity (X := X) (Y := Y) * ordinaryReadWithBit = checkedReadUnitary := by
  rw [ordinaryReadWithBit, checkedReadValidity, compressedReadTranslation_mul, checkedReadUnitary]
  congr 1
  funext a
  cases a <;> simp [checkedReadValue]

/-- Every compressed table translation is unitary. -/
theorem compressedReadTranslation_mem_unitaryGroup (f : Option Y → Y × ZMod 2) :
    compressedReadTranslation (X := X) f ∈ unitaryGroup _ ℂ := by
  have hc : (1 : Matrix (X × (Y × ZMod 2)) (X × (Y × ZMod 2)) ℂ) ⊗ₖ
      compressAll X Y ∈ unitaryGroup _ ℂ :=
    mem_unitaryGroup_iff'.mpr (by
      rw [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one,
        conjTranspose_compressAll,
        ← mul_kronecker_mul, Matrix.one_mul, compressAll_mul_self, one_kronecker_one])
  exact mul_mem (mul_mem hc (mem_unitaryGroup_iff'.mpr
    (conjTranspose_tableOracle_mul_self _))) hc

/-- The checked-read dilation is unitary. -/
theorem checkedReadUnitary_mem_unitaryGroup :
    checkedReadUnitary (X := X) (Y := Y) ∈ unitaryGroup _ ℂ :=
  compressedReadTranslation_mem_unitaryGroup _

/-- The outcome projector of the checked read at an address. -/
noncomputable def checkedReadProjector (x : X) (a : Option Y) :
    Matrix (Database X Y) (Database X Y) ℂ :=
  compressAll X Y * diagonal (fun D ↦ if D x = a then 1 else 0) * compressAll X Y

/-- A fresh response extracts the corresponding table-value projector. -/
theorem compressedReadTranslation_fresh (f : Option Y → Y × ZMod 2)
    (x : X) (z : Y × ZMod 2) (D D' : Database X Y) :
    compressedReadTranslation f ((x, z), D) ((x, 0), D') =
      (compressAll X Y * diagonal (fun (E : Database X Y) ↦ if f (E x) = z then 1 else 0) *
        compressAll X Y : Matrix (Database X Y) (Database X Y) ℂ) D D' := by
  rw [compressedReadTranslation, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single (x, 0)]
  · conv_rhs => rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [tableOracle, mul_basisMatrix_apply, tableOracleEquiv_apply, mul_diagonal]
    simp [kroneckerMap_apply, Matrix.one_apply, oracleEquiv_apply, eq_comm]
  · intro m _ hm
    refine Finset.sum_eq_zero fun E _ ↦ ?_
    simp [kroneckerMap_apply, hm]
  · simp

/-- A fresh response cannot change the query address. -/
theorem checkedReadUnitary_fresh_of_ne (x x' : X) (z : Y × ZMod 2)
    (D D' : Database X Y) (h : x ≠ x') :
    checkedReadUnitary (X := X) (Y := Y) ((x, z), D) ((x', 0), D') = 0 := by
  rw [checkedReadUnitary_eq, compressedReadTranslation_eq, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single (x', 0)]
  · apply Finset.sum_eq_zero
    intro E _
    rw [tableOracle, mul_basisMatrix_apply, tableOracleEquiv_apply]
    simp [kroneckerMap_apply, oracleEquiv_apply, h]
  · intro m _ hm
    apply Finset.sum_eq_zero
    intro E _
    simp [kroneckerMap_apply, hm]
  · simp

omit [Fintype Y] [DecidableEq Y] in
/-- Encodings of distinct checked outcomes are distinct response basis vectors. -/
theorem checkedReadValue_injective : Function.Injective (checkedReadValue (Y := Y)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [checkedReadValue]

/-- A filled fresh-response branch is precisely the prescribed-answer projector. -/
theorem checkedReadUnitary_fresh_some (x : X) (y : Y) (D D' : Database X Y) :
    checkedReadUnitary ((x, (y, 1)), D) ((x, (0, 0)), D') =
      checkedReadProjector x (some y) D D' := by
  change compressedReadTranslation (X := X) checkedReadValue _ ((x, 0), D') = _
  rw [compressedReadTranslation_fresh, checkedReadProjector]
  have h : ∀ E : Database X Y, checkedReadValue (E x) = (y, 1) ↔ E x = some y := by
    intro E
    cases hE : E x <;> simp [checkedReadValue]
  simp only [h]

/-- The fresh zero response with validity zero is precisely the empty-sector projector. -/
theorem checkedReadUnitary_fresh_none (x : X) (D D' : Database X Y) :
    checkedReadUnitary ((x, (0, 0)), D) ((x, (0, 0)), D') =
      checkedReadProjector x none D D' := by
  change compressedReadTranslation (X := X) checkedReadValue _ ((x, 0), D') = _
  rw [compressedReadTranslation_fresh, checkedReadProjector]
  have h : ∀ E : Database X Y, checkedReadValue (E x) = (0, 0) ↔ E x = none := by
    intro E
    cases hE : E x <;> simp [checkedReadValue]
  simp only [h]

omit [AddCommGroup Y] in
/-- A checked projector factors into one-cell sums. -/
theorem checkedReadProjector_apply (x : X) (a : Option Y) (D D' : Database X Y) :
    checkedReadProjector x a D D' =
      ∏ i, ∑ z, (if i = x then (if z = a then 1 else 0) else 1) *
        (cellCompress Y (D i) z * cellCompress Y z (D' i)) := by
  rw [checkedReadProjector, Matrix.mul_apply]
  simp only [mul_diagonal]
  simpa only [compressAll, mul_left_comm, mul_assoc] using
    sum_mul_piKron_mul_piKron (fun _ : X ↦ cellCompress Y)
      (fun _ : X ↦ cellCompress Y) x (fun z ↦ if z = a then 1 else 0) D D'

/-- A checked branch changes only the queried cell. -/
theorem eq_update_of_checkedReadProjector_ne_zero (x : X) (a : Option Y)
    {D D' : Database X Y} (h : checkedReadProjector x a D D' ≠ 0) :
    D = Function.update D' x (D x) := by
  apply Function.eq_update_iff.mpr
  refine ⟨rfl, fun j hj ↦ ?_⟩
  rw [checkedReadProjector_apply] at h
  have hj' := (Finset.prod_ne_zero_iff.mp h) j (Finset.mem_univ j)
  simp only [hj, ite_false, one_mul, ← Matrix.mul_apply, cellCompress_mul_self,
    Matrix.one_apply] at hj'
  split_ifs at hj' with hh
  · exact hh
  · exact False.elim (hj' rfl)

/-- Each checked outcome increases database population by at most one. -/
theorem size_le_of_checkedReadProjector_ne_zero (x : X) (a : Option Y)
    {D D' : Database X Y} (h : checkedReadProjector x a D D' ≠ 0) :
    D.size ≤ D'.size + 1 :=
  (congrArg Database.size (eq_update_of_checkedReadProjector_ne_zero x a h)).trans_le
    (Database.size_update_le _ _ _)

/-- The ordinary zero branch includes both the filled-zero and empty sectors. -/
theorem compressedOracle_fresh_zero (x : X) (D D' : Database X Y) :
    compressedOracle X Y ((x, 0), D) ((x, 0), D') =
      (checkedReadProjector x (some (0 : Y)) + checkedReadProjector x none :
        Matrix (Database X Y) (Database X Y) ℂ) D D' := by
  have he : compressedOracle X Y ((x, 0), D) ((x, 0), D') =
      (compressAll X Y * diagonal (fun E : Database X Y ↦
        if (E x).getD 0 = 0 then 1 else 0) * compressAll X Y :
          Matrix (Database X Y) (Database X Y) ℂ) D D' := by
    rw [compressedOracle, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single (x, 0)]
    · conv_rhs => rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun E _ ↦ ?_
      rw [standardOracle, tableOracle, mul_basisMatrix_apply, tableOracleEquiv_apply,
        mul_diagonal]
      simp [kroneckerMap_apply, Matrix.one_apply, oracleEquiv_apply, eq_comm]
    · intro m _ hm
      refine Finset.sum_eq_zero fun E _ ↦ ?_
      simp [kroneckerMap_apply, hm]
    · simp
  rw [he]
  have hd : (diagonal (fun E : Database X Y ↦ if (E x).getD 0 = 0 then 1 else 0) :
      Matrix (Database X Y) (Database X Y) ℂ) =
      diagonal (fun E ↦ if E x = some 0 then 1 else 0) +
        diagonal (fun E ↦ if E x = none then 1 else 0) := by
    rw [diagonal_add]
    congr 1
    funext E
    cases E x <;> simp
  rw [hd, Matrix.mul_add, Matrix.add_mul]
  rfl

/-- Every read outcome preserves the population bound with one additional cell,
including when the database is entangled with an arbitrary external register. -/
theorem DatabaseSupportedOn.conj_checkedReadProjector
    {M : Type*} [Fintype M] [DecidableEq M] {t : ℕ}
    {ρ : Matrix (M × Database X Y) (M × Database X Y) ℂ}
    (h : DatabaseSupportedOn t ρ) (x : X) (a : Option Y) :
    DatabaseSupportedOn (t + 1)
      (MatrixMap.conj ((1 : Matrix M M ℂ) ⊗ₖ checkedReadProjector x a) ρ) := by
  refine QuerySupportedOn.conj h ?_
  intro i j hij hj
  have hn : checkedReadProjector x a i.2 j.2 ≠ 0 :=
    right_ne_zero_of_mul hij
  exact (size_le_of_checkedReadProjector_ne_zero x a hn).trans (Nat.add_le_add_right hj 1)

end Quantum
