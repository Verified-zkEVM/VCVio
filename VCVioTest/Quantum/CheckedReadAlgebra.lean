/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.CheckedReadBound

/-!
# Checked-read algebra at small answer alphabets

The singleton alphabet still distinguishes an empty decompressed cell from the filled zero
answer. The negative trivial character is a nonidentity block even in this case.
-/

public section

open Quantum Matrix

namespace VCVioTest.CheckedReadAlgebra

/-- At one answer, the negative trivial block has residual squared norm four. -/
theorem singleton_negative_trivial :
    ∑ a, ‖checkedReadPhaseCell (0 : AddChar (ZMod 1) ℂ) (-1) (some 0) a -
      if a = some 0 then -1 else 0‖ ^ 2 = 4 := by
  simpa using sum_norm_checkedReadPhaseCell_zero_neg_one_sub_sq (0 : ZMod 1)

/-- The empty decompressed sector is fixed by the negative trivial block. -/
theorem negative_trivial_filled_entry :
    checkedReadPhaseCell (0 : AddChar (ZMod 1) ℂ) (-1) (some 0) (some 0) = 1 := by
  rw [checkedReadPhaseCell_zero_neg_one]
  norm_num [checkedReadEmptyCell_apply, cellAmp]

/-- The same block negates the compressed empty basis vector. -/
theorem negative_trivial_empty_entry :
    checkedReadPhaseCell (0 : AddChar (ZMod 1) ℂ) (-1) none none = -1 := by
  rw [checkedReadPhaseCell_zero_neg_one]
  simp [checkedReadEmptyCell_apply]

/-- With one answer, the ordinary zero branch retains the entire private state. -/
theorem singleton_ordinary_zero :
    compressedOracle Unit (ZMod 1)
      (((), 0), Database.ofFun (fun _ ↦ 0)) (((), 0), Database.ofFun (fun _ ↦ 0)) = 1 := by
  rw [compressedOracle_fresh_zero]
  simp [Matrix.add_apply, checkedReadProjector_apply, cellAmp]

/-- The checked filled-zero branch rejects the state retained by the ordinary zero branch. -/
theorem singleton_checked_zero :
    checkedReadUnitary (X := Unit) (Y := ZMod 1)
      (((), (0, 1)), Database.ofFun (fun _ ↦ 0))
      (((), (0, 0)), Database.ofFun (fun _ ↦ 0)) = 0 := by
  rw [checkedReadUnitary_fresh_some]
  simp [checkedReadProjector_apply]


/-- The actual dilation has the signed-cell Fourier form even for a singleton answer type. -/
example (χ : AddChar (ZMod 1 × ZMod 2) ℂ) (D D' : Database Unit (ZMod 1)) :
    (checkedReadFourier * checkedReadUnitary *
      (checkedReadFourier (X := Unit) (Y := ZMod 1))ᴴ :
      Matrix ((Unit × AddChar (ZMod 1 × ZMod 2) ℂ) × Database Unit (ZMod 1))
        ((Unit × AddChar (ZMod 1 × ZMod 2) ℂ) × Database Unit (ZMod 1)) ℂ)
      (((), χ), D') (((), χ), D) =
      checkedReadPhaseCell (checkedReadAnswerChar χ) (χ (0, 1)) (D' ()) (D ()) := by
  rw [checkedReadFourier_conj_apply]
  simp

#check @DatabaseSupportedOn.conj_checkedReadProjector
#check @QuerySupportedOn.conj_selectedCheckedReadProjector
#check @truncatedCheckedRead_eq
#check @truncatedValidity_eq


namespace ResidualState

/-- The one-address database, indexed by its sole cell content. -/
private def db (a : Option (ZMod 1)) : Database Unit (ZMod 1) := fun _ ↦ a

private noncomputable def Q : Matrix (Option (ZMod 1)) (Option (ZMod 1)) ℂ :=
  fun a b ↦ checkedReadProjector () (some 0) (db a) (db b)

private noncomputable def R : Matrix (Option (ZMod 1)) (Option (ZMod 1)) ℂ :=
  fun a b ↦ checkedReadProjector () none (db a) (db b)

private theorem Q_eq : Q = diagonal (fun a ↦ if a = none then 1 else 0) := by
  ext a b
  have hz (y : ZMod 1) : y = 0 := Subsingleton.elim _ _
  cases a <;> cases b <;>
    simp [Q, db, checkedReadProjector_apply, cellAmp, diagonal, hz]

private theorem R_eq : R = diagonal (fun a ↦ if a = some 0 then 1 else 0) := by
  ext a b
  have hz (y : ZMod 1) : y = 0 := Subsingleton.elim _ _
  cases a <;> cases b <;>
    simp [R, db, checkedReadProjector_apply, cellAmp, diagonal, hz]

/-- The two basis vectors lie in the filled-zero and empty-sector projector ranges. -/
private theorem sector_vectors :
    Q *ᵥ Pi.single none 1 = Pi.single none 1 ∧
      R *ᵥ Pi.single (some 0) 1 = Pi.single (some 0) 1 := by
  rw [Q_eq, R_eq]
  constructor <;> ext a <;> cases a <;> simp [mulVec_diagonal, Pi.single_apply]

/-- Equal amplitudes on the two orthogonal sectors form a coherent normalized vector. -/
private noncomputable def ψ : Option (ZMod 1) → ℂ := fun _ ↦ cellAmp (Fin 2)

private theorem psi_superposition :
    ψ = cellAmp (Fin 2) • (Pi.single none 1 + Pi.single (some 0) 1) := by
  ext a
  have hz (y : ZMod 1) : y = 0 := Subsingleton.elim _ _
  cases a <;> simp [ψ, hz]

private noncomputable def ρ : Matrix (Option (ZMod 1)) (Option (ZMod 1)) ℂ :=
  vecMulVec ψ (star ψ)

private theorem rho_apply (a b : Option (ZMod 1)) : ρ a b = 1 / 2 := by
  simp only [ρ, vecMulVec, ψ, Pi.star_apply, star_cellAmp]
  norm_num [cellAmp_mul_self]

open scoped ComplexOrder in
private theorem rho_posSemidef : ρ.PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

private theorem rho_trace : ρ.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, rho_apply, Fintype.sum_option]
  norm_num

private noncomputable def ordinary : Matrix (Option (ZMod 1)) (Option (ZMod 1)) ℂ :=
  fun a b ↦ compressedOracle Unit (ZMod 1) (((), 0), db a) (((), 0), db b)

private theorem ordinary_eq : ordinary = Q + R := by
  ext a b
  exact compressedOracle_fresh_zero () (db a) (db b)

private noncomputable def ordinaryState := ordinary * ρ * ordinaryᴴ
private noncomputable def checkedState := Q * ρ * Qᴴ + R * ρ * Rᴴ

/-- The ordinary zero channel retains both coherences, whereas the merged fine read is diagonal. -/
private theorem residual_entries (a b : Option (ZMod 1)) :
    ordinaryState a b = 1 / 2 ∧ checkedState a b = if a = b then 1 / 2 else 0 := by
  have hz (y : ZMod 1) : y = 0 := Subsingleton.elim _ _
  have ho : ordinary = 1 := by
    rw [ordinary_eq, Q_eq, R_eq, diagonal_add]
    ext i j
    cases i <;> cases j <;> simp [diagonal, Matrix.one_apply, hz]
  simp only [ordinaryState, checkedState, ho, conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one, Q_eq, R_eq, diagonal_conjTranspose, Matrix.add_apply,
    mul_diagonal, diagonal_mul, rho_apply]
  cases a <;> cases b <;> norm_num [hz]

/-- Both merged zero outcomes have probability one on this state. -/
private theorem merged_zero_probabilities : ordinaryState.trace = 1 ∧ checkedState.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, (residual_entries _ _).1,
    (residual_entries _ _).2, ite_true, Fintype.sum_option]
  norm_num

/-- The cross-sector entry is retained only by the ordinary channel. -/
private theorem cross_terms_and_distinct :
    ordinaryState = checkedState + (Q * ρ * Rᴴ + R * ρ * Qᴴ) ∧
      ordinaryState none (some 0) = 1 / 2 ∧ checkedState none (some 0) = 0 ∧
      ordinaryState ≠ checkedState := by
  refine ⟨?_, (residual_entries _ _).1, ?_, ?_⟩
  · simp only [ordinaryState, ordinary_eq, checkedState, conjTranspose_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  · simpa using (residual_entries none (some 0)).2
  · intro h
    have he := congrArg (fun M : Matrix (Option (ZMod 1)) (Option (ZMod 1)) ℂ ↦
      M none (some 0)) h
    rw [(residual_entries _ _).1, (residual_entries _ _).2] at he
    norm_num at he

end ResidualState

end VCVioTest.CheckedReadAlgebra
