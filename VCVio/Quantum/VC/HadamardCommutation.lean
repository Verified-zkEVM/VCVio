/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Hadamard

/-!
# Commutation of extended oracle ports

The decompressed ports preserve their database labels and act on separate query registers.
They therefore commute, including when they address the same cell. Conjugation by the common
compression preserves this equality. No exponent-two or flat-column hypothesis is required.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

section blocks

variable {M N S : Type*} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype S] [DecidableEq S]

/-- Database-controlled operations on separate query registers commute even when they use
the same database label. No unitarity assumption is necessary. -/
theorem blockDiagonal_slotSnd_mul_slotFst_comm (A : S → Matrix N N ℂ)
    (B : S → Matrix M M ℂ) :
    onFactor (slotSnd M N S) (blockDiagonal A) *
        onFactor (slotFst M N S) (blockDiagonal B) =
      onFactor (slotFst M N S) (blockDiagonal B) *
        onFactor (slotSnd M N S) (blockDiagonal A) := by
  ext ⟨⟨m, n⟩, s⟩ ⟨⟨m', n'⟩, s'⟩
  by_cases hs : s = s'
  · subst s'
    simp [Matrix.mul_apply, Fintype.sum_prod_type, onFactor_apply, slotSnd, slotFst,
      blockDiagonal_apply, mul_comm]
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, onFactor_apply, slotSnd, slotFst,
      blockDiagonal_apply, hs, ite_mul, mul_ite]

end blocks

section ports

variable {X Y S : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq S] [AddCommGroup Y]

/-- The extended table operation is block diagonal in the database, with an input-controlled
response operation on each block. -/
theorem extendedTableOracle_eq_blockDiagonal (W : Matrix Y Y ℂ) (read : S → X → Option Y) :
    extendedTableOracle W read = blockDiagonal (fun d ↦
      (blockDiagonal fun x ↦ emptyExtensionBlock W (read d x)).submatrix
        (Equiv.prodComm X Y) (Equiv.prodComm X Y)) := by
  ext ⟨⟨x, r⟩, d⟩ ⟨⟨z, s⟩, e⟩
  by_cases hx : x = z <;> by_cases hd : d = e <;>
    simp [extendedTableOracle_apply, blockDiagonal_apply, hx, hd]

variable [Fintype X] [Fintype Y] [Fintype S]

/-- Decompressed extended table operations on separate query registers commute. -/
theorem extendedTableOracle_slotSnd_mul_slotFst_comm (W V : Matrix Y Y ℂ)
    (read read' : S → X → Option Y) :
    onFactor (slotSnd (X × Y) (X × Y) S) (extendedTableOracle W read) *
        onFactor (slotFst (X × Y) (X × Y) S) (extendedTableOracle V read') =
      onFactor (slotFst (X × Y) (X × Y) S) (extendedTableOracle V read') *
        onFactor (slotSnd (X × Y) (X × Y) S) (extendedTableOracle W read) := by
  rw [extendedTableOracle_eq_blockDiagonal, extendedTableOracle_eq_blockDiagonal]
  exact blockDiagonal_slotSnd_mul_slotFst_comm _ _

end ports

section vc

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- Extended VC ports commute, even with different empty-sector matrices on the two ports. -/
theorem extendedVCPort_commute (W V : Matrix Y Y ℂ) (i j : Fin k) :
    onFactor (slotSnd (X × Y) (X × Y) (Fin k → Database X Y))
        (extendedVCPort k X Y W i) *
      onFactor (slotFst (X × Y) (X × Y) (Fin k → Database X Y))
        (extendedVCPort k X Y V j) =
    onFactor (slotFst (X × Y) (X × Y) (Fin k → Database X Y))
        (extendedVCPort k X Y V j) *
      onFactor (slotSnd (X × Y) (X × Y) (Fin k → Database X Y))
        (extendedVCPort k X Y W i) := by
  simp only [extendedVCPort, onFactor_mul, onFactor_slotFst_one_kronecker,
    onFactor_slotSnd_one_kronecker]
  refine conj_mul_conj_comm ?_ (extendedTableOracle_slotSnd_mul_slotFst_comm W V _ _)
  rw [one_kronecker_mul_one_kronecker, compressDatabases_mul_self, one_kronecker_one]

/-- The exact oracle-oracle part of P2 for the extended witness. -/
theorem oraclesCommute_extendedVCOracle (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ) :
    OraclesCommute (extendedVCOracle k X Y W hW) :=
  fun i j ↦ extendedVCPort_commute W W i j

end vc

end Quantum
