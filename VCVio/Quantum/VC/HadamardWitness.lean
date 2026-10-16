/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Hadamard
public import Mathlib.Data.ZMod.Basic

/-!
# A concrete Hadamard empty-sector response

The general extension accepts any response unitary. Here the response is the ordinary tensor
product Hadamard on bitstrings. Its zero column is the uniform vector, and it is an involution.
The exponent-two identity is proved explicitly for this answer group.
-/

public section

open Matrix

namespace Quantum

/-- The one-bit Hadamard, in the computational basis indexed by `ZMod 2`. -/
@[expose]
noncomputable def binaryHadamard : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun r s ↦ if r = 1 ∧ s = 1 then -cellAmp (ZMod 2) else cellAmp (ZMod 2)

/-- The one-bit Hadamard has a uniform zero column. -/
theorem binaryHadamard_zero (r : ZMod 2) : binaryHadamard r 0 = cellAmp (ZMod 2) := by
  simp [binaryHadamard]

/-- The one-bit Hadamard is Hermitian. -/
theorem conjTranspose_binaryHadamard : binaryHadamardᴴ = binaryHadamard := by
  ext r s
  simp only [conjTranspose_apply, binaryHadamard, and_comm]
  split_ifs <;> simp only [star_neg, star_cellAmp]

/-- Applying the one-bit Hadamard twice gives the identity. -/
theorem binaryHadamard_mul_self : binaryHadamard * binaryHadamard = 1 := by
  have ha := cellAmp_mul_self (ZMod 2)
  norm_num at ha
  ext r s
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ t : Fin 2, binaryHadamard r t * binaryHadamard t s) = _
  rw [Fin.sum_univ_two]
  fin_cases r <;> fin_cases s
  · change cellAmp (ZMod 2) * cellAmp (ZMod 2) +
      cellAmp (ZMod 2) * cellAmp (ZMod 2) = 1
    linear_combination 2 * ha
  · change cellAmp (ZMod 2) * cellAmp (ZMod 2) +
      cellAmp (ZMod 2) * -cellAmp (ZMod 2) = 0
    ring
  · change cellAmp (ZMod 2) * cellAmp (ZMod 2) +
      -cellAmp (ZMod 2) * cellAmp (ZMod 2) = 0
    ring
  · change cellAmp (ZMod 2) * cellAmp (ZMod 2) +
      -cellAmp (ZMod 2) * -cellAmp (ZMod 2) = 1
    linear_combination 2 * ha

/-- The one-bit Hadamard is unitary. -/
theorem binaryHadamard_mem_unitaryGroup : binaryHadamard ∈ unitaryGroup (ZMod 2) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_binaryHadamard,
    binaryHadamard_mul_self]

/-- The Hadamard response on bitstrings is the tensor product of the one-bit responses. -/
@[expose]
noncomputable def bitstringHadamard (σ : ℕ) :
    Matrix (Fin σ → ZMod 2) (Fin σ → ZMod 2) ℂ :=
  piKron fun _ : Fin σ ↦ binaryHadamard

/-- The bitstring Hadamard is unitary, including the zero-bit case. -/
theorem bitstringHadamard_mem_unitaryGroup (σ : ℕ) :
    bitstringHadamard σ ∈ unitaryGroup (Fin σ → ZMod 2) ℂ :=
  piKron_mem_unitaryGroup fun _ ↦ binaryHadamard_mem_unitaryGroup

/-- The bitstring Hadamard is an involution. -/
theorem bitstringHadamard_mul_self (σ : ℕ) :
    bitstringHadamard σ * bitstringHadamard σ = 1 := by
  simp only [bitstringHadamard, piKron_mul, binaryHadamard_mul_self, piKron_one]

/-- The zero column of the bitstring Hadamard is exactly the positive uniform vector. -/
theorem bitstringHadamard_zero (σ : ℕ) (r : Fin σ → ZMod 2) :
    bitstringHadamard σ r 0 = cellAmp (Fin σ → ZMod 2) := by
  simp only [bitstringHadamard, piKron_apply, Pi.zero_apply, binaryHadamard_zero,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs : Real.sqrt ((2 : ℝ) ^ σ) = Real.sqrt 2 ^ σ := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  simp [cellAmp, Fintype.card_pi, inv_pow, hs]

/-- Every bitstring is its own additive inverse, the hypothesis needed for the residual bound. -/
theorem bitstring_add_self (σ : ℕ) (r : Fin σ → ZMod 2) : r + r = 0 := by
  ext i
  change r i + r i = (0 : ZMod 2)
  generalize r i = b
  fin_cases b <;> decide

/-- The concrete Hadamard emulation witness, with one empty database for each oracle index. -/
@[expose]
noncomputable def hadamardVCOracle (k : ℕ) (X : Type) [Fintype X] [DecidableEq X] (σ : ℕ) :
    VCOracle k X (Fin σ → ZMod 2) :=
  extendedVCOracle k X (Fin σ → ZMod 2) (bitstringHadamard σ)
    (bitstringHadamard_mem_unitaryGroup σ)

end Quantum
