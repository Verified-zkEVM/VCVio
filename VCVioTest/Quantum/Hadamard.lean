/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardWitness
public import VCVio.Quantum.VC.HadamardSimulation
public import VCVio.Quantum.VC.HadamardCommutation
public import VCVio.Quantum.VC.HadamardResidual
public import VCVio.Quantum.VC.HadamardExtraction
public import VCVio.Quantum.VC.HadamardComBound
public import VCVio.Quantum.VC.HadamardBinary

/-!
# Small-instance tests for the Hadamard extension

The tests instantiate the witness, simulation, exact port commutation, residual estimate and
accepting-map identities. Repeated and conflicting prescriptions retain their multiplicity.
-/

public section

open Quantum Matrix Convexity OracleSpec
open scoped Matrix.Norms.L2Operator

namespace VCVioTest.QuantumHadamard

/-- A one-bit response satisfies the involutive-translation hypothesis. -/
example (y : Fin 1 → ZMod 2) : y + y = 0 := bitstring_add_self 1 y

/-- A two-port Hadamard witness is unitary. -/
example (i : Fin 2) : (hadamardVCOracle 2 Bool 1).U i ∈ unitaryGroup _ ℂ :=
  (hadamardVCOracle 2 Bool 1).unitary i

/-- The ports commute, including queries to the same cell. -/
example : OraclesCommute (hadamardVCOracle 2 Bool 1) :=
  oraclesCommute_extendedVCOracle _ (bitstringHadamard_mem_unitaryGroup 1)

/-- Perfect simulation uses exactly the uniform weights over pairs of functions. -/
example : Simulates (StdSimplex.barycenter : StdSimplex ℝ (Fin 2 → Bool → Fin 1 → ZMod 2))
    (fun H ↦ (romVCOracle 2 Bool (Fin 1 → ZMod 2) H).coherent.toRuntime)
    (hadamardVCOracle 2 Bool 1) 0 :=
  simulates_extendedVCOracle _ (bitstringHadamard_mem_unitaryGroup 1)

/-- The actual one-query accepting map has the additional invalid-sector amplitude. -/
example (y : ZMod 2) :
    (compressedCell binaryHadamard).submatrix (fun d ↦ (y, d)) (fun d ↦ (0, d)) =
      cellFilledProjector y + cellAmp (ZMod 2) • cellInvalidProjector := by
  rw [submatrix_compressedCell, binaryHadamard_zero]

/-- Repeated queries on an empty cell give a power of the amplitude. -/
example (m : ℕ) :
    acceptWeight (fun _ : ZMod 2 ↦ cellAmp (ZMod 2))
      (List.replicate m (false, 0)) (fun _ ↦ none) = cellAmp (ZMod 2) ^ m := by
  rw [acceptWeight_replicate]
  rfl

/-- Conflicting queries can both accept through the empty sector, with amplitude `1 / 2`. -/
example : acceptValue (fun _ : ZMod 2 ↦ cellAmp (ZMod 2)) 0 none *
    acceptValue (fun _ : ZMod 2 ↦ cellAmp (ZMod 2)) 1 none = (2 : ℂ)⁻¹ := by
  change cellAmp (ZMod 2) * cellAmp (ZMod 2) = _
  simpa using cellAmp_mul_self (ZMod 2)

/-- The cell residual estimate instantiates on a bitstring Hadamard. -/
example (y : Fin 1 → ZMod 2) :
    ‖(compressedCell (bitstringHadamard 1) - decompressedCell (bitstringHadamard 1)).submatrix
      (fun r ↦ (r, some y)) id‖ ^ 2 ≤ 6 / Fintype.card (Fin 1 → ZMod 2) :=
  norm_compressedCell_residual_row_sq_le (bitstring_add_self 1)
    (bitstringHadamard_mem_unitaryGroup 1) (bitstringHadamard_mul_self 1) y

-- P3's exact error theorem is available to consumers of the new witness.
#check extractionCorrect_extendedVCOracle

/-- Cardinality four alone does not imply the exponent-two translation hypothesis. -/
example : ¬ ∀ y : ZMod 4, y + y = 0 := by
  intro h
  have he := h 1
  norm_num at he
  exact (by decide : (2 : ZMod 4) ≠ 0) he

-- P2 uses the existing error and security predicate.
#check comBound_extendedVCOracle

/-- Uniform answer semantics for the concrete bitstring oracle. -/
noncomputable local instance : UniformAnswerMeasure (Unit →ₒ (Fin 1 → ZMod 2)) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- The binary event estimate elaborates for a small concrete Hadamard database. -/
example (π : Database Unit (Fin 1 → ZMod 2) → Bool) (t : ℕ) :
    ‖labelProjector (fun p : (Unit × (Fin 1 → ZMod 2)) ×
          Database Unit (Fin 1 → ZMod 2) ↦ π p.2) true *
          truncatedExtendedOracle (bitstringHadamard 1) t -
        truncatedExtendedOracle (bitstringHadamard 1) t *
          labelProjector (fun p : (Unit × (Fin 1 → ZMod 2)) ×
            Database Unit (Fin 1 → ZMod 2) ↦ π p.2) true‖ ^ 2 ≤
      6 * (Database.instability π t).toReal := by
  exact norm_binary_commutator_truncatedExtendedOracle_sq_le (bitstring_add_self 1)
    (bitstringHadamard_mem_unitaryGroup 1) (bitstringHadamard_mul_self 1) π t true

end VCVioTest.QuantumHadamard
