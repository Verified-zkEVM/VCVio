/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Pure.Tensor

/-!
# Pure-state regression tests

A Hadamard gate followed by the computational-basis measurement of one qubit, started from
`|0⟩`, reports each outcome with weight `1 / 2`: once through the Born rule on vectors, and once
through the density matrix `|+⟩⟨+|`, which the vector route reaches. The remaining checks
instantiate the commutator bounds on Pauli matrices, the hybrid bound at one query, and the norm
of a gate on one of two qubits.
-/

public section

open Quantum Matrix MeasureTheory WithLp
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace VCVioTest.QuantumPure

/-! ## Hadamard, then measure -/

/-- The projector onto the computational-basis state `i` of a qubit. -/
def proj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i 1

theorem sum_conjTranspose_proj_mul_proj : ∑ i, (proj i)ᴴ * proj i = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj, Matrix.sum_apply, Matrix.single_apply]

/-- Measurement of a qubit in the computational basis. -/
noncomputable def measureZ : SubInstrument (Fin 2) (Fin 2) (Fin 2) :=
  SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj

/-- The density matrix `|+⟩⟨+|`. -/
noncomputable def plus : SubState (Fin 2) where
  matrix := Matrix.of fun _ _ ↦ 1 / 2
  posSemidef := by
    have h : (Matrix.of fun _ _ ↦ 1 / 2 : Matrix (Fin 2) (Fin 2) ℂ) =
        (Matrix.of fun _ _ ↦ 1 / 2)ᴴ * Matrix.of fun _ _ ↦ 1 / 2 := by
      ext i j
      simp [Matrix.mul_apply]
    rw [h]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_re_le_one := by
    simp [Matrix.trace]

/-- Density route: on `|+⟩⟨+|`, each outcome of the measurement has weight `1 / 2`. -/
theorem outcomeMeasure_measureZ_plus (a : Fin 2) :
    measureZ.outcomeMeasure plus {a} = ENNReal.ofReal (1 / 2) := by
  rw [SubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- The amplitude `1 / √2`. -/
noncomputable def amp : ℂ := ((√2 : ℝ) : ℂ)⁻¹

theorem amp_mul_amp : amp * amp = 1 / 2 := by
  rw [amp, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem conj_amp : (starRingEnd ℂ) amp = amp := by
  rw [amp, ← Complex.ofReal_inv]
  exact Complex.conj_ofReal _

theorem norm_amp_sq : ‖amp‖ ^ 2 = 1 / 2 := by
  rw [sq, ← norm_mul, amp_mul_amp]
  norm_num

/-- The Hadamard gate. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![amp, amp; amp, -amp]

theorem hadamard_mem_unitaryGroup : hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two, conj_amp, amp_mul_amp] <;> norm_num

/-- The Hadamard gate as an element of the unitary group. -/
noncomputable def hadamardGate : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨hadamard, hadamard_mem_unitaryGroup⟩

/-- The basis vector `|0⟩`. -/
noncomputable def ket0 : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 1

theorem norm_ket0_le_one : ‖ket0‖ ≤ 1 := by
  simp [ket0]

/-- The Hadamard gate sends `|0⟩` to `|+⟩`. -/
theorem hadamard_applyVec_ket0 : hadamard •ᵥ ket0 = toLp 2 ![amp, amp] := by
  ext i
  fin_cases i <;> simp [hadamard, ket0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The Hadamard gate followed by the computational-basis measurement. -/
noncomputable def hadamardThenMeasure : SubInstrument (Fin 2) (Fin 2) (Fin 2) :=
  SubInstrument.ofUnitary hadamardGate >>= fun _ ↦ measureZ

/-- Each computational-basis component of `|+⟩` has squared norm `1 / 2`. -/
theorem norm_sq_proj_applyVec_hadamard_applyVec_ket0 (a : Fin 2) :
    ‖proj a •ᵥ hadamard •ᵥ ket0‖ ^ 2 = 1 / 2 := by
  rw [hadamard_applyVec_ket0, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  fin_cases a <;>
    simp [proj, Matrix.mulVec, dotProduct, Matrix.single_apply, norm_amp_sq]

/-- Vector route: each outcome has weight `1 / 2`, by the Born rule on `H •ᵥ |0⟩`. -/
example (a : Fin 2) :
    hadamardThenMeasure.outcomeMeasure (.ofVector ket0 norm_ket0_le_one) {a} =
      ENNReal.ofReal (1 / 2) := by
  rw [hadamardThenMeasure, SubInstrument.outcomeMeasure_ofUnitary_bind_ofVector, measureZ,
    SubInstrument.outcomeMeasure_ofKraus_ofVector_singleton]
  exact congrArg ENNReal.ofReal (norm_sq_proj_applyVec_hadamard_applyVec_ket0 a)

/-- The pure substate of `H •ᵥ |0⟩` is the density matrix `|+⟩⟨+|`. -/
theorem ofVector_hadamard_applyVec_ket0 (h : ‖hadamard •ᵥ ket0‖ ≤ 1) :
    SubState.ofVector (hadamard •ᵥ ket0) h = plus := by
  refine SubState.ext ?_
  ext i j
  simp only [SubState.matrix_ofVector, hadamard_applyVec_ket0, ketBra_apply, plus]
  fin_cases i <;> fin_cases j <;> simp [conj_amp, amp_mul_amp]

/-- Agreement with the density route: the outcome measure computed with vectors is the outcome
measure of the measurement on `|+⟩⟨+|`. -/
theorem outcomeMeasure_hadamardThenMeasure_ket0 :
    hadamardThenMeasure.outcomeMeasure (.ofVector ket0 norm_ket0_le_one) =
      measureZ.outcomeMeasure plus := by
  rw [hadamardThenMeasure, SubInstrument.outcomeMeasure_ofUnitary_bind_ofVector]
  exact congrArg _ (ofVector_hadamard_applyVec_ket0 _)

/-- The two routes give the same weight `1 / 2`. -/
example (a : Fin 2) :
    hadamardThenMeasure.outcomeMeasure (.ofVector ket0 norm_ket0_le_one) {a} =
      ENNReal.ofReal (1 / 2) := by
  rw [outcomeMeasure_hadamardThenMeasure_ket0, outcomeMeasure_measureZ_plus]

/-- Changing the input vector moves the weight of every event by at most twice the distance. -/
example (ψ φ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) (s : Set (Fin 2)) :
    |(measureZ.outcomeMeasure (.ofVector ψ hψ)).real s -
      (measureZ.outcomeMeasure (.ofVector φ hφ)).real s| ≤ 2 * ‖ψ - φ‖ :=
  SubInstrument.abs_outcomeMeasure_real_ofKraus_ofVector_sub_le_two_mul proj
    sum_conjTranspose_proj_mul_proj ψ φ hψ hφ s

/-! ## Commutators of Pauli matrices -/

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The Pauli matrix `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The commutator of `X` and `Z`. -/
theorem commutator_pauliX_pauliZ : ⁅pauliX, pauliZ⁆ = !![0, -2; 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ring.lie_def, pauliX, pauliZ] <;> norm_num

theorem norm_pauliZ_le_one : ‖pauliZ‖ ≤ 1 := by
  refine l2_opNorm_le_one_of_isometry ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The telescoped Leibniz bound on the commutator of `X` with `Z * Z`. -/
example : ‖⁅pauliX, pauliZ * pauliZ⁆‖ ≤ ‖⁅pauliX, pauliZ⁆‖ + ‖⁅pauliX, pauliZ⁆‖ := by
  simpa using norm_commutator_list_prod_le pauliX [pauliZ, pauliZ]
    (by simpa using norm_pauliZ_le_one)

/-! ## The hybrid bound at one query -/

/-- With one query, two oracles lead to final states at distance at most the norm of their
difference on the state before the query. -/
example {A : Type} [Fintype A] [DecidableEq A] (U₀ U₁ O O' : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ A) (hU₁ : ‖U₁‖ ≤ 1) (hO' : ‖O'‖ ≤ 1) :
    ‖U₁ •ᵥ O •ᵥ U₀ •ᵥ ψ - U₁ •ᵥ O' •ᵥ U₀ •ᵥ ψ‖ ≤ ‖(O - O') •ᵥ U₀ •ᵥ ψ‖ := by
  have h := norm_queryState_const_sub_queryState_const_le (fun i ↦ if i = 0 then U₀ else U₁)
    O O' ψ 1 (by simpa using hU₁) hO'
  simpa using h

/-- The hybrid bound for a Hadamard, one call to `Z` or to the identity, and a Hadamard. -/
example :
    ‖hadamard •ᵥ pauliZ •ᵥ hadamard •ᵥ ket0 - hadamard •ᵥ (1 : Matrix _ _ ℂ) •ᵥ hadamard •ᵥ ket0‖ ≤
      ‖(pauliZ - 1) •ᵥ hadamard •ᵥ ket0‖ := by
  have h := norm_queryState_const_sub_queryState_const_le (fun _ ↦ hadamard) pauliZ 1 ket0 1
    (fun _ _ ↦ l2_opNorm_le_one_of_mem_unitaryGroup hadamard_mem_unitaryGroup) l2_opNorm_one_le
  simpa using h

/-! ## A gate on one of two qubits -/

/-- A Hadamard gate on the first of two qubits is a contraction. -/
example : ‖hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1 :=
  (l2_opNorm_kronecker_one (R := Fin 2) hadamard).le.trans
    (l2_opNorm_le_one_of_mem_unitaryGroup hadamard_mem_unitaryGroup)

/-- Framing the Hadamard gate by a second qubit applies `H ⊗ₖ 1`, and sends `|0⟩ ⊗ χ` to
`|+⟩ ⊗ χ`. -/
example (χ : EuclideanSpace ℂ (Fin 2)) (h : ‖ket0 ⊗ᵥ χ‖ ≤ 1)
    (h' : ‖(hadamard •ᵥ ket0) ⊗ᵥ χ‖ ≤ 1) :
    ((SubInstrument.ofUnitary hadamardGate).frame (Fin 2)).post (.ofVector (ket0 ⊗ᵥ χ) h)
      PUnit.unit = .ofVector ((hadamard •ᵥ ket0) ⊗ᵥ χ) h' :=
  SubInstrument.post_frame_ofContraction_ofVector_tensorVec ..

end VCVioTest.QuantumPure
