/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Pure.Tensor
public import VCVioTest.Quantum.Basic

/-!
# Pure-state regression tests

A Hadamard gate followed by the computational-basis measurement of one qubit, started from
`|0⟩`, reports each outcome with weight `1 / 2`: once through the Born rule on vectors, and once
through the density matrix `|+⟩⟨+|`, which the vector route reaches. Further checks cover
natural-number projective labels, complex phase and interference, Pauli commutator bounds,
the hybrid bound at one query, the norm of a gate on one of two qubits, and local measurement
of a Bell pair. A keep-or-discard measurement checks outcome-dependent output registers. Last,
the geometric instrument, which has infinitely many outcomes, is written in Kraus form, and the Born
rule on vectors gives outcome `n` the weight
`2^{-(n+1)} ‖ψ‖ ^ 2`.
-/

public section

open Quantum Matrix MeasureTheory WithLp
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace VCVioTest.QuantumPure

/-! ## Constant-output composition -/

section constantOutput

variable {A B C R α β γ : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype R]

/-- Repeated relabelling infers its output register without an expected result type. -/
noncomputable example (p : SubInstrument A B α) (f : α → β) (g : β → γ) :=
  (p.map f).map g

/-- Relabelling a bind infers the continuation's constant output register. -/
noncomputable example (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (g : β → γ) := (p.bind k).map g

/-- Relabelling a frame infers the extended constant output register. -/
noncomputable example (p : SubInstrument A B α) (f : α → β) := (p.frame R).map f

/-- Losslessness chains through bind and relabelling without a supplied result type. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) (g : β → γ) := (hp.bind hk).map g

/-- Losslessness chains through frame and relabelling without a supplied result type. -/
example (p : SubInstrument A B α) (hp : p.Lossless) (f : α → β) := (hp.frame R).map f

/-- The left unit law rewrites a constant-output bind through an ordinary import. -/
example (a : α) (k : α → SubInstrument A B β) : (SubInstrument.pure a).bind k = k a := by
  rw [SubInstrument.pure_bind]

/-- Framing and sequencing rewrite using the constant-output law. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).frame R = (p.frame R).bind fun a ↦ (k a).frame R := by
  rw [SubInstrument.frame_bind]

end constantOutput

/-! ## Hadamard, then measure -/

/-- The projector onto the computational-basis state `i` of a qubit. -/
def proj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i 1

/-- The computational-basis projectors satisfy Kraus completeness. -/
theorem sum_conjTranspose_proj_mul_proj : ∑ i, (proj i)ᴴ * proj i = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj, Matrix.sum_apply, Matrix.single_apply]

/-- Each computational-basis projector is a self-adjoint idempotent. -/
theorem isStarProjection_proj (i : Fin 2) : IsStarProjection (proj i) := by
  constructor
  · change proj i * proj i = proj i
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [proj]
  · change (proj i)ᴴ = proj i
    simp [proj]

/-- Computational-basis projections labelled by naturals, with support `{0, 1}`. -/
def natProj (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if n = 0 then proj 0 else if n = 1 then proj 1 else 0

/-- Every natural-labelled branch is a star projection, including the zero branches. -/
theorem isStarProjection_natProj (n : ℕ) : IsStarProjection (natProj n) := by
  unfold natProj
  split_ifs <;> first | exact isStarProjection_proj _ | exact IsStarProjection.zero _

/-- All natural-labelled projections outside `{0, 1}` vanish. -/
theorem natProj_eq_zero (n : ℕ) (hn : n ∉ ({0, 1} : Finset ℕ)) : natProj n = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [natProj, hn.1, hn.2]

/-- The two nonzero natural-labelled projections sum to the identity. -/
theorem sum_natProj : ∑ n ∈ ({0, 1} : Finset ℕ), natProj n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [natProj, proj]

/-- A projective measurement with arbitrary natural-number outcome labels. -/
noncomputable def measureNat : SubInstrument (Fin 2) (Fin 2) ℕ :=
  SubInstrument.ofProjectiveFinset natProj isStarProjection_natProj {0, 1}
    natProj_eq_zero sum_natProj

/-- Relabelling a projective measurement infers its output register before observing branches. -/
noncomputable example (f : ℕ → ℝ) := (measureNat.map f).branch

/-- Losslessness of a projective measurement supports constant-output relabelling. -/
example (f : ℕ → ℝ) : (measureNat.map f).Lossless := by
  have hp := SubInstrument.lossless_ofProjectiveFinset natProj isStarProjection_natProj {0, 1}
    natProj_eq_zero sum_natProj
  exact hp.map f

/-- Total-map rewriting composes with constant mapping and the constant right unit law. -/
example (f : ℕ → ℝ) :
    ((measureNat.map f).bind SubInstrument.pure).total = measureNat.total := by
  rw [SubInstrument.bind_pure, DSubInstrument.total_map]

/-- A framed projective measurement exposes its amplified total map through field notation. -/
example : (measureNat.frame (Fin 2)).total = measureNat.total.amplify (Fin 2) := by
  rw [DSubInstrument.total_frame]

/-- Both projections in the natural-labelled support are nonzero. -/
example : natProj 0 ≠ 0 ∧ natProj 1 ≠ 0 := by
  constructor
  · intro h
    have := congrArg (fun M ↦ M 0 0) h
    simp [natProj, proj] at this
  · intro h
    have := congrArg (fun M ↦ M 1 1) h
    simp [natProj, proj] at this

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
  rw [DSubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- The amplitude `1 / √2`. -/
noncomputable def amp : ℂ := ((√2 : ℝ) : ℂ)⁻¹

/-- The square of the real Hadamard amplitude is one half. -/
theorem amp_mul_amp : amp * amp = 1 / 2 := by
  rw [amp, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The Hadamard amplitude is fixed by complex conjugation. -/
theorem conj_amp : (starRingEnd ℂ) amp = amp := by
  rw [amp, ← Complex.ofReal_inv]
  exact Complex.conj_ofReal _

/-- The squared norm of the Hadamard amplitude is one half. -/
theorem norm_amp_sq : ‖amp‖ ^ 2 = 1 / 2 := by
  rw [sq, ← norm_mul, amp_mul_amp]
  norm_num

/-- The Hadamard gate. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![amp, amp; amp, -amp]

/-- The Hadamard matrix is unitary. -/
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

/-- The computational-basis vector is subnormalized. -/
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
    DSubInstrument.outcomeMeasure_ofKraus_ofVector_singleton]
  exact congrArg ENNReal.ofReal (norm_sq_proj_applyVec_hadamard_applyVec_ket0 a)

/-- Natural labels give weights one half at `0` and `1`, and zero everywhere else. -/
example (n : ℕ) :
    measureNat.outcomeMeasure
      (.ofVector (hadamard •ᵥ ket0)
        (norm_applyVec_le_one
          (l2_opNorm_le_one_of_mem_unitaryGroup hadamard_mem_unitaryGroup) norm_ket0_le_one))
      {n} = if n = 0 ∨ n = 1 then ENNReal.ofReal (1 / 2) else 0 := by
  rw [measureNat, SubInstrument.outcomeMeasure_ofProjectiveFinset_ofVector_singleton]
  by_cases h0 : n = 0
  · simp [natProj, h0, norm_sq_proj_applyVec_hadamard_applyVec_ket0]
  · by_cases h1 : n = 1
    · simp [natProj, h1, norm_sq_proj_applyVec_hadamard_applyVec_ket0]
    · simp [natProj, h0, h1]

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
  DSubInstrument.abs_outcomeMeasure_real_ofKraus_ofVector_sub_le_two_mul proj
    sum_conjTranspose_proj_mul_proj ψ φ hψ hφ s

/-! ## Complex phase and interference -/

/-- The phase gate `S = diag(1, i)`. -/
def phaseGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.I]

/-- Applying `S` to `|+⟩` gives amplitudes `(1, i) / √2`. -/
theorem phaseGate_applyVec_plus :
    phaseGate •ᵥ hadamard •ᵥ ket0 = toLp 2 ![amp, Complex.I * amp] := by
  rw [hadamard_applyVec_ket0]
  ext i
  fin_cases i <;> simp [phaseGate, mul_comm]

/-- The vector `S|+⟩` is normalized. -/
theorem norm_phaseGate_applyVec_plus : ‖phaseGate •ᵥ hadamard •ᵥ ket0‖ = 1 := by
  have hsq : ‖phaseGate •ᵥ hadamard •ᵥ ket0‖ ^ 2 = 1 := by
    rw [phaseGate_applyVec_plus, EuclideanSpace.norm_sq_eq]
    norm_num [Fin.sum_univ_two, norm_amp_sq]
  nlinarith [norm_nonneg (phaseGate •ᵥ hadamard •ᵥ ket0)]

/-- A Hadamard after `S|+⟩` gives amplitudes `(1 + i, 1 - i) / 2`. -/
theorem hadamard_applyVec_phaseGate_plus :
    hadamard •ᵥ phaseGate •ᵥ hadamard •ᵥ ket0 =
      toLp 2 ![(1 + Complex.I) / 2, (1 - Complex.I) / 2] := by
  rw [phaseGate_applyVec_plus]
  ext i
  fin_cases i <;> simp [hadamard]
  · linear_combination (1 + Complex.I) * amp_mul_amp
  · linear_combination (1 - Complex.I) * amp_mul_amp

/-- X-basis outcome statistics, obtained by applying a Hadamard and then measuring in the
computational basis. The retained output is in the computational basis: the branch operator
is `P_a H`. Applying a further Hadamard would give the X-basis Lüders instrument. -/
noncomputable def measureX : SubInstrument (Fin 2) (Fin 2) (Fin 2) :=
  SubInstrument.ofUnitary hadamardGate >>= fun _ ↦ measureZ

/-- The Born weights of an `X`-basis measurement on `S|+⟩` are both one half. -/
theorem outcomeMeasure_measureX_phaseGate_plus (a : Fin 2) :
    measureX.outcomeMeasure
      (.ofVector (phaseGate •ᵥ hadamard •ᵥ ket0) norm_phaseGate_applyVec_plus.le) {a} =
        ENNReal.ofReal (1 / 2) := by
  rw [measureX, SubInstrument.outcomeMeasure_ofUnitary_bind_ofVector, measureZ,
    DSubInstrument.outcomeMeasure_ofKraus_ofVector_singleton]
  change ENNReal.ofReal (‖proj a •ᵥ hadamard •ᵥ phaseGate •ᵥ hadamard •ᵥ ket0‖ ^ 2) = _
  rw [hadamard_applyVec_phaseGate_plus, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  fin_cases a <;> norm_num [proj, Matrix.mulVec, dotProduct, Matrix.single_apply,
    div_pow, Complex.sq_norm, Complex.normSq_apply]

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

/-- The Pauli Z matrix is a contraction. -/
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
example (χ : EuclideanSpace ℂ (Fin 2)) (h : ‖ket0 ⊗ᵥ χ‖ ≤ 1) :
    ((SubInstrument.ofUnitary hadamardGate).frame (Fin 2)).post (.ofVector (ket0 ⊗ᵥ χ) h)
      PUnit.unit = .ofVector ((hadamard •ᵥ ket0) ⊗ᵥ χ)
        (norm_applyVec_tensorVec_le_one
          (l2_opNorm_le_one_of_mem_unitaryGroup hadamard_mem_unitaryGroup) ket0 χ h) :=
  SubInstrument.post_frame_ofContraction_ofVector_tensorVec ..

/-! ## A Bell pair and local measurement -/

/-- The basis vector `|1⟩`. -/
noncomputable def ket1 : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 1 1

/-- The Bell vector `(|00⟩ + |11⟩) / √2`, expressed using tensor products. -/
noncomputable def bell : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  amp • (ket0 ⊗ᵥ ket0) + amp • (ket1 ⊗ᵥ ket1)

/-- The Bell vector has norm one. -/
theorem norm_bell : ‖bell‖ = 1 := by
  have hsq : ‖bell‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [bell, ket0, ket1, Fintype.sum_prod_type, Fin.sum_univ_two, norm_amp_sq]
  nlinarith [norm_nonneg bell]

/-- Projecting the first half of a Bell pair selects the matching basis state in both halves. -/
theorem proj_kronecker_one_applyVec_bell (a : Fin 2) :
    (proj a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) •ᵥ bell =
      amp • (EuclideanSpace.single a 1 ⊗ᵥ EuclideanSpace.single a 1) := by
  ext ⟨i, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [bell, ket0, ket1, proj, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.single_apply, Matrix.one_apply]

/-- Each local Bell branch has squared norm one half. -/
theorem norm_sq_proj_kronecker_one_applyVec_bell (a : Fin 2) :
    ‖(proj a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) •ᵥ bell‖ ^ 2 = 1 / 2 := by
  rw [proj_kronecker_one_applyVec_bell]
  simp [norm_smul, norm_tensorVec, norm_amp_sq]

/-- Measuring the first qubit of the Bell pair reports either bit with weight one half. -/
theorem outcomeMeasure_frame_measureZ_bell (a : Fin 2) :
    (measureZ.frame (Fin 2)).outcomeMeasure (.ofVector bell norm_bell.le) {a} =
      ENNReal.ofReal (1 / 2) := by
  rw [measureZ, SubInstrument.frame_ofKraus,
    DSubInstrument.outcomeMeasure_ofKraus_ofVector_singleton,
    norm_sq_proj_kronecker_one_applyVec_bell]

/-- The retained Bell branch is the unnormalized correlated vector `|aa⟩ / √2`. -/
theorem post_frame_measureZ_bell (a : Fin 2) :
    ∃ h, (measureZ.frame (Fin 2)).post (.ofVector bell norm_bell.le) a =
      .ofVector (amp • (EuclideanSpace.single a 1 ⊗ᵥ EuclideanSpace.single a 1)) h := by
  have hamp : ‖amp‖ ≤ 1 := by nlinarith [norm_amp_sq, norm_nonneg amp]
  refine ⟨by simpa [norm_smul, norm_tensorVec] using hamp, SubState.ext ?_⟩
  simp only [measureZ, SubInstrument.frame_ofKraus, DSubInstrument.post_ofKraus_ofVector,
    SubState.matrix_ofVector, proj_kronecker_one_applyVec_bell]

/-! ## Outcome-dependent output registers -/

/-- The vector event bound applies when one outcome keeps a qubit and the other discards it.
This checks elaboration with output dimensions two and one in the same Kraus family. -/
example (ψ φ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1)
    (s : Set (Fin 2)) :
    let p := DSubInstrument.ofKraus QuantumBasic.keepKraus QuantumBasic.sum_keepKraus
    |(p.outcomeMeasure (.ofVector ψ hψ)).real s -
      (p.outcomeMeasure (.ofVector φ hφ)).real s| ≤ 2 * ‖ψ - φ‖ :=
  DSubInstrument.abs_outcomeMeasure_real_ofKraus_ofVector_sub_le_two_mul
    QuantumBasic.keepKraus QuantumBasic.sum_keepKraus ψ φ hψ hφ s

/-- The vector chain rule accepts a continuation with outcome-dependent output registers. -/
example (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ ≤ 1) :
    let p := DSubInstrument.ofKraus QuantumBasic.keepKraus QuantumBasic.sum_keepKraus
    (p.bind QuantumBasic.remeasure).outcomeMeasure (.ofVector ψ hψ) =
      ∑ i, (QuantumBasic.remeasure i).outcomeMeasure (p.post (.ofVector ψ hψ) i) := by
  dsimp only
  rw [DSubInstrument.outcomeMeasure_ofKraus_bind_ofVector]
  simp_rw [DSubInstrument.post_ofKraus_ofVector]

/-! ## A measurement with infinitely many outcomes -/

/-- The amplitude `√(2^{-(n+1)})` of the outcome `n` of the geometric instrument. -/
noncomputable def geomAmp (n : ℕ) : ℂ :=
  ((√(QuantumBasic.geomWeight n) : ℝ) : ℂ)

/-- Each branch of the geometric instrument is the Kraus map of a multiple of the identity. -/
theorem geometric_branch_eq_conj (n : ℕ) :
    QuantumBasic.geometric.branch n =
      MatrixMap.conj (geomAmp n • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hc : star (geomAmp n) = geomAmp n := Complex.conj_ofReal _
  have hw : geomAmp n * geomAmp n = (QuantumBasic.geomWeight n : ℂ) := by
    rw [geomAmp, ← Complex.ofReal_mul, Real.mul_self_sqrt (QuantumBasic.geomWeight_nonneg n)]
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [QuantumBasic.geometric_branch_apply, MatrixMap.conj_apply, conjTranspose_smul,
    conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, hc, hw]

/-- Born rule on vectors for the geometric instrument, whose outcomes are all of `ℕ`: on the pure
substate of `ψ`, outcome `n` has weight `2^{-(n+1)} ‖ψ‖ ^ 2`. -/
example (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ ≤ 1) (n : ℕ) :
    QuantumBasic.geometric.outcomeMeasure (.ofVector ψ hψ) {n} =
      ENNReal.ofReal (QuantumBasic.geomWeight n * ‖ψ‖ ^ 2) := by
  rw [DSubInstrument.outcomeMeasure_ofVector_singleton_of_branch_eq_conj _
    (geometric_branch_eq_conj n)]
  congr 1
  rw [map_smul, LinearMap.smul_apply, one_applyVec, norm_smul, mul_pow, geomAmp,
    Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (QuantumBasic.geomWeight_nonneg n)]

/-- After outcome `n` of the geometric instrument, the pure substate of `ψ` is that of the
rescaled vector `√(2^{-(n+1)}) • ψ`. -/
example (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ ≤ 1) (n : ℕ) :
    ∃ h, QuantumBasic.geometric.post (.ofVector ψ hψ) n = .ofVector (geomAmp n • ψ) h := by
  refine ⟨?_, (DSubInstrument.post_ofVector_of_branch_eq_conj _
    (geometric_branch_eq_conj n) ψ hψ).trans ?_⟩
  · exact ((QuantumBasic.geometric.norm_applyVec_le_of_branch_eq_conj
      (geometric_branch_eq_conj n) ψ).trans hψ).trans_eq' (by
        rw [map_smul, LinearMap.smul_apply, one_applyVec])
  · congr 1
    rw [map_smul, LinearMap.smul_apply, one_applyVec]

end VCVioTest.QuantumPure
