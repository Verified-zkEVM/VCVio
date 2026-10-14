/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Observe

/-!
# Qubit measurement regression tests

The computational-basis measurement of one qubit, built from its two diagonal projectors, is
lossless, also when framed by an ancilla; measuring twice never reports two different outcomes;
and on the state `|+⟩⟨+|` each outcome has weight `1 / 2`, for total mass one under the bundled
semantics.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ComplexOrder

namespace VCVioTest.QuantumBasic

/-- The projector onto the computational-basis state `i` of a qubit. -/
def proj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i 1

/-- The computational-basis projectors satisfy the completeness relation. -/
theorem sum_conjTranspose_proj_mul_proj : ∑ i, (proj i)ᴴ * proj i = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj, Matrix.sum_apply, Matrix.single_apply]

/-- Measurement of a qubit in the computational basis. -/
noncomputable def measureZ : SubInstrument (Fin 2) (Fin 2) (Fin 2) :=
  SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj

/-- The computational-basis measurement is lossless. -/
theorem lossless_measureZ : measureZ.Lossless :=
  SubInstrument.lossless_ofKraus _ _

/-- Framing the measurement by a three-level ancilla keeps it lossless. -/
example : (measureZ.frame (Fin 3)).Lossless :=
  lossless_measureZ.frame _

/-- Measuring twice never reports two different outcomes. -/
example (a b : Fin 2) (h : a ≠ b) :
    (do
      let x ← measureZ
      let y ← measureZ
      pure (x, y) : SubInstrument (Fin 2) (Fin 2) (Fin 2 × Fin 2)).branch (a, b) = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [measureZ, SubInstrument.branch_bind_apply_univ, Fin.sum_univ_two,
      Finsupp.single_apply, ← MatrixMap.conj_mul, proj] at h ⊢

/-- The state `|+⟩⟨+|`. -/
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

/-- On `|+⟩⟨+|`, each outcome of the computational-basis measurement has weight `1 / 2`. -/
example (a : Fin 2) : (measureZ.branch a plus.matrix).trace = 1 / 2 := by
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- On `|+⟩⟨+|`, the outcome measure gives each outcome mass `1 / 2`. -/
example (a : Fin 2) : measureZ.outcomeMeasure plus {a} = ENNReal.ofReal (1 / 2) := by
  rw [SubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- Under the bundled semantics started from `|+⟩⟨+|`, the measurement has total mass one. -/
example : (SubInstrument.semanticsVia plus).evalDist measureZ Set.univ = 1 := by
  rw [SubInstrument.semanticsVia_evalDist, lossless_measureZ.outcomeMeasure_apply_univ]
  simp [plus, Matrix.trace]

end VCVioTest.QuantumBasic
