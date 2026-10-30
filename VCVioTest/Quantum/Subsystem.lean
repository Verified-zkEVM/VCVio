/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Lift
public import VCVioTest.Quantum.Oracle

/-!
# Subsystem and lifting regression tests

* **A gate on a subsystem.** The bit flip lifted to the second qubit of `Fin 2 × Fin 2` moves
  `|0, 0⟩` to `|0, 1⟩`, and lifted to the first qubit moves it to `|1, 0⟩`.
* **Lifting a program.** A call, lifted into a register with an extra qubit, keeps its budget of
  one call and still needs it, and stays lossless under the framed interpretation.
* **Operations on named subsystems.** A program over the framed signature applies one gate to
  the second qubit: it costs one gate and not zero.
-/

public section

open Quantum Matrix VCVioTest.QuantumOracle

namespace VCVioTest.QuantumSubsystem

/-- The bit flip on one qubit. -/
noncomputable abbrev flip : SubInstrument (QReg.of (Fin 2)) (QReg.of (Fin 2)) Unit :=
  SubInstrument.relabel (Equiv.swap (0 : Fin 2) 1)

/-- The bit flip on the second qubit moves `|0, 0⟩` to `|0, 1⟩`. -/
example : (flip.lift (Subsystem.snd (QReg.of (Fin 2)) (QReg.of (Fin 2)))).branch ()
      (Matrix.single ((0 : Fin 2), (0 : Fin 2)) (0, 0) 1) =
    Matrix.single ((0 : Fin 2), (1 : Fin 2)) (0, 1) 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [SubInstrument.lift_branch_apply, submatrix_apply, MatrixMap.amplify_apply,
    SubInstrument.relabel_branch_apply]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp +decide [Subsystem.snd, Matrix.single_apply, Equiv.swap_apply_def]

/-- The bit flip on the first qubit moves `|0, 0⟩` to `|1, 0⟩`. -/
example : (flip.lift (Subsystem.fst (QReg.of (Fin 2)) (QReg.of (Fin 2)))).branch ()
      (Matrix.single ((0 : Fin 2), (0 : Fin 2)) (0, 0) 1) =
    Matrix.single ((1 : Fin 2), (0 : Fin 2)) (1, 0) 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [SubInstrument.lift_branch_apply, submatrix_apply, MatrixMap.amplify_apply,
    SubInstrument.relabel_branch_apply]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp +decide [Subsystem.fst, Matrix.single_apply, Equiv.swap_apply_def]

/-! ## Lifting a program -/

/-- One call on the query and response qubits, with the trivial remainder. -/
noncomputable abbrev oneCall :=
  QuantumComp.query (L := LocalSig.instruments.{0}) (spec := qrom2) (A := QReg.of Reg) ()
    (QReg.of Unit) (Equiv.prodPUnit Reg).symm

/-- The call on the first factor of `Reg × Fin 2`, with one more qubit in the complement. -/
noncomputable abbrev liftedCall :=
  oneCall.lift (Subsystem.fst (QReg.of Reg) (QReg.of (Fin 2)))

/-- The lifted call keeps its budget of one call. -/
example : liftedCall.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp.isQueryBound_lift_iff _ _ _).mpr
    ((QuantumComp.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos)

/-- The lifted call still calls the oracle. -/
example : ¬ liftedCall.IsQueryBound 0 := fun h ↦
  Nat.lt_irrefl 0 ((QuantumComp.isQueryBound_query_iff _ _ _ _).mp
    ((QuantumComp.isQueryBound_lift_iff _ _ _).mp h))

/-- The lifted call is lossless under the framed interpretation. -/
example : liftedCall.Lossless LocalSig.Interp.instruments.framed :=
  (QuantumComp.lossless_query _ _ _).lift _

/-! ## Operations on named subsystems -/

/-- Flip the second qubit of a two-qubit register, as one operation on a named subsystem. -/
@[expose]
noncomputable def flipSecond :=
  QuantumComp.primAt (spec := qrom2) (L := LocalSig.instruments.{0})
    (Subsystem.snd (QReg.of (Fin 2)) (QReg.of (Fin 2)))
    ⟨Unit, fun _ ↦ QReg.of (Fin 2), flip⟩

/-- Applying one gate to a subsystem costs one gate. -/
example : flipSecond.IsCostBound (fun _ _ ↦ 1) 1 :=
  ⟨le_rfl, fun _ ↦ trivial⟩

/-- Applying one gate to a subsystem does not cost zero gates. -/
example : ¬ flipSecond.IsCostBound (fun _ _ ↦ 1) 0 :=
  fun h ↦ absurd h.1 (by decide)

/-- Lifting a gate to a larger register preserves its nonzero operation cost. -/
example : (flipSecond.lift
    (Subsystem.fst (QReg.of (Fin 2 × Fin 2)) (QReg.of (Fin 2)))).IsCostBound
      (fun _ _ ↦ 1) 1 :=
  (QuantumComp.isCostBound_lift_iff (fun _ _ ↦ 1) _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩

/-- A spectator cannot make a charged gate fit within the zero budget. -/
example : ¬ (flipSecond.lift
    (Subsystem.fst (QReg.of (Fin 2 × Fin 2)) (QReg.of (Fin 2)))).IsCostBound
      (fun _ _ ↦ 1) 0 := fun h ↦
  absurd ((QuantumComp.isCostBound_lift_iff (fun _ _ ↦ 1) _ _ _).mp h).1 (by decide)

end VCVioTest.QuantumSubsystem
