/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.DropEmptyBatches
public import Mathlib.Logic.Equiv.Bool

/-!
# Empty-round erasure regressions

Zero-width calls can outnumber queried points. Their removal preserves basis relabellings
and the complete joint quantum state, including off-diagonal private-memory correlations.
-/

public section

open Quantum Matrix

namespace VCVioTest.QuantumDropEmptyBatches

/-- One oracle point, surrounded by empty calls and register relabellings. -/
noncomputable def paddedQuery :
    QuantumComp LocalSig.instruments.{0} (uBatchSpec Unit fun _ ↦ QReg.of Bool)
      (fun _ ↦ Unit) (QReg.of ((Fin 1 → Bool) × Unit)) :=
  QuantumComp.queryBind ((), 0) (QReg.of ((Fin 1 → Bool) × Unit))
    (Equiv.uniqueProd _ (Fin 0 → Bool)).symm fun _ ↦
      QuantumComp.relabelThen (Equiv.uniqueProd _ (Fin 0 → Bool))
        (QuantumComp.queryBind ((), 1) (QReg.of Unit) (Equiv.refl _) fun _ ↦
          QuantumComp.queryBind ((), 0) (QReg.of ((Fin 1 → Bool) × Unit))
            (Equiv.uniqueProd _ (Fin 0 → Bool)).symm fun _ ↦ QuantumComp.pure ())

/-- Empty rounds make the syntactic round count strictly larger than the point count. -/
example : paddedQuery.IsPointBound 1 ∧ paddedQuery.IsTotalQueryBound 3 ∧
    ¬ paddedQuery.IsTotalQueryBound 1 := by
  simp [paddedQuery, QuantumComp.relabelThen]

/-- The erased program uses only one round, with no change to its one-point budget. -/
example : (paddedQuery.dropEmptyBatches .instruments).IsTotalQueryBound 1 ∧
    (paddedQuery.dropEmptyBatches .instruments).IsPointBound 1 := by
  have h : paddedQuery.IsPointBound 1 := by simp [paddedQuery, QuantumComp.relabelThen]
  exact ⟨h.isTotalQueryBound_dropEmptyBatches .instruments, h.dropEmptyBatches .instruments⟩

/-- Removing empty calls keeps the one-slot width cap of the retained call. -/
example : paddedQuery.IsWidthBound 1 ∧
    (paddedQuery.dropEmptyBatches .instruments).IsWidthBound 1 := by
  have h : paddedQuery.IsWidthBound 1 := by simp [paddedQuery, QuantumComp.relabelThen]
  exact ⟨h, h.dropEmptyBatches .instruments⟩

/-- Swapping each public slot with private memory makes retaining that memory observable. -/
@[expose, reducible]
noncomputable def swapRuntime : QuantumRuntime (uSpec Unit fun _ ↦ QReg.of Bool) where
  D := QReg.of Bool
  init := SubState.basis false
  step _ := SubInstrument.relabel (Equiv.prodComm Bool Bool)

/-- Erasure keeps every branch map, including the private qubit updated by the retained call. -/
example : swapRuntime.batch.run .instruments (paddedQuery.dropEmptyBatches .instruments) =
    swapRuntime.batch.run .instruments paddedQuery := by
  apply QuantumRuntime.run_dropEmptyBatches
  intro p
  exact SubInstrument.batch_zero (QReg.of Bool) (QReg.of Bool) (swapRuntime.step p)

/-- An empty call may change the public basis while its private coherences remain intact. -/
example :
    (swapRuntime.batch.queryStep (A := QReg.of Bool) ((), 0) (QReg.of Bool)
      (Equiv.boolNot.trans (Equiv.uniqueProd Bool (Fin 0 → Bool)).symm)).branch ()
        (Matrix.single (false, false) (true, true) (Complex.I : ℂ)) =
      (Matrix.single ((default, true), false) ((default, false), true) Complex.I :
        Matrix (((Fin 0 → Bool) × Bool) × Bool) (((Fin 0 → Bool) × Bool) × Bool) ℂ) := by
  rw [QuantumRuntime.queryStep_zero_width swapRuntime.batch
    (fun p ↦ SubInstrument.batch_zero (QReg.of Bool) (QReg.of Bool) (swapRuntime.step p)),
    DSubInstrument.branch_frame_apply]
  change ((SubInstrument.relabel
    (Equiv.boolNot.trans (Equiv.uniqueProd Bool (Fin 0 → Bool)).symm)).branch ()).amplify Bool
      (Matrix.single (false, false) (true, true) Complex.I) = _
  ext ⟨⟨u, a⟩, d⟩ ⟨⟨v, b⟩, e⟩
  rw [MatrixMap.amplify_apply, SubInstrument.relabel_branch_apply]
  have hu : u = default := Subsingleton.elim _ _
  have hv : v = default := Subsingleton.elim _ _
  subst u
  subst v
  cases a <;> cases b <;> cases d <;> cases e <;> simp

end VCVioTest.QuantumDropEmptyBatches
