/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.Parallel
public import VCVio.Quantum.Comp.TotalQueryBound
public import Mathlib.Data.ZMod.Basic

/-!
# Parallel oracle regression tests

Exact checks of simultaneous queries, coherent inputs, repeated inputs, widths larger than
the domain, zero-width calls, and the ordering of steps that share private memory.
-/

public section

open Quantum Matrix
open scoped Kronecker

namespace VCVioTest.QuantumParallel

/-- Two copies of the same input both receive the same oracle answer. -/
example :
    parallelOracleEquiv (fun _ : Unit ↦ (1 : ZMod 3)) 2 (fun _ ↦ ((), 0)) =
      fun _ ↦ ((), 1) := by
  funext i
  simp

/-- The width may exceed the domain cardinality without distinct-input assumptions. -/
example :
    parallelOracleEquiv (fun _ : Unit ↦ (2 : ZMod 5)) 3 (fun _ ↦ ((), 4)) =
      fun _ ↦ ((), 1) := by
  funext i
  change ((), (4 : ZMod 5) + 2) = ((), 1)
  decide

/-- On a cyclic group of order three, two equal queries do not cancel. -/
example :
    parallelOracleEquiv (fun _ : Unit ↦ (1 : ZMod 3)) 2
        (parallelOracleEquiv (fun _ : Unit ↦ (1 : ZMod 3)) 2 (fun _ ↦ ((), 0))) =
      fun _ ↦ ((), 2) := by
  funext i
  norm_num

/-- The inverse subtracts the same answer in every slot. -/
example (H : Unit → ZMod 5) (x : Fin 2 → Unit × ZMod 5) :
    (parallelOracleEquiv H 2).symm (parallelOracleEquiv H 2 x) = x :=
  Equiv.symm_apply_apply _ _

/-- The matrix law applies to an entangled superposition, retaining both coherent terms. -/
example :
    parallelOracleUnitary (id : ZMod 2 → ZMod 2) 2 *ᵥ
        (Pi.single (fun _ : Fin 2 ↦ ((0 : ZMod 2), (0 : ZMod 2))) 1 +
          Pi.single (fun _ : Fin 2 ↦ ((1 : ZMod 2), (0 : ZMod 2))) 1) =
      Pi.single (fun _ : Fin 2 ↦ ((0 : ZMod 2), (0 : ZMod 2))) 1 +
        Pi.single (fun _ : Fin 2 ↦ ((1 : ZMod 2), (1 : ZMod 2))) 1 := by
  rw [Matrix.mulVec_add, parallelOracleUnitary_mulVec_single,
    parallelOracleUnitary_mulVec_single]
  rfl

/-- Ordered batching equals the simultaneous query on all matrices, including coherent inputs. -/
example (H : Unit → ZMod 3) (ρ : Matrix ((Fin 2 → Unit × ZMod 3) × Unit)
    ((Fin 2 → Unit × ZMod 3) × Unit) ℂ) :
    (SubInstrument.batch (QReg.of (Unit × ZMod 3)) (QReg.of Unit)
      ((oracleQuery H).frame Unit) 2).branch () ρ =
        ((parallelOracleQuery H 2).frame Unit).branch () ρ := by
  rw [batch_oracleQuery]

/-- A zero-width call also leaves private memory unchanged. -/
example (H : Unit → ZMod 3) :
    (parallelOracleRuntime H).step 0 = SubInstrument.pure () :=
  parallelOracleRuntime_step_zero H

/-- Port widths are classical natural numbers. -/
example : (qromBatchSpec Unit (ZMod 3)).Port = ℕ :=
  rfl

/-- The first oracle call selects width two, with the entire register as its input. -/
noncomputable def queryTwo :
    QComp (qromBatchSpec Unit (ZMod 3))
      (QReg.of (Fin 2 → Unit × ZMod 3))
      (QReg.of ((Fin 2 → Unit × ZMod 3) × Unit)) Unit :=
  QuantumComp₂.query (spec := qromBatchSpec Unit (ZMod 3)) 2
    (QReg.of Unit) (Equiv.prodPUnit _).symm

/-- A two-slot batch consumes one oracle round. -/
example : queryTwo.IsTotalQueryBound 1 := by
  simp [queryTwo, QuantumComp₂.query, QuantumComp.query,
    QuantumComp.isTotalQueryBound_queryBind_iff,
    QuantumComp.isTotalQueryBound_pure]

/-- A local operation may select different register sizes and query widths on its branches. -/
noncomputable def chooseWidth
    (p : DSubInstrument Unit Bool
      (fun b ↦ (Fin (if b then 2 else 0) → Unit × ZMod 3) × Unit)) :
    QuantumComp LocalSig.instruments (qromBatchSpec Unit (ZMod 3))
      (fun _ ↦ Unit) (QReg.of Unit) :=
  QuantumComp.primBind
    ⟨Bool, fun b ↦ QReg.of ((Fin (if b then 2 else 0) → Unit × ZMod 3) × Unit), p⟩
    fun b ↦ QuantumComp.queryBind (if b then 2 else 0) (QReg.of Unit)
      (Equiv.refl _) fun _ ↦ QuantumComp.pure ()

/-- Branch-dependent widths still consume one round on each branch. -/
example (p : DSubInstrument Unit Bool
    (fun b ↦ (Fin (if b then 2 else 0) → Unit × ZMod 3) × Unit)) :
    (chooseWidth p).IsTotalQueryBound 1 := by
  simp [chooseWidth, QuantumComp.isTotalQueryBound_primBind_iff,
    QuantumComp.isTotalQueryBound_queryBind_iff, QuantumComp.isTotalQueryBound_pure]

/-- Batching swaps slots `[false, true]` with shared memory `false` in increasing order,
producing slots `[false, false]` and memory `true`. -/
example :
    (SubInstrument.batch (QReg.of Bool) (QReg.of Bool)
      (SubInstrument.relabel (Equiv.prodComm Bool Bool)) 2).branch ()
        (Matrix.single (fun i : Fin 2 ↦ i == 1, false)
          (fun i : Fin 2 ↦ i == 1, false) 1) =
      Matrix.single (fun _ : Fin 2 ↦ false, true) (fun _ : Fin 2 ↦ false, true) 1 := by
  unfold SubInstrument.batch
  simp_rw [SubInstrument.lift_relabel (A := QReg.of (Bool × Bool))
    (M := QReg.of ((Fin 2 → Bool) × Bool))]
  rw [SubInstrument.sequenceUnit_relabel, SubInstrument.branch_relabel,
    conj_basisMatrix_equiv_single]
  congr 1 <;> decide

/-- Reversing those same lifted steps produces slots `[true, false]` and memory `false`,
so the batch's ordering determines the correlation with private memory. -/
example :
    (SubInstrument.sequenceUnit (fun i : Fin 2 ↦
      (SubInstrument.relabel (Equiv.prodComm Bool Bool)).lift
        (Subsystem.piWithMemory i (QReg.of Bool) (QReg.of Bool))) [1, 0]).branch ()
        (Matrix.single (fun i : Fin 2 ↦ i == 1, false)
          (fun i : Fin 2 ↦ i == 1, false) 1) =
      Matrix.single (fun i : Fin 2 ↦ i == 0, false)
        (fun i : Fin 2 ↦ i == 0, false) 1 := by
  simp_rw [SubInstrument.lift_relabel (A := QReg.of (Bool × Bool))
    (M := QReg.of ((Fin 2 → Bool) × Bool))]
  rw [SubInstrument.sequenceUnit_relabel, SubInstrument.branch_relabel,
    conj_basisMatrix_equiv_single]
  congr 1 <;> decide

end VCVioTest.QuantumParallel
