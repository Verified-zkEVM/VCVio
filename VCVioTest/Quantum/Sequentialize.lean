/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Sequentialize
public import VCVio.Quantum.Oracle.Sequentialize
public import Mathlib.Logic.Equiv.Bool
public import Mathlib.Data.ZMod.Basic

/-!
# Sequentialization regressions

Path-wise point budgets, zero-width calls, adaptive register changes, and exact execution
with shared private memory.
-/

public section

open Quantum Matrix
open scoped Kronecker

namespace VCVioTest.QuantumSequentialize

/-- A zero-width call relabels a nontrivial caller register into its remainder. -/
noncomputable def zeroWidth :
    QuantumComp LocalSig.instruments (uBatchSpec Unit fun _ ↦ QReg.of Bool)
      (fun _ ↦ Unit) (QReg.of Bool) :=
  QuantumComp.queryBind ((), 0) (QReg.of Bool)
    (Equiv.boolNot.trans (Equiv.uniqueProd Bool (Fin 0 → Bool)).symm)
    fun _ ↦ QuantumComp.pure ()

/-- A width-zero call costs no points. -/
example : zeroWidth.IsPointBound 0 := by simp [zeroWidth]

/-- The same call consumes one round. -/
example : zeroWidth.IsTotalQueryBound 1 := by simp [zeroWidth]

/-- Zero points do not make a width-zero call disappear from the round budget. -/
example : ¬ zeroWidth.IsTotalQueryBound 0 := by simp [zeroWidth]

/-- A zero-width call applies the caller's basis relabelling and preserves private memory. -/
theorem run_zeroWidth_branch
    (R : QuantumRuntime (uSpec Unit fun _ ↦ QReg.of Bool)) (b : Bool) (d : R.D) :
    (R.batch.run .instruments zeroWidth).branch
        ⟨QReg.of ((Fin 0 → Bool) × Bool), ()⟩ (Matrix.single (b, d) (b, d) 1) =
      Matrix.single ((default, !b), d) ((default, !b), d) 1 := by
  rw [zeroWidth, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_unit]
  simp only [QuantumRuntime.run_pure, DSubInstrument.branch_ret_self,
    LinearMap.id_comp]
  have h := R.batch.queryStep_branch_single (A := QReg.of Bool) ((), 0) (QReg.of Bool)
    (Equiv.boolNot.trans (Equiv.uniqueProd Bool (Fin 0 → Bool)).symm) () b d
  dsimp only [QuantumRuntime.batch] at h
  refine h.trans ?_
  let s : Fin 0 → Bool := ((Equiv.uniqueProd Bool (Fin 0 → Bool)).symm (!b)).1
  change (SubInstrument.relabel (QuantumRuntime.queryEquivOut (Fin 0 → Bool) R.D Bool)).branch ()
    ((SubInstrument.pure (A := ((Fin 0 → Bool) × R.D)) ()).branch ()
      (Matrix.single (s, d) (s, d) 1) ⊗ₖ Matrix.single (!b) (!b) 1) = _
  rw [SubInstrument.branch_pure_self, LinearMap.id_apply, Matrix.single_kronecker_single,
    one_mul, SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
    QuantumRuntime.queryEquivOut_apply]
  congr 3 <;> exact Subsingleton.elim _ _

/-- Sequentializing a width-zero batch emits no oracle queries. -/
example : (zeroWidth.sequentialize .instruments).IsTotalQueryBound 0 :=
  (show zeroWidth.IsPointBound 0 by simp [zeroWidth]).sequentialize .instruments

/-- Two adaptive rounds with path sums three and five and different register sizes. -/
noncomputable def adaptive
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) :
    QuantumComp LocalSig.instruments (uBatchSpec Unit fun _ ↦ QReg.of Bool)
      (fun _ ↦ Unit) (QReg.of Unit) :=
  QuantumComp.primBind
    ⟨Bool, fun b ↦ QReg.of ((Fin (if b then 2 else 3) → Bool) × Unit), p⟩ fun b ↦
    QuantumComp.queryBind ((), if b then 2 else 3) (QReg.of Unit) (Equiv.refl _) fun _ ↦
      QuantumComp.primBind
        ⟨PUnit, fun _ ↦ QReg.of ((Fin (if b then 1 else 2) → Bool) × Bool), q b⟩ fun _ ↦
        QuantumComp.queryBind ((), if b then 1 else 2) (QReg.of Bool) (Equiv.refl _)
          fun _ ↦ QuantumComp.pure ()

/-- The exact point budget is the maximum path sum, smaller than the uniform product six. -/
theorem adaptive_point_iff
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) (n : ℕ) :
    (adaptive p q).IsPointBound n ↔ 5 ≤ n := by
  simp [adaptive, LocalSig.InstrumentOp.Outcome, Bool.forall_bool]
  omega

/-- Width caps constrain every batch without accumulating across rounds. -/
theorem adaptive_width_iff
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) (k : ℕ) :
    (adaptive p q).IsWidthBound k ↔ 3 ≤ k := by
  simp [adaptive, LocalSig.InstrumentOp.Outcome, Bool.forall_bool]
  omega

/-- Both branches make two rounds, independently of their widths and local outcomes. -/
theorem adaptive_round_iff
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) (r : ℕ) :
    (adaptive p q).IsTotalQueryBound r ↔ 2 ≤ r := by
  simp [adaptive, LocalSig.InstrumentOp.Outcome]
  omega

/-- A lossless local choice reaches only the shorter, width-two branch. -/
noncomputable def shortChoice :
    DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit :=
  DSubInstrument.classical (fun _ ↦ true) (fun _ ↦ (fun _ ↦ false, ()))

/-- The long branch has zero weight despite imposing the exact point and width budgets. -/
example : shortChoice.branch false (Matrix.single () () 1) = 0 := by
  simp [shortChoice, DSubInstrument.branch_classical_basis]

/-- The shorter branch is live: its continuation cannot mask the impossible long branch. -/
example : shortChoice.branch true (Matrix.single () () 1) =
    Matrix.single (fun _ : Fin 2 ↦ false, ()) (fun _ : Fin 2 ↦ false, ()) 1 := by
  simp [shortChoice, DSubInstrument.branch_classical_basis]

/-- The zero-weight long branch rejects a point budget exceeding the live path's cost three. -/
example
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) :
    ¬ (adaptive shortChoice q).IsPointBound 4 := by
  rw [adaptive_point_iff]
  omega

/-- A width cap fitting the live branch still fails on the zero-weight width-three branch. -/
example
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) :
    ¬ (adaptive shortChoice q).IsWidthBound 2 := by
  rw [adaptive_width_iff]
  omega

/-- Zero-weight branches still count their oracle rounds. -/
example : ¬ (adaptive DSubInstrument.fail (fun _ ↦ SubInstrument.fail)).IsTotalQueryBound 1 := by
  rw [adaptive_round_iff]
  omega

/-- The exact path budget five survives translation, rather than being rounded up to six. -/
example
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) :
    ((adaptive p q).sequentialize .instruments).IsTotalQueryBound 5 :=
  ((adaptive_point_iff p q 5).mpr (by omega)).sequentialize .instruments

/-- A round bound and a width cap independently recover the general product budget. -/
example
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) :
    ((adaptive p q).sequentialize .instruments).IsTotalQueryBound (3 * 2) :=
  ((adaptive_round_iff p q 2).mpr (by omega)).isPointBound
    ((adaptive_width_iff p q 3).mpr (by omega)) |>.sequentialize .instruments

/-- A named local operation flips the spectator qubit. -/
inductive Gate : QReg → Type
  | flipSpectator : Gate (QReg.of ((Fin 2 → Bool) × Bool))

/-- A one-gate signature with a classical unit outcome. -/
@[expose]
def gates : LocalSig where
  Op := Gate
  Outcome _ := Unit
  next {A} _ _ := A

/-- The spectator flip leaves the oracle's two input slots unchanged. -/
@[expose]
noncomputable def gateInterp : gates.Interp := fun _ g ↦ match g with
  | .flipSpectator => SubInstrument.relabel
      ((Equiv.refl (Fin 2 → Bool)).prodCongr Equiv.boolNot)

/-- A named local gate precedes a stateful two-slot batch. -/
noncomputable def namedBatch :
    QuantumComp gates (uBatchSpec Unit fun _ ↦ QReg.of Bool)
      (fun _ ↦ Unit) (QReg.of ((Fin 2 → Bool) × Bool)) :=
  QuantumComp.primBind .flipSpectator fun _ ↦
    QuantumComp.queryBind ((), 2) (QReg.of Bool) (Equiv.refl _)
      fun _ ↦ QuantumComp.pure ()

/-- Named operations are interpreted explicitly while the translated call budget stays two. -/
example : (namedBatch.sequentialize gateInterp).IsTotalQueryBound 2 := by
  apply QuantumComp.IsPointBound.sequentialize
  simp [namedBatch, gates]

/-- A private qubit exchanged with each public slot makes call order observable. -/
@[expose, reducible]
noncomputable def swapRuntime : QuantumRuntime (uSpec Unit fun _ ↦ QReg.of Bool) where
  D := QReg.of Bool
  init := SubState.basis false
  step _ := SubInstrument.relabel (Equiv.prodComm Bool Bool)

/-- Two slots share the same private qubit and retain a public spectator qubit. -/
noncomputable def statefulBatch :
    QComp (uBatchSpec Unit fun _ ↦ QReg.of Bool)
      (QReg.of ((Fin 2 → Bool) × Bool)) (QReg.of ((Fin 2 → Bool) × Bool)) Unit :=
  QuantumComp₂.query (spec := uBatchSpec Unit fun _ ↦ QReg.of Bool) ((), 2)
    (QReg.of Bool) (Equiv.refl _)

/-- Increasing slot order leaves the final slot's value in the private register. -/
theorem swap_batch_branch :
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

/-- The caller's spectator qubit survives the stateful batch unchanged. -/
theorem run_statefulBatch_branch :
    (swapRuntime.batch.run₂ .instruments statefulBatch).branch ()
        (Matrix.single ((fun i : Fin 2 ↦ i == 1, true), false)
          ((fun i : Fin 2 ↦ i == 1, true), false) 1) =
      Matrix.single ((fun _ : Fin 2 ↦ false, true), true)
        ((fun _ : Fin 2 ↦ false, true), true) 1 := by
  rw [statefulBatch, QuantumRuntime.run₂_query, SubInstrument.bind_pure]
  have h := swapRuntime.batch.queryStep_branch_single
    (A := QReg.of ((Fin 2 → Bool) × Bool)) ((), 2) (QReg.of Bool)
    (Equiv.refl ((Fin 2 → Bool) × Bool)) () (fun i : Fin 2 ↦ i == 1, true) false
  refine h.trans ?_
  change (SubInstrument.relabel (QuantumRuntime.queryEquivOut (Fin 2 → Bool) Bool Bool)).branch ()
    ((SubInstrument.batch (QReg.of Bool) (QReg.of Bool)
      (SubInstrument.relabel (Equiv.prodComm Bool Bool)) 2).branch ()
      (Matrix.single (fun i : Fin 2 ↦ i == 1, false) (fun i : Fin 2 ↦ i == 1, false) 1) ⊗ₖ
      Matrix.single true true 1) = _
  rw [swap_batch_branch, Matrix.single_kronecker_single, one_mul,
    SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
    QuantumRuntime.queryEquivOut_apply]

/-- Zero-width translation keeps the nontrivial remainder relabelling and all private memory. -/
example (R : QuantumRuntime (uSpec Unit fun _ ↦ QReg.of Bool)) (b : Bool) (d : R.D) :
    (R.run .instruments (zeroWidth.sequentialize .instruments)).branch
        ⟨QReg.of ((Fin 0 → Bool) × Bool), ()⟩ (Matrix.single (b, d) (b, d) 1) =
      Matrix.single ((default, !b), d) ((default, !b), d) 1 := by
  rw [QuantumRuntime.run_sequentialize]
  exact run_zeroWidth_branch R b d

/-- The named translation implements increasing order through shared private memory. -/
example :
    (swapRuntime.run .instruments (statefulBatch.sequentialize .instruments)).branch
        ⟨QReg.of ((Fin 2 → Bool) × Bool), rfl, ()⟩
        (Matrix.single ((fun i : Fin 2 ↦ i == 1, true), false)
          ((fun i : Fin 2 ↦ i == 1, true), false) 1) =
      Matrix.single ((fun _ : Fin 2 ↦ false, true), true)
        ((fun _ : Fin 2 ↦ false, true), true) 1 := by
  have h := swapRuntime.run_sequentialize .instruments statefulBatch
  exact (congrArg (fun J ↦ J.branch ⟨QReg.of ((Fin 2 → Bool) × Bool), rfl, ()⟩
    (Matrix.single ((fun i : Fin 2 ↦ i == 1, true), false)
      ((fun i : Fin 2 ↦ i == 1, true), false) 1)) h).trans run_statefulBatch_branch

/-- All adaptive local branches and changed register sizes preserve the complete operator
semantics for arbitrary stateful, possibly lossy runtimes. -/
example (R : QuantumRuntime (uSpec Unit fun _ ↦ QReg.of Bool))
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit) :
    R.run .instruments ((adaptive p q).sequentialize .instruments) =
      R.batch.run .instruments (adaptive p q) :=
  R.run_sequentialize .instruments (adaptive p q)

/-- Named local gates use their supplied interpretation under every stateful runtime. -/
example (R : QuantumRuntime (uSpec Unit fun _ ↦ QReg.of Bool)) :
    R.run .instruments (namedBatch.sequentialize gateInterp) = R.batch.run gateInterp namedBatch :=
  R.run_sequentialize gateInterp namedBatch

/-- Joint observations also preserve the full adaptive program's output law. -/
example (R : QuantumRuntime (uSpec Unit fun _ ↦ QReg.of Bool))
    (p : DSubInstrument Unit Bool fun b ↦ (Fin (if b then 2 else 3) → Bool) × Unit)
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 2 else 3) → Bool) × Unit)
        ((Fin (if b then 1 else 2) → Bool) × Bool) PUnit)
    [MeasurableSpace (Σ _ : QReg, Unit)] (ρ : SubState Unit) :
    R.evalDist .instruments ((adaptive p q).sequentialize .instruments) ρ =
      R.batch.evalDist .instruments (adaptive p q) ρ :=
  R.evalDist_sequentialize .instruments (adaptive p q) ρ

/-- The actual QROM signature permits two repeated inputs from a singleton domain. -/
noncomputable def qromCall :
    QuantumComp LocalSig.instruments (qromBatchSpec Unit (ZMod 3))
      (fun _ ↦ Unit) (QReg.of ((Fin 2 → Unit × ZMod 3) × Bool)) :=
  QuantumComp.queryBind ((), 2) (QReg.of Bool) (Equiv.refl _)
    fun _ ↦ QuantumComp.pure ()

/-- Coherent operators, including off-diagonal correlations with the public spectator, are
preserved on the actual QROM interface with repeated inputs and width above domain size. -/
example (H : Unit → ZMod 3)
    (ρ : Matrix (((Fin 2 → Unit × ZMod 3) × Bool) × Unit)
      (((Fin 2 → Unit × ZMod 3) × Bool) × Unit) ℂ) :
    ((additiveOracleRuntime H).run .instruments (qromCall.sequentialize .instruments)).branch
        ⟨QReg.of ((Fin 2 → Unit × ZMod 3) × Bool), ()⟩ ρ =
      ((parallelOracleRuntime H).queryStep
        (A := QReg.of ((Fin 2 → Unit × ZMod 3) × Bool)) ((), 2)
        (QReg.of Bool) (Equiv.refl _)).branch () ρ := by
  rw [QuantumRuntime.run_sequentialize]
  change ((parallelOracleRuntime H).run .instruments qromCall).branch _ ρ = _
  rw [qromCall, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_unit]
  simp only [QuantumRuntime.run_pure, DSubInstrument.branch_ret_self, LinearMap.id_comp]

/-- Measure both repeated-input responses after a batch, retaining the spectator register. -/
noncomputable def qromObserve :
    QuantumComp LocalSig.instruments (qromBatchSpec Unit (ZMod 3))
      (fun _ ↦ ZMod 3 × ZMod 3) (QReg.of ((Fin 2 → Unit × ZMod 3) × Bool)) :=
  QuantumComp.queryBind ((), 2) (QReg.of Bool) (Equiv.refl _) fun _ ↦
    QuantumComp.primBind
      ⟨ZMod 3 × ZMod 3, fun _ ↦ QReg.of ((Fin 2 → Unit × ZMod 3) × Bool),
        DSubInstrument.classical (fun a ↦ ((a.1 0).2, (a.1 1).2)) id⟩
      fun r ↦ QuantumComp.pure r

/-- Sequential QROM queries retain the correlation between the sampled function and both
measured repeated-input responses, with one function shared by the entire execution. -/
example (ρ : SubState ((Fin 2 → Unit × ZMod 3) × Bool))
    [MeasurableSpace (ZMod 3 × (ZMod 3 × ZMod 3))] :
    qromEvalDistMap .instruments (qromObserve.sequentialize .instruments) ρ
        (fun H out ↦ (H (), out.2)) =
      sampledEvalDistMap parallelOracleRuntime .instruments qromObserve ρ
        (fun H out ↦ (H (), out.2)) :=
  qromEvalDistMap_sequentialize .instruments qromObserve ρ (fun H out ↦ (H (), out.2))

/-- The measured repeated-input QROM program fits the two-call sequential query budget. -/
example : (qromObserve.sequentialize .instruments).IsQueryBound (fun _ ↦ 2) := by
  apply QuantumComp.IsPointBound.qrom_sequentialize
  simp [qromObserve]

/-- A bound covering all two-query sequential programs transfers to the concrete two-slot
program, with an event comparing the returned responses to the sampled function. -/
example (ρ : SubState ((Fin 2 → Unit × ZMod 3) × Bool)) (ε : ENNReal)
    (h : ∀ z : QuantumComp LocalSig.instruments.{0} (qromSpec Unit (ZMod 3))
      (fun _ ↦ ZMod 3 × ZMod 3) (QReg.of ((Fin 2 → Unit × ZMod 3) × Bool)),
      z.IsQueryBound (fun _ ↦ 2) → qromEvalDistMap .instruments z ρ
        (fun H out ↦ out.2 = (H (), H ())) {True} ≤ ε) :
    qromBatchEvalDistMap .instruments qromObserve ρ
      (fun H out ↦ out.2 = (H (), H ())) {True} ≤ ε := by
  apply qromBatchEvalDistMap_le_of_sequential_bound .instruments qromObserve ρ _ _ _ ε h
  simp [qromObserve]

/-- Generic local-step budget lemmas support large classical outcomes and large port types. -/
example (p : SubInstrument Unit Unit (ULift.{1} Unit))
    (k : ULift.{1} Unit → QComp
      (uBatchSpec (ULift.{1} Unit) fun _ ↦ QReg.of Unit)
      (QReg.of Unit) (QReg.of Unit) (ULift.{1} Unit)) (n : ℕ) :
    let x := (QComp.act (A := QReg.of Unit) p).bind k
    x.IsTotalQueryBound n ∧ x.IsPointBound n ↔
      (∀ b, (k b).IsTotalQueryBound n) ∧ ∀ b, (k b).IsPointBound n := by
  dsimp only
  rw [QComp.isTotalQueryBound_act_bind_iff, QComp.isPointBound_act_bind_iff]

/-- Fixed-register query budgets also support outcome and base-port universes above `Type`. -/
example (k : Unit → QuantumComp₂ LocalSig.instruments.{1}
    (uBatchSpec (ULift.{1} Unit) fun _ ↦ QReg.of Unit)
    (QReg.of ((Fin 1 → Unit) × Unit)) (QReg.of Unit) (ULift.{1} Unit)) (n : ℕ) :
    let x := (QuantumComp₂.query (L := LocalSig.instruments.{1})
      (spec := uBatchSpec (ULift.{1} Unit) fun _ ↦ QReg.of Unit)
      (A := QReg.of ((Fin 1 → Unit) × Unit)) (ULift.up (), 1)
      (QReg.of Unit) (Equiv.refl _)).bind k
    x.IsTotalQueryBound n ∧ x.IsPointBound n ↔
      (0 < n ∧ ∀ r, (k r).IsTotalQueryBound (n - 1)) ∧
        1 ≤ n ∧ ∀ r, (k r).IsPointBound (n - 1) := by
  dsimp only
  rw [QuantumComp₂.isTotalQueryBound_query_bind_iff, QuantumComp₂.isPointBound_query_bind_iff]

end VCVioTest.QuantumSequentialize
