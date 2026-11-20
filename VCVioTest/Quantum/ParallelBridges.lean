/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.Compressed.Parallel
public import VCVio.Quantum.Oracle.ClassicalParallel
public import VCVio.Quantum.Comp.RoundBound
public import Mathlib.Data.ZMod.Basic

/-!
# Parallel classical and compressed bridge regressions

Ordered repeated-input tuples, adaptive batch widths, subnormalized inputs, and the distinction
between compression isometries and non-trace-preserving function-register projections.
-/

public section

open Quantum Matrix MeasureTheory OracleSpec OracleComp
open scoped Kronecker ComplexOrder ENNReal

namespace VCVioTest.QuantumParallelBridges

/-- A successful input mass of one half, without renormalization. -/
noncomputable def halfState : SubState Unit where
  matrix := (1 / 2 : ℝ) • (SubState.basis ()).matrix
  posSemidef := (SubState.basis ()).posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  trace_re_le_one := by norm_num

/-- The input is strictly subnormalized. -/
example : halfState.matrix.trace.re = 1 / 2 := by simp [halfState]

/-- A rank-two classical mixture of total mass one half. -/
noncomputable def mixedBool : SubState Bool where
  matrix := Matrix.diagonal fun _ ↦ (1 / 4 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro b; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag, Fintype.sum_bool]

/-- Both spectator alternatives have positive mass and no off-diagonal coherence. -/
example : mixedBool.matrix false false = 1 / 4 ∧ mixedBool.matrix true true = 1 / 4 ∧
    mixedBool.matrix false true = 0 ∧ mixedBool.matrix.trace.re = 1 / 2 := by
  norm_num [mixedBool, Matrix.trace, Matrix.diag, Fintype.sum_bool]

/-- Prepare two repeated-input slots while retaining a Boolean spectator. -/
noncomputable def spectatorBatch :
    QuantumComp LocalSig.instruments (qromBatchSpec Unit (ZMod 3))
      (fun _ ↦ Unit) (QReg.of Bool) :=
  QuantumComp.primBind
    ⟨Unit, fun _ ↦ QReg.of ((Fin 2 → Unit × ZMod 3) × Bool),
      DSubInstrument.classical (fun _ : Bool ↦ ()) (fun b ↦ (fun _ ↦ ((), 0), b))⟩
    fun _ ↦ QuantumComp.queryBind ((), 2) (QReg.of Bool) (Equiv.refl _)
      fun _ ↦ QuantumComp.pure ()

/-- A genuine mixture with missing input mass obeys the exact compressed parallel law. -/
example :
    (compressedRuntime Unit (ZMod 3)).batch.evalDistMap .instruments
      spectatorBatch mixedBool (fun _ ↦ ()) =
      sampledEvalDistMap parallelOracleRuntime .instruments spectatorBatch mixedBool
        (fun _ _ ↦ ()) :=
  outcomeLawWith_compressedRuntime_batch .instruments spectatorBatch mixedBool _

/-- Discarding private memory preserves both alternatives of the mixed spectator. -/
example (out : Σ _ : QReg, Unit) :
    (compressedRuntime Unit (ZMod 3)).batch.reducedPost .instruments spectatorBatch mixedBool out =
      (purifiedRuntime Unit (ZMod 3)).batch.reducedPost .instruments spectatorBatch mixedBool out :=
  reducedPost_compressedRuntime_batch .instruments spectatorBatch mixedBool out

/-! ## Compression and purification -/

/-- A single function-register row discards every other function and is not a channel. -/
example : ¬ (MatrixMap.conj (evalRow (fun _ : Unit ↦ (0 : ZMod 3)))).IsTP := by
  intro h
  have ht := h (Matrix.single (fun _ : Unit ↦ (1 : ZMod 3))
    (fun _ : Unit ↦ (1 : ZMod 3)) 1)
  have hne : (fun _ : Unit ↦ (1 : ZMod 3)) ≠ (fun _ : Unit ↦ 0) := by decide
  norm_num [MatrixMap.conj_apply, Matrix.mul_apply, evalRow, Matrix.trace,
    Matrix.diag, Matrix.single_apply, hne] at ht

/-- The private compression column has an empty-cell amplitude and a negative off-diagonal
entry; it is not a classical copy of the function value. -/
example :
    (compressAll Unit (ZMod 3) *
      basisMatrix (Database.ofFun : (Unit → ZMod 3) → Database Unit (ZMod 3)))
        (fun _ ↦ some 1) (fun _ ↦ 0) = -(3 : ℂ)⁻¹ := by
  rw [mul_basisMatrix_apply]
  norm_num [compressAll, piKron_apply]

/-- The full compression map preserves trace, including off-diagonal matrices. -/
example (ρ : Matrix (Bool → ZMod 5) (Bool → ZMod 5) ℂ) :
    (MatrixMap.conj (compressAll Bool (ZMod 5) *
      basisMatrix (Database.ofFun : (Bool → ZMod 5) → Database Bool (ZMod 5))) ρ).trace =
      ρ.trace :=
  MatrixMap.isTP_conj conjTranspose_compressAll_mul_basisMatrix_mul_self ρ

/-- Two rounds have widths selected by a local classical outcome, with a larger-than-domain
width on one branch and a zero-width call on the other. -/
noncomputable def adaptive
    (p : DSubInstrument Unit Bool
      (fun b ↦ (Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit))
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit)
        ((Fin (if b then 1 else 2) → Fin 3 × ZMod 5) × Bool) PUnit) :
    QuantumComp LocalSig.instruments (qromBatchSpec (Fin 3) (ZMod 5))
      (fun _ ↦ Bool) (QReg.of Unit) :=
  QuantumComp.primBind
    ⟨Bool, fun b ↦ QReg.of ((Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit), p⟩
    fun b ↦ QuantumComp.queryBind ((), if b then 4 else 0) (QReg.of Unit)
      (Equiv.refl _) fun _ ↦ QuantumComp.primBind
        ⟨PUnit, fun _ ↦ QReg.of ((Fin (if b then 1 else 2) → Fin 3 × ZMod 5) × Bool), q b⟩
        fun _ ↦ QuantumComp.queryBind ((), if b then 1 else 2) (QReg.of Bool)
          (Equiv.refl _) fun _ ↦ QuantumComp.pure b

/-- Both adaptive branches have two calls, even when the first call has width zero. -/
example
    (p : DSubInstrument Unit Bool
      (fun b ↦ (Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit))
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit)
        ((Fin (if b then 1 else 2) → Fin 3 × ZMod 5) × Bool) PUnit) :
    (adaptive p q).IsTotalQueryBound 2 ∧ (adaptive p q).IsPointBound 5 := by
  constructor <;> simp [adaptive, LocalSig.InstrumentOp.Outcome, Bool.forall_bool]

/-- Complete private post-states are related by compression, for arbitrary substates. -/
example
    (p : DSubInstrument Unit Bool
      (fun b ↦ (Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit))
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit)
        ((Fin (if b then 1 else 2) → Fin 3 × ZMod 5) × Bool) PUnit)
    (ρ : SubState Unit) (out : Σ _ : QReg, Bool) :
    (((compressedRuntime (Fin 3) (ZMod 5)).batch.jointPost .instruments
      (adaptive p q) ρ out).matrix) =
      (MatrixMap.conj (compressAll (Fin 3) (ZMod 5) *
        basisMatrix (Database.ofFun : (Fin 3 → ZMod 5) → Database (Fin 3) (ZMod 5)))).amplifyLeft
          out.1 (((purifiedRuntime (Fin 3) (ZMod 5)).batch.jointPost .instruments
            (adaptive p q) ρ out).matrix) :=
  matrix_jointPost_compressedRuntime_batch .instruments (adaptive p q) ρ out

/-- The observation is a function of the program's classical leaf, with no access to the
sampled function or compressed database. Local operations may themselves lose trace. -/
example
    (p : DSubInstrument Unit Bool
      (fun b ↦ (Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit))
    (q : ∀ b : Bool,
      SubInstrument ((Fin (if b then 4 else 0) → Fin 3 × ZMod 5) × Unit)
        ((Fin (if b then 1 else 2) → Fin 3 × ZMod 5) × Bool) PUnit)
    (ρ : SubState Unit) :
    (compressedRuntime (Fin 3) (ZMod 5)).batch.evalDistMap .instruments
      (adaptive p q) ρ (fun out ↦ out.2) =
      sampledEvalDistMap parallelOracleRuntime .instruments (adaptive p q) ρ
        (fun _ out ↦ out.2) :=
  outcomeLawWith_compressedRuntime_batch .instruments (adaptive p q) ρ _

/-! ## Ordered classical answers -/

/-- A nonbinary table makes the ordering of distinct positions observable. -/
@[expose]
def table (b : Bool) : ZMod 3 := if b then 2 else 1

/-- A genuine three-slot classical batch preserves order and repeated-input correlations. -/
example (d : (parallelOracleRuntime table).D) :
    ((parallelOracleRuntime table).run₂ .instruments
      (classicalBatchQuery [true, false, true])).branch ![2, 1, 2]
        (Matrix.single ((), d) ((), d) 1) = Matrix.single ((), d) ((), d) 1 := by
  rw [run_classicalBatchQuery_branch table _ d]
  split_ifs with h
  · rfl
  · exact False.elim (h (by decide))

/-- A tuple with different answers at repeated positions has zero weight. -/
example (d : (parallelOracleRuntime table).D) :
    ((parallelOracleRuntime table).run₂ .instruments
      (classicalBatchQuery [true, false, true])).branch ![2, 1, 0]
        (Matrix.single ((), d) ((), d) 1) = 0 := by
  rw [run_classicalBatchQuery_branch table _ d]
  split_ifs with h
  · exfalso
    revert h
    decide
  · rfl

/-- The empty round still produces the unique empty tuple with certainty. -/
example (H : Bool → ZMod 3) (d : (parallelOracleRuntime H).D) :
    ((parallelOracleRuntime H).run₂ .instruments
      (classicalBatchQuery ([] : List Bool))).branch (fun j ↦ Fin.elim0 j)
        (Matrix.single ((), d) ((), d) 1) = Matrix.single ((), d) ((), d) 1 := by
  rw [run_classicalBatchQuery_branch H _ d]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    funext j
    exact Fin.elim0 j

/-- Exact compressed equivalence also applies to a half-mass input on an actual measured
three-slot round with repetitions. -/
example :
    (compressedRuntime Bool (ZMod 3)).batch.evalDist₂ .instruments
      (classicalBatchQuery [true, false, true]) halfState =
      sampledEvalDist₂ parallelOracleRuntime .instruments
        (classicalBatchQuery [true, false, true]) halfState := by
  rw [QuantumRuntime.evalDist₂_eq_evalDistMap]
  exact outcomeLawWith_compressedRuntime_batch .instruments _ _ _

/-- A lossless fixed-function round retains the half input mass. -/
example :
    (parallelOracleRuntime table).evalDist₂ .instruments
      (classicalBatchQuery [true, false, true]) halfState Set.univ = 1 / 2 := by
  have hloss : ((parallelOracleRuntime table).run₂ .instruments
      (classicalBatchQuery [true, false, true])).Lossless := by
    rw [run_classicalBatchQuery]
    exact DSubInstrument.lossless_ret _ _
  calc
    _ = ENNReal.ofReal (halfState.matrix.trace.re *
        (parallelOracleRuntime table).init.matrix.trace.re) :=
      (parallelOracleRuntime table).evalDist₂_apply_univ_of_lossless .instruments hloss halfState
    _ = _ := by
      change ENNReal.ofReal (halfState.matrix.trace.re * (SubState.basis ()).matrix.trace.re) = _
      norm_num [halfState, ENNReal.ofReal_div_of_pos]

/-- Two classical rounds compare a repeated slot with a fresh query to the same input. -/
@[expose]
def correlatedRounds : OracleComp (unifSpec + (Bool →ₒ ZMod 3).batch) Bool := do
  let ys ← liftM ((unifSpec + (Bool →ₒ ZMod 3).batch).query (.inr [true, false, true]))
  let zs ← liftM ((unifSpec + (Bool →ₒ ZMod 3).batch).query (.inr [true]))
  pure (ys 0 == ys 2 && ys 0 == zs 0)

/-- A single fixed table makes all three occurrences of `true` agree across both rounds. -/
theorem simulateQ_correlatedRounds (H : Bool → ZMod 3) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' correlatedRounds = pure true := by
  change (pure (H true == H true && H true == H true) : ProbComp Bool) = pure true
  simp

/-- The quantum embedding returns the cross-round equality check with certainty. -/
theorem run_correlatedRounds (H : Bool → ZMod 3) :
    (parallelOracleRuntime H).run₂ .instruments correlatedRounds.toQuantumBatch =
      SubInstrument.pure true := by
  rw [run_toQuantumBatch, simulateQ_correlatedRounds]
  simp

/-- Sampling the function once preserves the correlation across all repeated positions. -/
example :
    sampledEvalDist₂ parallelOracleRuntime .instruments correlatedRounds.toQuantumBatch
      (SubState.basis ()) = Measure.dirac true := by
  have h (H : Bool → ZMod 3) :
      (parallelOracleRuntime H).evalDist₂ .instruments correlatedRounds.toQuantumBatch
        (SubState.basis ()) = Measure.dirac true := by
    rw [QuantumRuntime.evalDist₂, run_correlatedRounds]
    change (SubInstrument.pure true).outcomeMeasure
      ((SubState.basis ()).prod (SubState.basis ())) = _
    simp
  rw [sampledEvalDist₂_eq_sum]
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  norm_num [Fintype.card_fun, ENNReal.inv_mul_cancel]

/-- The complete parallel quantum law agrees with the shared lazy classical cache. -/
example :
    sampledEvalDist₂ parallelOracleRuntime .instruments correlatedRounds.toQuantumBatch
      (SubState.basis ()) =
      𝒟[(simulateQ (unifFwdImpl (Bool →ₒ ZMod 3) + (Bool →ₒ ZMod 3).randomOracle.batch)
        correlatedRounds).run' ∅] :=
  sampledEvalDist₂_toQuantumBatch_eq_randomOracle correlatedRounds

/-- A free local coin chooses between an empty round and a three-slot round. -/
@[expose]
def randomizedWidths : OracleComp (unifSpec + (Bool →ₒ ZMod 3).batch) (Fin 2) := do
  let b : Fin 2 ← liftM ((unifSpec + (Bool →ₒ ZMod 3).batch).query (.inl 1))
  let _ ← liftM ((unifSpec + (Bool →ₒ ZMod 3).batch).query
    (.inr (if b = 0 then [] else [true, false, true])))
  pure b

/-- The round budget charges the empty branch, and the point budget allows the longer branch. -/
theorem online_randomizedWidths : randomizedWidths.IsOnlineQueryBound (1, 3) := by
  simp only [IsOnlineQueryBound, randomizedWidths, Fin.isValue, OracleSpec.add_apply_inr,
    bind_pure_comp, isQueryBound_query_bind_iff, onlineCanQuery_inl, OracleSpec.add_apply_inl,
    onlineCost_inl, isQueryBound_map_iff, isQueryBound_query_iff, onlineCanQuery_inr,
    Order.lt_one_iff, true_and]
  intro b
  split_ifs <;> simp

/-- Local coins retain their classical distribution in the quantum embedding, even when their
outcomes select different query widths. -/
example (H : Bool → ZMod 3) :
    (parallelOracleRuntime H).evalDist₂ .instruments randomizedWidths.toQuantumBatch
      (SubState.basis ()) = 𝒟[(liftM (unifSpec.query 1) : ProbComp (Fin 2))] := by
  rw [evalDist_parallelOracleRuntime_toQuantumBatch]
  congr 1
  simp only [randomizedWidths, simulateQ_bind, simulateQ_spec_query, QueryImpl.batch'_apply_inl,
    QueryImpl.batch'_apply_inr, QueryImpl.batch_unifFwdAnswerImpl]
  change ((liftM (unifSpec.query 1) : ProbComp (Fin 2)) >>= fun b ↦ pure b) = _
  simp

/-- A local uniform draw without any oracle round. -/
@[expose]
def freeCoin : OracleComp (unifSpec + (Bool →ₒ ZMod 3).batch) (Fin 2) :=
  liftM ((unifSpec + (Bool →ₒ ZMod 3).batch).query (.inl 1))

/-- An empty classical round still crosses the oracle interface once. -/
@[expose]
def emptyRound : OracleComp (unifSpec + (Bool →ₒ ZMod 3).batch) Unit := do
  let _ ← liftM ((unifSpec + (Bool →ₒ ZMod 3).batch).query (.inr []))
  pure ()

/-- A free coin embeds with no quantum oracle calls and no charged points. -/
example : freeCoin.toQuantumBatch.IsTotalQueryBound 0 ∧
    freeCoin.toQuantumBatch.IsPointBound 0 := by
  have h : freeCoin.IsOnlineQueryBound (0, 0) := by simp [freeCoin, IsOnlineQueryBound]
  exact ⟨h.isTotalQueryBound_toQuantumBatch, h.isPointQueryBound.isPointBound_toQuantumBatch⟩

/-- Empty rounds consume a quantum round and zero points. -/
example : emptyRound.toQuantumBatch.IsTotalQueryBound 1 ∧
    emptyRound.toQuantumBatch.IsPointBound 0 := by
  have h : emptyRound.IsOnlineQueryBound (1, 0) := by simp [emptyRound, IsOnlineQueryBound]
  exact ⟨h.isTotalQueryBound_toQuantumBatch, h.isPointQueryBound.isPointBound_toQuantumBatch⟩

/-- Zero width does not erase the call from the quantum syntax. -/
example : ¬ emptyRound.toQuantumBatch.IsTotalQueryBound 0 := by
  simp only [emptyRound, toQuantumBatch_query_bind, toQuantumBatch_pure]
  change ¬ ((classicalBatchQuery (Y := ZMod 3) ([] : List Bool)).bind
    (fun _ ↦ QuantumComp₂.pure ())).IsTotalQueryBound 0
  rw [isTotalQueryBound_classicalBatchQuery_bind_iff]
  simp

/-- The randomized width choice retains its classical one-round, three-point budget. -/
example : randomizedWidths.toQuantumBatch.IsTotalQueryBound 1 ∧
    randomizedWidths.toQuantumBatch.IsPointBound 3 :=
  ⟨online_randomizedWidths.isTotalQueryBound_toQuantumBatch,
    online_randomizedWidths.isPointQueryBound.isPointBound_toQuantumBatch⟩

/-- Quantum sequentialization and classical ordered unbatching agree on the adaptive-width
program, with one shared random-oracle cache in both executions. -/
example :
    qromEvalDistMap .instruments (randomizedWidths.toQuantumBatch.sequentialize .instruments)
      (SubState.basis ())
      (fun _ p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) (Fin 2)).symm p) =
      𝒟[(simulateQ (Bool →ₒ ZMod 3).romImpl
        (simulateQ (Bool →ₒ ZMod 3).unbatch randomizedWidths)).run' ∅] :=
  qromEvalDistMap_sequentialize_toQuantumBatch_eq_unbatch randomizedWidths

end VCVioTest.QuantumParallelBridges
