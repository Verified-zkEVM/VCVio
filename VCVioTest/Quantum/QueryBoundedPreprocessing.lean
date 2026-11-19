/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.MaskedChainPuzzle.Preprocessing
public import VCVio.Quantum.Oracle.MaskedChain.Preprocessing
public import Mathlib.Data.ZMod.Basic

/-!
# Query-bounded preprocessing regressions

Reading a complete two-point oracle before receiving a one-link puzzle permits recovery with
no online calls. This checks that the endpoint game retains actual oracle-dependent advice
and uses the same oracle for preprocessing and honest generation.
-/

public section

open Quantum Quantum.MaskedChain Quantum.TimeLockPuzzle OracleComp OracleSpec MeasureTheory Matrix
open scoped ENNReal ComplexOrder

namespace VCVioTest.QuantumQueryBoundedPreprocessing

/-- Read the complete two-point domain in one parallel round. -/
@[expose, reducible]
def readTable : MaskedChainPuzzle.RoundComp (ZMod 2) (ZMod 2 → ZMod 2) := do
  let answers ← queryRound (fun i : Fin 2 ↦ (i.val : ZMod 2))
  pure (fun x ↦ answers ⟨x.val, x.val_lt⟩)

private theorem simulateQ_readTable (H : ZMod 2 → ZMod 2) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' readTable = pure H := by
  simp [readTable, simulateQ_queryRound, Id.run]

/-- The preprocessing state contains the oracle table; the online program only unmasks a link. -/
@[expose, reducible]
noncomputable def tableAdversary : PreprocessingAdversary (ZMod 2) 0 where
  initialReg := QReg.of Unit
  initialState := SubState.basis ()
  State := QuantumComp₂.Leaf (QReg.of Unit) (ZMod 2 → ZMod 2)
  preprocess := readTable.toQuantumBatch
  online M state puzzle := by
    rcases state with ⟨h, table⟩
    subst M
    exact QuantumComp.pure (puzzle.2 0 - table puzzle.1)

/-- Reading the table spends one preprocessing round and two points, with no online resources. -/
example : tableAdversary.IsQueryBound ⟨1, 2, 0, 0, 0⟩ := by
  have hc : IsOnlineQueryBound readTable (1, 2) :=
    isOnlineQueryBound_bind
      (isOnlineQueryBound_queryRound (fun i : Fin 2 ↦ (i.val : ZMod 2)))
      (fun answers ↦ isOnlineQueryBound_pure (fun x : ZMod 2 ↦ answers ⟨x.val, x.val_lt⟩) (0, 0))
  refine ⟨hc.isTotalQueryBound_toQuantumBatch, hc.isPointBound_toQuantumBatch, ?_⟩
  intro M state puzzle
  rcases state with ⟨h, table⟩
  subst M
  simp

private theorem run_preprocess (H : ZMod 2 → ZMod 2) :
    (parallelOracleRuntime H).run .instruments tableAdversary.preprocess =
      DSubInstrument.ret (fun leaf : Σ M, tableAdversary.State M ↦
        leaf.1 × (parallelOracleRuntime H).D) ⟨QReg.of Unit, rfl, H⟩ := by
  apply DSubInstrument.ext
  funext leaf
  rcases leaf with ⟨M, h, table⟩
  cases h
  change ((parallelOracleRuntime H).run₂ .instruments readTable.toQuantumBatch).branch table = _
  rw [run_toQuantumBatch, simulateQ_readTable, OracleComp.toQuantumAt_pure,
    QuantumRuntime.run₂_pure]
  by_cases h : table = H
  · subst table
    rw [SubInstrument.branch_pure_self, DSubInstrument.branch_ret_self]
  · rw [SubInstrument.branch_pure_of_ne h]
    exact (DSubInstrument.branch_ret_of_ne
      (fun leaf : Σ M, tableAdversary.State M ↦ leaf.1 × (parallelOracleRuntime H).D)
      (i := ⟨QReg.of Unit, rfl, H⟩) (j := ⟨QReg.of Unit, rfl, table⟩)
      (by intro he; exact h (congrArg (fun leaf ↦ leaf.2.2) he))).symm

/-- The online execution uses the retained table, with no new oracle call. -/
example (M : QReg) (state : tableAdversary.State M) (puzzle : Puzzle (ZMod 2) 0) :
    (tableAdversary.online M state puzzle).IsTotalQueryBound 0 := by
  rcases state with ⟨h, table⟩
  subst M
  simp

/-- Under every fixed oracle and vertex tuple, the complete execution returns the endpoint. -/
private theorem run_endpoint (H : ZMod 2 → ZMod 2) (vertices : Fin 2 → ZMod 2) :
    (parallelOracleRuntime H).run .instruments
      (preprocessedRecoveryProgram tableAdversary (publicPuzzle H vertices)) =
      DSubInstrument.ret (fun leaf : Σ _B : QReg, ZMod 2 ↦
        leaf.1 × (parallelOracleRuntime H).D) ⟨QReg.of Unit, vertices 1⟩ := by
  rw [preprocessedRecoveryProgram, QuantumRuntime.run_bind, run_preprocess,
    DSubInstrument.ret_bind]
  change (parallelOracleRuntime H).run .instruments
    (QuantumComp.pure (X := fun _ : QReg ↦ ZMod 2) (A := QReg.of Unit)
      ((H (vertices 0) + vertices 1) - H (vertices 0))) = _
  simp [QuantumRuntime.run_pure]

private theorem event_endpoint (ρ : SubState Unit) (H : ZMod 2 → ZMod 2)
    (vertices : Fin 2 → ZMod 2) :
    (parallelOracleRuntime H).evalDistMap .instruments
      (preprocessedRecoveryProgram { tableAdversary with initialState := ρ }
        (publicPuzzle H vertices)) ρ (fun leaf ↦ leaf.2 = vertices 1) {True} = ρ.mass := by
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True),
    tsum_eq_single ⟨QReg.of Unit, vertices 1⟩]
  · simp only [QuantumRuntime.matrix_jointPost]
    change ENNReal.ofReal (((parallelOracleRuntime H).run .instruments
      (preprocessedRecoveryProgram tableAdversary (publicPuzzle H vertices))).branch
        ⟨QReg.of Unit, vertices 1⟩ (ρ.prod (SubState.basis ())).matrix).trace.re * _ = _
    rw [run_endpoint, DSubInstrument.branch_ret_self]
    change ENNReal.ofReal (ρ.prod (SubState.basis ())).matrix.trace.re *
      ({True} : Set Prop).indicator 1 True = _
    rw [SubState.trace_re_prod, SubState.trace_basis]
    simp [SubState.mass]
  · intro leaf hleaf
    simp only [QuantumRuntime.matrix_jointPost]
    change ENNReal.ofReal (((parallelOracleRuntime H).run .instruments
      (preprocessedRecoveryProgram tableAdversary (publicPuzzle H vertices))).branch
        leaf (ρ.prod (SubState.basis ())).matrix).trace.re * _ = 0
    rw [run_endpoint, DSubInstrument.branch_ret_of_ne _ hleaf]
    change ENNReal.ofReal (0 : Matrix (leaf.1 × Unit) (leaf.1 × Unit) ℂ).trace.re *
      ({True} : Set Prop).indicator 1 (leaf.2 = vertices 1) = 0
    simp

/-- Complete oracle advice yields the full original input mass, even with zero online calls. -/
theorem recovery_with_table (ρ : SubState Unit) :
    preprocessedRecoveryAdvantage { tableAdversary with initialState := ρ } = ρ.mass := by
  rw [preprocessedRecoveryAdvantage_eq_sum]
  change (∑ H : ZMod 2 → ZMod 2, (Fintype.card (ZMod 2 → ZMod 2) : ℝ≥0∞)⁻¹ *
    ∑ vertices : Fin 2 → ZMod 2, (Fintype.card (Fin 2 → ZMod 2) : ℝ≥0∞)⁻¹ *
      (parallelOracleRuntime H).evalDistMap .instruments
        (preprocessedRecoveryProgram { tableAdversary with initialState := ρ }
          (publicPuzzle H vertices)) ρ (fun leaf ↦ leaf.2 = vertices 1) {True}) = _
  trans ∑ _H : ZMod 2 → ZMod 2, (Fintype.card (ZMod 2 → ZMod 2) : ℝ≥0∞)⁻¹ *
      ∑ _vertices : Fin 2 → ZMod 2,
        (Fintype.card (Fin 2 → ZMod 2) : ℝ≥0∞)⁻¹ * ρ.mass
  · apply Finset.sum_congr rfl
    intro H _
    apply congrArg
    apply Finset.sum_congr rfl
    intro vertices _
    exact congrArg _ (event_endpoint ρ H vertices)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), one_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), one_mul]

/-- The actual three-phase scheme shares the preprocessing oracle and keeps its advice. -/
example : Quantum.TimeLockPuzzle.qromDelayAdvantage
    (MaskedChainPuzzle.scheme 0) tableAdversary = 1 := by
  rw [MaskedChainPuzzle.qromDelayAdvantage_eq_preprocessedRecoveryAdvantage]
  convert recovery_with_table (SubState.basis ()) using 1
  simp [SubState.mass]

/-- Missing input mass remains failure even when the table advice determines the endpoint. -/
noncomputable def halfInput : SubState Unit where
  matrix := Matrix.diagonal fun _ ↦ (1 / 2 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro u; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag]

/-- Actual preprocessing and honest generation do not renormalize a half-mass input. -/
example : Quantum.TimeLockPuzzle.qromDelayAdvantage (MaskedChainPuzzle.scheme 0)
    { tableAdversary with initialState := halfInput } = 1 / 2 := by
  rw [MaskedChainPuzzle.qromDelayAdvantage_eq_preprocessedRecoveryAdvantage,
    recovery_with_table]
  norm_num [halfInput, SubState.mass, Matrix.trace, Matrix.diag, ENNReal.ofReal_div_of_pos]

/-- A real two-phase adversary may spend a preprocessing round without spending a point. -/
@[expose, reducible]
noncomputable def emptyAdversary : PreprocessingAdversary (ZMod 3) 0 where
  initialReg := QReg.of Unit
  initialState := SubState.basis ()
  State M := PLift (M = QReg.of ((Fin 0 → ZMod 3 × ZMod 3) × Unit))
  preprocess := QuantumComp.queryBind ((), 0) (QReg.of Unit)
    (Equiv.uniqueProd Unit (Fin 0 → ZMod 3 × ZMod 3)).symm fun _ ↦ QuantumComp.pure ⟨rfl⟩
  online M state _ := by
    rcases state with ⟨h⟩
    subst M
    exact QuantumComp.pure 0

/-- Preprocessing rounds and points are separate admissibility conditions. -/
example : emptyAdversary.IsQueryBound ⟨1, 0, 0, 0, 0⟩ ∧
    ¬ emptyAdversary.IsQueryBound ⟨0, 0, 0, 0, 0⟩ := by
  constructor
  · refine ⟨by simp [emptyAdversary], by simp [emptyAdversary], ?_⟩
    intro M state puzzle
    rcases state with ⟨h⟩
    subst M
    simp
  · intro h
    simpa [emptyAdversary] using h.1

/-- Empty-round removal gives zero preprocessing rounds despite the original positive clock. -/
example : (dropEmptyPreprocessing emptyAdversary).preprocess.IsTotalQueryBound 0 :=
  isTotalQueryBound_dropEmptyPreprocessing_of_isPointBound emptyAdversary
    (by simp [emptyAdversary])

/-- Erasing a real preprocessing call preserves the actual three-phase scheme experiment. -/
example : Quantum.TimeLockPuzzle.qromDelayAdvantage (MaskedChainPuzzle.scheme 0)
      (dropEmptyPreprocessing emptyAdversary) =
    Quantum.TimeLockPuzzle.qromDelayAdvantage (MaskedChainPuzzle.scheme 0) emptyAdversary := by
  rw [MaskedChainPuzzle.qromDelayAdvantage_eq_preprocessedRecoveryAdvantage,
    MaskedChainPuzzle.qromDelayAdvantage_eq_preprocessedRecoveryAdvantage,
    preprocessedRecoveryAdvantage_dropEmptyPreprocessing_eq]

end VCVioTest.QuantumQueryBoundedPreprocessing
