/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.DropEmptyBatches
public import VCVio.Quantum.Oracle.MaskedChain.Preprocessing.Model

/-!
# Removing empty masked-chain preprocessing rounds

Zero-width calls are identities for the fixed-function parallel oracle. Removing them from
preprocessing preserves the complete preprocessing/online run and its endpoint recovery law.
The retained register, classical state and online family are unchanged. Every remaining call
spends at least one point, so a preprocessing point budget bounds the normalized round count,
without restricting how many empty rounds the original program contains.
-/

public section

open Matrix MeasureTheory
open scoped ENNReal

namespace Quantum.MaskedChain

variable {G : Type} [Fintype G] [DecidableEq G]

/-- Remove empty preprocessing calls while retaining all adversary data and online programs. -/
@[expose]
noncomputable def dropEmptyPreprocessing {q : ℕ} (adv : PreprocessingAdversary G q) :
    PreprocessingAdversary G q :=
  { adv with preprocess := adv.preprocess.dropEmptyBatches .instruments }

/-- The normalized preprocessing retains the original point budget. -/
theorem isPointBound_dropEmptyPreprocessing {q Q : ℕ} (adv : PreprocessingAdversary G q)
    (hQ : adv.preprocess.IsPointBound Q) :
    (dropEmptyPreprocessing adv).preprocess.IsPointBound Q :=
  hQ.dropEmptyBatches .instruments

/-- Every retained preprocessing call spends a point, even if the original round count is
unbounded across branches. -/
theorem isTotalQueryBound_dropEmptyPreprocessing_of_isPointBound {q Q : ℕ}
    (adv : PreprocessingAdversary G q) (hQ : adv.preprocess.IsPointBound Q) :
    (dropEmptyPreprocessing adv).preprocess.IsTotalQueryBound Q :=
  hQ.isTotalQueryBound_dropEmptyBatches .instruments

/-- Removing empty calls also retains any existing preprocessing round bound. -/
theorem isTotalQueryBound_dropEmptyPreprocessing {q r : ℕ}
    (adv : PreprocessingAdversary G q) (hr : adv.preprocess.IsTotalQueryBound r) :
    (dropEmptyPreprocessing adv).preprocess.IsTotalQueryBound r :=
  hr.dropEmptyBatches .instruments

variable [AddCommGroup G]

/-- Empty-round removal preserves the full fixed-function run, including the private oracle
register shared between preprocessing and online execution. -/
theorem run_preprocessedRecoveryProgram_dropEmptyPreprocessing {q : ℕ}
    (H : G → G) (adv : PreprocessingAdversary G q) (puzzle : Puzzle G q) :
    (parallelOracleRuntime H).run .instruments
        (preprocessedRecoveryProgram (dropEmptyPreprocessing adv) puzzle) =
      (parallelOracleRuntime H).run .instruments
        (preprocessedRecoveryProgram adv puzzle) := by
  simp only [preprocessedRecoveryProgram, dropEmptyPreprocessing, QuantumRuntime.run_bind]
  rw [(parallelOracleRuntime H).run_dropEmptyBatches .instruments
    (fun _ ↦ parallelOracleRuntime_step_zero H)]

/-- Normalization preserves actual endpoint success under one oracle and one hidden tuple.
It does not postselect or reinitialize either phase. -/
theorem preprocessedRecoveryAdvantage_dropEmptyPreprocessing_eq {q : ℕ}
    (adv : PreprocessingAdversary G q) :
    preprocessedRecoveryAdvantage (dropEmptyPreprocessing adv) =
      preprocessedRecoveryAdvantage adv := by
  rw [preprocessedRecoveryAdvantage_eq_sum, preprocessedRecoveryAdvantage_eq_sum]
  apply Finset.sum_congr rfl
  intro H _
  congr 1
  apply Finset.sum_congr rfl
  intro vertices _
  congr 1
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost]
  rw [run_preprocessedRecoveryProgram_dropEmptyPreprocessing]
  rfl

end Quantum.MaskedChain
