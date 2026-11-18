/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.MaskedChainPuzzle
public import VCVio.Quantum.Oracle.MaskedChain.Preprocessing

/-!
# Quantum preprocessing in the idealized masked-chain puzzle

The actual three-phase puzzle experiment has the same endpoint law as the complete
preprocessing/online program against one uniformly sampled function. Honest generation samples
the hidden tuple between preprocessing and online execution. This exact bridge retains the
preprocessing state, public masks, endpoint and complete tuple, without an independence claim
between the retained advice and the sampled function.

The security theorems bound preprocessing rounds and points, while retaining unrestricted
classical and quantum memory. Empty preprocessing calls are removed before deriving point-only
bounds. `qromDelaySecure` covers every adversary admitted by the stated phase budgets,
including preprocessing states correlated with the sampled oracle. Retained advice is
unrestricted. Auxiliary-input security with unbounded preprocessing and bounded advice is a
separate model.
-/

public section

open Quantum Quantum.MaskedChain MeasureTheory
open scoped ENNReal

namespace MaskedChainPuzzle

variable {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The named puzzle's complete quantum experiment agrees with the preprocessed endpoint game.
No bound is assumed on preprocessing, online queries or retained memory for this equality. -/
theorem qromDelayAdvantage_eq_preprocessedRecoveryAdvantage {q : ℕ}
    (adv : PreprocessingAdversary G q) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (scheme q) adv =
      preprocessedRecoveryAdvantage adv := by
  rw [Quantum.TimeLockPuzzle.qromDelayAdvantage,
    Quantum.TimeLockPuzzle.sampledDelayAdvantage_eq_sum,
    preprocessedRecoveryAdvantage_eq_sum]
  apply Finset.sum_congr rfl
  intro H _
  congr 1
  change Quantum.TimeLockPuzzle.delayAdvantage (parallelOracleRuntime H)
    (Quantum.TimeLockPuzzle.ofClassicalGenerator (gen q) (fun p ↦ (solve p).toQuantumBatch)) adv = _
  rw [Quantum.TimeLockPuzzle.delayAdvantage_ofClassicalGenerator, tsum_gen_mul]
  rfl

/-- Quantum delay with bounded preprocessing rounds and points, and an adaptive online
phase of at most `q` rounds of width at most `k`. Retained memory is unrestricted. -/
theorem qromDelayAdvantage_le_of_preprocessing {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (scheme q) adv ≤
      min 1 (recoveryBound G q k + preprocessingError G q r Q) := by
  rw [qromDelayAdvantage_eq_preprocessedRecoveryAdvantage]
  exact preprocessedRecoveryAdvantage_le adv hr hQ honline

/-- Removing empty preprocessing calls strengthens the effective round budget to the smaller
of the stated round and point bounds, without changing the actual puzzle experiment. -/
theorem qromDelayAdvantage_le_of_preprocessing_min {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (scheme q) adv ≤
      min 1 (recoveryBound G q k + preprocessingError G q (min r Q) Q) := by
  rw [qromDelayAdvantage_eq_preprocessedRecoveryAdvantage]
  exact preprocessedRecoveryAdvantage_le_min adv hr hQ honline

/-- A preprocessing point bound alone suffices for a linear preprocessing error. The original
program may have arbitrarily many zero-width calls across its branches. -/
theorem qromDelayAdvantage_le_of_preprocessing_points {q k Q : ℕ}
    (adv : PreprocessingAdversary G q) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (scheme q) adv ≤
      min 1 (recoveryBound G q k +
        4 * (Q : ℝ≥0∞) * (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)) := by
  rw [qromDelayAdvantage_eq_preprocessedRecoveryAdvantage]
  exact preprocessedRecoveryAdvantage_le_points adv hQ honline

/-- The idealized puzzle is secure against every two-phase adversary satisfying the phase
budgets. The online clock may be any bound at most `q`; honest generation is outside that
clock. This theorem establishes the security predicate from the oracle argument. -/
theorem qromDelaySecure {q : ℕ} (b : Quantum.TimeLockPuzzle.DelayBudget)
    (honline : b.onlineRounds ≤ q) :
    Quantum.TimeLockPuzzle.QROMDelaySecure (scheme (G := G) q) b
      (min 1 (recoveryBound G q b.onlineWidth +
        preprocessingError G q (min b.preprocessingRounds b.preprocessingPoints)
          b.preprocessingPoints)) := by
  intro adv hbound
  apply qromDelayAdvantage_le_of_preprocessing_min adv hbound.1 hbound.2.1
  intro M state puzzle
  have h := hbound.2.2 M state puzzle
  exact ⟨h.1.mono honline, h.2.2⟩

/-- A point-only preprocessing consequence covers every budget-admitted two-phase adversary.
The error ignores the preprocessing round bound, retaining unrestricted classical and quantum
memory. The online point budget remains part of the admissibility condition. -/
theorem qromDelaySecure_points {q : ℕ} (b : Quantum.TimeLockPuzzle.DelayBudget)
    (honline : b.onlineRounds ≤ q) :
    Quantum.TimeLockPuzzle.QROMDelaySecure (scheme (G := G) q) b
      (min 1 (recoveryBound G q b.onlineWidth +
        4 * (b.preprocessingPoints : ℝ≥0∞) *
          (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ))) := by
  intro adv hbound
  apply qromDelayAdvantage_le_of_preprocessing_points adv hbound.2.1
  intro M state puzzle
  have h := hbound.2.2 M state puzzle
  exact ⟨h.1.mono honline, h.2.2⟩

end MaskedChainPuzzle
