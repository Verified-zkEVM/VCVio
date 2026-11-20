/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.TimeLockPuzzle.Quantum
public import VCVio.Quantum.Oracle.MaskedChain.Model

/-!
# Endpoint recovery with query-bounded oracle preprocessing

A two-phase adversary preprocesses one sampled oracle before seeing the masked-chain puzzle.
Its retained classical state and quantum register pass to the online phase. The complete
preprocessing/online program runs against that same oracle, without resetting private oracle
memory or initializing the adversary a second time.

The vertex tuple is independent of preprocessing. Sampling it outside the complete program
is equivalent to sampling it between phases: preprocessing has no puzzle argument. The named
puzzle bridge proves this equivalence against honest generation, retaining the endpoint jointly
with the oracle and public masks. Lost mass counts as failure.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Quantum.MaskedChain

variable {G : Type} [Fintype G] [DecidableEq G]

/-- A quantum endpoint adversary with oracle preprocessing and unrestricted retained memory. -/
abbrev PreprocessingAdversary (G : Type) [Fintype G] [DecidableEq G] (q : ℕ) :=
  TimeLockPuzzle.Adversary (qromBatchSpec G G) (Puzzle G q) G

/-- Preprocessing followed by online recovery of the published puzzle. The puzzle is passed
only to the online continuation, after the actual retained register and state are known. -/
@[expose]
noncomputable def preprocessedRecoveryProgram {q : ℕ} (adv : PreprocessingAdversary G q)
    (puzzle : Puzzle G q) :
    QuantumComp LocalSig.instruments (qromBatchSpec G G) (fun _ ↦ G) adv.initialReg :=
  adv.preprocess.bind fun M state ↦ adv.online M state puzzle

/-- The complete two-phase program as a family indexed by the public puzzle. Its initial state
is initialized once; its preprocessing prefix is independent of that puzzle. -/
@[expose]
noncomputable def preprocessedRecoveryAdversary {q : ℕ} (adv : PreprocessingAdversary G q) :
    OnlineAdversary LocalSig.instruments G q where
  initialReg := adv.initialReg
  initialState := adv.initialState
  run := preprocessedRecoveryProgram adv

variable [AddCommGroup G]

/-- The joint endpoint law under one uniformly sampled function and independent hidden tuple,
with the actual preprocessing prefix retained in every online run. -/
@[expose]
noncomputable def preprocessedRecoveryLaw {q : ℕ} (adv : PreprocessingAdversary G q) :
    Measure Prop :=
  recoveryLaw .instruments (preprocessedRecoveryAdversary adv)

/-- Unconditional endpoint recovery probability after preprocessing; no successful phase is
renormalized, and every call shares the same sampled function. -/
@[expose]
noncomputable def preprocessedRecoveryAdvantage {q : ℕ} (adv : PreprocessingAdversary G q) :
    ℝ≥0∞ :=
  preprocessedRecoveryLaw adv {True}

/-- Expand the full two-phase game as one uniform oracle average and one uniform tuple average. -/
theorem preprocessedRecoveryAdvantage_eq_sum {q : ℕ} (adv : PreprocessingAdversary G q) :
    preprocessedRecoveryAdvantage adv =
      ∑ H : G → G, (Fintype.card (G → G) : ℝ≥0∞)⁻¹ *
        ∑ vertices : Fin (q + 2) → G, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
          (parallelOracleRuntime H).evalDistMap .instruments
            (preprocessedRecoveryProgram adv (publicPuzzle H vertices)) adv.initialState
            (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True} :=
  recoveryAdvantage_eq_sum .instruments (preprocessedRecoveryAdversary adv)

/-- Lossy preprocessing and online execution remain unconditional subprobability success. -/
theorem preprocessedRecoveryAdvantage_le_one {q : ℕ} (adv : PreprocessingAdversary G q) :
    preprocessedRecoveryAdvantage adv ≤ 1 :=
  recoveryAdvantage_le_one .instruments (preprocessedRecoveryAdversary adv)

end Quantum.MaskedChain
