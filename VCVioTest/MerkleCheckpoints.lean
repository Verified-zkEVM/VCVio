/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.MerkleCheckpoints

/-! # Frozen-checkpoint and shared-cache semantics through ordinary imports -/

public section

open OracleComp OracleSpec MeasureTheory
open MerkleTreeMultiExtractability MerkleTreeMultiExtractability.DelayedObservation
open MerkleCheckpoints

noncomputable local instance : IsUniformMeasureSpec (Query →ₒ Bool) :=
  IsUniformMeasureSpec.ofFiniteNonempty (Query →ₒ Bool)

example : (atTerminal (outcome false) checkpoint).root = checkpoint.root := rfl

example : (outcome false).HasOpeningOrEqualRootDisagreement model ∧
    ¬ LateOpeningFailure model.view (outcome false) :=
  ⟨(publicFailure_outcome false).2 rfl, no_lateFailure_outcome false⟩

example : Drift model.view (outcome false) ∧ ¬ Drift model.view (outcome true) :=
  ⟨drift_outcome_false, no_drift_outcome_true⟩

-- The drift charge is sharp on the actual executable game.
example :
    letI : MeasurableSpace (Transcript Unit Query Unit Bool config) := ⊤
    𝒟[extractabilityExperiment model config 1 adversary]
        {tr | tr.HasOpeningOrEqualRootDisagreement model} =
      𝒟[extractabilityExperiment model config 1 adversary] {tr | LateOpeningFailure model.view tr} +
      𝒟[extractabilityExperiment model config 1 adversary] {tr | Drift model.view tr} := by
  rw [publicFailure_probability, lateFailure_probability, drift_probability, zero_add]

example : 𝒟[honestShared] {true} - 𝒟[honestReset] {true} = (1 : ENNReal) / 2 := by
  rw [honestShared_probability, honestReset_probability]
  norm_num

-- Resetting memoization while retaining the same fixed function preserves completeness.
example (table : Query → Bool) :
    evalWithAnswerFn (QueryImpl.ofFn table) honestReset = true :=
  reset_same_table_accepts table
