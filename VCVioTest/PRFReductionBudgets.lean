/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.ReductionBudgets

/-! # Public PRF budgets on adaptive clients and degenerate interfaces -/

public section

namespace PRFTagReader.QueryBudgets.Tests

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery

/-- A reader call is selected by the tag response. -/
@[expose]
def adaptive : OracleComp (UnlinkOracleSpec Bool Bool Bool) Bool :=
  queryBind (.inl false) fun transcript =>
    match transcript with
    | none => pure false
    | some transcript => queryBind (.inr transcript) fun reply => pure reply.accepts

theorem adaptive_reader_bound : IsQueryBoundP adaptive (·.isRight) 1 := by
  change _ ∧ _
  constructor
  · decide
  · intro transcript
    cases transcript
    · trivial
    · exact ⟨by simp, fun _ => trivial⟩

theorem adaptive_tag_bound : IsQueryBoundP adaptive (·.isLeft) 1 := by
  change _ ∧ _
  constructor
  · decide
  · intro transcript
    cases transcript
    · trivial
    · exact ⟨by simp, fun _ => trivial⟩

example : IsQueryBoundP (unlinkToMultiplePRFReduction (sessionsPerTag := 2) adaptive)
    (·.isRight) 3 := by
  simpa using multiple_reduction_bound adaptive 1 1 adaptive_reader_bound adaptive_tag_bound

example : IsQueryBoundP (unlinkToSinglePRFReduction (sessionsPerTag := 2) adaptive)
    (·.isRight) 5 := by
  simpa using single_reduction_bound adaptive 1 1 adaptive_reader_bound adaptive_tag_bound

example : IsQueryBoundP
    (unlinkToMultiplePRFReduction (TagId := Bool) (Nonce := Bool) (Digest := Bool)
      (sessionsPerTag := 0)
      (pure true : OracleComp (UnlinkOracleSpec Bool Bool Bool) Bool)) (·.isRight) 0 := by
  simpa using multiple_reduction_bound (TagId := Bool) (Nonce := Bool) (Digest := Bool)
    (sessionsPerTag := 0) (pure true : OracleComp (UnlinkOracleSpec Bool Bool Bool) Bool)
    0 0 (by simp) (by simp)

example (transcript : TagTranscript Bool Bool) (state : UnlinkState Empty) :
    IsQueryBoundP ((unlinkToMultiplePRFReaderImpl transcript).run state) (·.isRight) 0 := by
  simpa using multiple_reader_bound transcript state

example (transcript : TagTranscript Bool Bool) (state : UnlinkState Bool) :
    IsQueryBoundP
      ((unlinkToSinglePRFReaderImpl (sessionsPerTag := 0) transcript).run state)
      (·.isRight) 0 := by
  simpa using single_reader_bound (sessionsPerTag := 0) transcript state

/-- An exhausted tag returns without sampling or calling the PRF. -/
example (state : UnlinkState Bool) (h : ¬ state.sessionsUsed false < 2) :
    (unlinkToMultiplePRFTagImpl (Nonce := Bool) (Digest := Bool)
      (sessionsPerTag := 2) false).run state = pure (none, state) := by
  unfold unlinkToMultiplePRFTagImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, dite_eq_right h, StateT.run_pure]

#print axioms PRFTagReader.QueryBudgets.multiple_reduction_bound
#print axioms PRFTagReader.QueryBudgets.single_reduction_bound

end PRFTagReader.QueryBudgets.Tests
