/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.NetworkUnlinkability

/-!
# Native network unlinkability through ordinary imports

An adaptive tag/reader client instantiates the two named distinguishers, their concrete query
budgets, and a nontrivial numerical loss bound. The empty-client boundary checks the
retained collision flag without requiring positive query fuel.
-/

public section

namespace PRFTagReader.NetworkUnlinkability.Tests

open OracleComp OracleSpec MeasureTheory

/-- A reader query depends on the sampled tag response. -/
@[expose]
def adaptive : UnlinkAdversary Bool (Fin 64) (Fin 64) :=
  queryBind (.inl false) fun transcript =>
    match transcript with
    | none => pure false
    | some transcript => queryBind (.inr transcript) fun reply => pure reply.accepts

theorem reader_bound : IsQueryBoundP adaptive (·.isRight) 1 := by
  change _ ∧ _
  constructor
  · decide
  · intro transcript
    cases transcript
    · trivial
    · exact ⟨by simp, fun _ => trivial⟩

theorem tag_bound : IsQueryBoundP adaptive (·.isLeft) 1 := by
  change _ ∧ _
  constructor
  · decide
  · intro transcript
    cases transcript
    · trivial
    · exact ⟨by simp, fun _ => trivial⟩

example :
    IsQueryBoundP (unlinkToMultiplePRFReduction (sessionsPerTag := 2) adaptive) (·.isRight) 3 ∧
    IsQueryBoundP (unlinkToSinglePRFReduction (sessionsPerTag := 2) adaptive) (·.isRight) 5 := by
  simpa using named_reduction_budgets adaptive 1 1 reader_bound tag_bound

-- The collision, multiple reader, aliasing, and single reader losses are 8, 2, 1, and 4
-- sixty-fourths, respectively. The explicit PRF hypotheses name both distinguishers.
example {K : Type} (prfs : TagReaderPRFs K Bool (Fin 64) (Fin 64) 2)
    (epsilonMultiple epsilonSingle : Real)
    (hMultiple : (PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := 2) adaptive)).toReal ≤ epsilonMultiple)
    (hSingle : (PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := 2) adaptive)).toReal ≤ epsilonSingle) :
    |(𝒟[realMultiple prfs 2 adaptive] {true}).toReal -
      (𝒟[realSingle prfs 2 adaptive] {true}).toReal| ≤
      epsilonMultiple + epsilonSingle + 15 / 64 := by
  have h := full_unlinkability prfs adaptive 1 1 reader_bound tag_bound
    epsilonMultiple epsilonSingle hMultiple hSingle
  norm_num at h ⊢
  linarith

example : badExperiment (TagId := Bool) (Nonce := Bool) (Digest := Bool)
    (sessionsPerTag := 0) 0
    (pure true : OracleComp (UnlinkOracleSpec Bool Bool Bool) Bool) = pure false := by
  rw [badExperiment_eq _ _ (by trivial), simulateQ_pure, StateT.run_pure, map_pure]
  rfl

example {K : Type} (prfs : TagReaderPRFs K Bool (Fin 64) (Fin 64) 2) :
    IsProbabilityMeasure 𝒟[realMultiple prfs 1 adaptive] := inferInstance

end PRFTagReader.NetworkUnlinkability.Tests
