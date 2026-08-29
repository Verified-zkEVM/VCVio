/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget

/-!
# Multi-target collection game canary

One end-to-end producer canary checks the security-critical transcript separation rule. The same
toy collision wins when it uses only the challenge oracle and loses after evaluating the
collection at the challenge tweak. This rejects implementations that expose executable game
syntax while forgetting to enforce challenge/collection separation.
-/

@[expose] public section

open OracleComp OracleSpec

namespace MultiTargetCollectionTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

def collection : TweakableHashCollection Seed Bool Bool where
  Index := Unit
  Message _ := Bool
  eval _ _ _ _ := false

def problem : MultiTarget.CollectionProblem Seed Bool Bool where
  collection := collection
  target := ()
  maxTargets := 1

instance : DecidableEq problem.Message := by
  change DecidableEq Bool
  infer_instance

def challengeOnly : MultiTarget.TcrCAdversary problem where
  State := Unit
  pick := do
    let _ ← (liftM (problem.tcrPickSpec.query (.inr (.inl (false, false)))) :
      OracleComp problem.tcrPickSpec Bool)
    return ()
  find _ _ := pure (0, true)

def challengeAndCollection : MultiTarget.TcrCAdversary problem where
  State := Unit
  pick := do
    let _ ← (liftM (problem.tcrPickSpec.query (.inr (.inl (false, false)))) :
      OracleComp problem.tcrPickSpec Bool)
    let _ ← (liftM (problem.tcrPickSpec.query (.inr (.inr ⟨(), false, false⟩))) :
      OracleComp problem.tcrPickSpec Bool)
    return ()
  find _ _ := pure (0, true)

private lemma run_challengeOnly :
    (simulateQ (MultiTarget.tcrCPickImpl problem .only) challengeOnly.pick).run
        (MultiTarget.Transcript.empty problem) =
      pure ((), { targets := [(false, false)], collectionTweaks := [] }) := by
  rfl

private lemma run_challengeAndCollection :
    (simulateQ (MultiTarget.tcrCPickImpl problem .only) challengeAndCollection.pick).run
        (MultiTarget.Transcript.empty problem) =
      pure ((), { targets := [(false, false)], collectionTweaks := [false] }) := by
  rfl

/-- Reusing a challenge tweak through the collection oracle flips the same collision from a win
to a loss. -/
theorem transcript_separation_canary :
    MultiTarget.tcrCExperiment challengeOnly = pure true ∧
      MultiTarget.tcrCExperiment challengeAndCollection = pure false := by
  constructor
  · simp only [MultiTarget.tcrCExperiment, uniformSample_seed, pure_bind]
    rw [run_challengeOnly]
    simp [MultiTarget.Transcript.Valid, challengeOnly, problem, collection]
    rfl
  · simp only [MultiTarget.tcrCExperiment, uniformSample_seed, pure_bind]
    rw [run_challengeAndCollection]
    simp [MultiTarget.Transcript.Valid, challengeAndCollection, problem, collection]
    rfl

end MultiTargetCollectionTest
