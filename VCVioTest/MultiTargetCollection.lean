/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# Multi-target collection-oracle canary

One end-to-end producer canary checks both directions of the security-critical tweak-separation
rule. A collection query at an existing challenge tweak must return `none`; the adversary branches
on that rejection, so forgetting the check turns its toy collision into a loss. In the other order,
a challenge query at a tweak already spent on the collection oracle is rejected and leaves no
target to forge against.
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

def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ _ := false

def problem : TweakableHash.SM_DT_TCR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

@[simp] lemma problem_eval (pk : Seed) (tweak message : Bool) :
    problem.th.eval pk tweak message = false := rfl

def challengeOnly : TweakableHash.SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← (liftM ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
      TweakableHash.collectionSpec problem.thColl)).query (.inr (.inl (false, false)))) :
      OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
        TweakableHash.collectionSpec problem.thColl)) (Option Bool))
    return ()
  forge _ _ := pure (0, true)

def challengeThenCollection : TweakableHash.SM_DT_TCR_Adversary problem where
  State := Option Bool
  choose := do
    let _ ← (liftM ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
      TweakableHash.collectionSpec problem.thColl)).query (.inr (.inl (false, false)))) :
      OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
        TweakableHash.collectionSpec problem.thColl)) (Option Bool))
    liftM ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
      TweakableHash.collectionSpec problem.thColl)).query (.inr (.inr ⟨(), false, false⟩)))
  forge answer _ := match answer with
    | none => pure (0, true)
    | some _ => pure (0, false)

def collectionThenChallenge : TweakableHash.SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← (liftM ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
      TweakableHash.collectionSpec problem.thColl)).query (.inr (.inr ⟨(), false, false⟩))) :
      OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
        TweakableHash.collectionSpec problem.thColl)) (Option Bool))
    let _ ← (liftM ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
      TweakableHash.collectionSpec problem.thColl)).query (.inr (.inl (false, false)))) :
      OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
        TweakableHash.collectionSpec problem.thColl)) (Option Bool))
    return ()
  forge _ _ := pure (0, true)

private lemma run_challengeOnly :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles problem .only) challengeOnly.choose).run ([], []) =
      pure ((), ([(false, false)], [])) := by
  rfl

private lemma run_challengeThenCollection :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles problem .only)
      challengeThenCollection.choose).run ([], []) =
      pure (none, ([(false, false)], [])) := by
  rfl

private lemma run_collectionThenChallenge :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles problem .only)
      collectionThenChallenge.choose).run ([], []) =
      pure ((), ([], [false])) := by
  rfl

/-- Both query orders enforce challenge/collection tweak separation. -/
theorem oracle_separation_canary :
    TweakableHash.SM_DT_TCR_Experiment challengeOnly = pure true ∧
      TweakableHash.SM_DT_TCR_Experiment challengeThenCollection = pure true ∧
      TweakableHash.SM_DT_TCR_Experiment collectionThenChallenge = pure false := by
  constructor
  · simp only [TweakableHash.SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
    rw [run_challengeOnly]
    simp [challengeOnly, problem_eval]
  · constructor
    · simp only [TweakableHash.SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
      rw [run_challengeThenCollection]
      simp [challengeThenCollection, problem_eval]
    · simp only [TweakableHash.SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
      rw [run_collectionThenChallenge]
      rfl

end MultiTargetCollectionTest
