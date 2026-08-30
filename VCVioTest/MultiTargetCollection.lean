/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# Multi-target final-validity collection canary

The target and collection oracles answer every query. A tweak clash in either order is recorded and
poisons the final-validity bit, so even a concrete collision loses. Repeated collection-only tweaks
remain valid. These canaries fail if the game is mutated back to rejection-on-arrival, forgets one
cross-oracle direction, or incorrectly requires collection tweaks to be distinct.
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
  eval _ _ _ m := m

def problem : TweakableHash.SM_DT_TCR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec Bool Bool Bool +
  TweakableHash.finalValidityCollectionSpec problem.thColl)

def challenge (t m : Bool) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inl (t, m))))

def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

def challengeOnly : TweakableHash.SM_DT_TCR_Adversary problem where
  State := Unit
  choose := challenge false false *> pure ()
  forge _ _ := pure (0, true)

def challengeThenCollection : TweakableHash.SM_DT_TCR_Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge false false
    let y₂ ← collectionQuery false true
    return (y₁, y₂)
  forge _ _ := pure (0, true)

def collectionThenChallenge : TweakableHash.SM_DT_TCR_Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← collectionQuery false true
    let y₂ ← challenge false false
    return (y₁, y₂)
  forge _ _ := pure (0, true)

/-- Repeating a collection tweak is permitted; the subsequent fresh challenge remains valid. -/
def repeatedCollection : TweakableHash.SM_DT_TCR_Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← collectionQuery false false
    let y₂ ← collectionQuery false true
    let _ ← challenge true false
    return (y₁, y₂)
  forge _ _ := pure (0, true)

private lemma run_challengeOnly :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles problem .only) challengeOnly.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl

private lemma run_challengeThenCollection :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles problem .only)
      challengeThenCollection.choose).run .initial =
      pure ((false, true), ⟨[(false, false)], [false], false⟩) := by
  rfl

private lemma run_collectionThenChallenge :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles problem .only)
      collectionThenChallenge.choose).run .initial =
      pure ((true, false), ⟨[(false, false)], [false], false⟩) := by
  rfl

private lemma run_repeatedCollection :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles problem .only)
      repeatedCollection.choose).run .initial =
      pure ((false, true), ⟨[(true, false)], [false, false], true⟩) := by
  rfl

private lemma experiment_challengeOnly :
    TweakableHash.SM_DT_TCR_Experiment challengeOnly = pure true := by
  simp only [TweakableHash.SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_challengeOnly]
  rfl

private lemma experiment_challengeThenCollection :
    TweakableHash.SM_DT_TCR_Experiment challengeThenCollection = pure false := by
  simp only [TweakableHash.SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_challengeThenCollection]
  rfl

private lemma experiment_collectionThenChallenge :
    TweakableHash.SM_DT_TCR_Experiment collectionThenChallenge = pure false := by
  simp only [TweakableHash.SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_collectionThenChallenge]
  rfl

private lemma experiment_repeatedCollection :
    TweakableHash.SM_DT_TCR_Experiment repeatedCollection = pure true := by
  simp only [TweakableHash.SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_repeatedCollection]
  rfl

/-- Both clash orders are answered and recorded but lose through final validity; repeated
collection tweaks remain legal. -/
theorem final_validity_collection_canary :
    TweakableHash.SM_DT_TCR_Experiment challengeOnly = pure true ∧
      TweakableHash.SM_DT_TCR_Experiment challengeThenCollection = pure false ∧
      TweakableHash.SM_DT_TCR_Experiment collectionThenChallenge = pure false ∧
      TweakableHash.SM_DT_TCR_Experiment repeatedCollection = pure true :=
  ⟨experiment_challengeOnly, experiment_challengeThenCollection,
    experiment_collectionThenChallenge, experiment_repeatedCollection⟩

end MultiTargetCollectionTest
