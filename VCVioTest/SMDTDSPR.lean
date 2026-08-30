/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR

/-!
# SM-DT-DSPR mutation canaries

These small executable games pin the security-critical parts of the definition: the hidden-seed
phase split, always-answering final-validity semantics, cap and cross-oracle poisoning, and the
`SPprob` subtraction in the exported advantage.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SMDTDSPRTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

/-- Every Boolean target has a second preimage. -/
def collidingHash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

/-- No Boolean target has a second preimage. -/
def injectiveHash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ m := m

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def collidingProblem : TweakableHash.SM_DT_DSPR_Problem Unit Seed Bool Bool Bool where
  th := collidingHash
  thColl := collection
  numTargets := 1

def injectiveProblem : TweakableHash.SM_DT_DSPR_Problem Unit Seed Bool Bool Bool where
  th := injectiveHash
  thColl := collection
  numTargets := 1

@[simp] lemma collidingProblem_seedGen : collidingProblem.th.seedGen = pure .only := rfl

@[simp] lemma injectiveProblem_seedGen : injectiveProblem.th.seedGen = pure .only := rfl

abbrev Specs (prob : TweakableHash.SM_DT_DSPR_Problem Unit Seed Bool Bool Bool) :=
  unifSpec + (TweakableHash.SM_DT_DSPR_challengeSpec Bool Bool Bool +
    TweakableHash.finalValidityCollectionSpec prob.thColl)

def challenge (prob : TweakableHash.SM_DT_DSPR_Problem Unit Seed Bool Bool Bool)
    (t m : Bool) : OracleComp (Specs prob) Bool :=
  liftM ((Specs prob).query (.inr (.inl (t, m))))

def collectionQuery (prob : TweakableHash.SM_DT_DSPR_Problem Unit Seed Bool Bool Bool)
    (t : Bool) (m : prob.thColl.Msg ()) : OracleComp (Specs prob) Bool :=
  liftM ((Specs prob).query (.inr (.inr ⟨(), t, m⟩)))

/-- This adversary predicts the collision that always exists for `collidingHash`. -/
def predictCollision : TweakableHash.SM_DT_DSPR_Adversary collidingProblem where
  State := Unit
  choose := challenge collidingProblem false false *> pure ()
  guess _ _ := pure (0, true)

/-- This adversary correctly predicts that the injective target has no second preimage. -/
def predictNoCollision : TweakableHash.SM_DT_DSPR_Adversary injectiveProblem where
  State := Unit
  choose := challenge injectiveProblem false false *> pure ()
  guess _ _ := pure (0, false)

/-- A second target query exceeds the cap but is still answered and recorded. -/
def exceedCap : TweakableHash.SM_DT_DSPR_Adversary collidingProblem where
  State := Bool
  choose := do
    let _ ← challenge collidingProblem false false
    challenge collidingProblem true false
  guess answer _ := pure (if answer then 1 else 0, true)

/-- A challenge/collection tweak clash is answered by both oracles but poisons the game. -/
def clashCollection : TweakableHash.SM_DT_DSPR_Adversary collidingProblem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge collidingProblem false false
    let y₂ ← collectionQuery collidingProblem false true
    return (y₁, y₂)
  guess _ _ := pure (0, true)

private lemma run_predictCollision :
    (simulateQ (TweakableHash.SM_DT_DSPR_oracles collidingProblem .only)
      predictCollision.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl

private lemma run_predictNoCollision :
    (simulateQ (TweakableHash.SM_DT_DSPR_oracles injectiveProblem .only)
      predictNoCollision.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl

private lemma run_exceedCap :
    (simulateQ (TweakableHash.SM_DT_DSPR_oracles collidingProblem .only)
      exceedCap.choose).run .initial =
      pure (false, ⟨[(false, false), (true, false)], [], false⟩) := by
  rfl

private lemma run_clashCollection :
    (simulateQ (TweakableHash.SM_DT_DSPR_oracles collidingProblem .only)
      clashCollection.choose).run .initial =
      pure ((false, true), ⟨[(false, false)], [false], false⟩) := by
  rfl

private lemma experiment_predictCollision :
    TweakableHash.SM_DT_DSPR_Experiment predictCollision = pure true := by
  simp only [TweakableHash.SM_DT_DSPR_Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl

private lemma baseline_predictCollision :
    TweakableHash.SM_DT_SP_Experiment predictCollision = pure true := by
  simp only [TweakableHash.SM_DT_SP_Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl

private lemma experiment_predictNoCollision :
    TweakableHash.SM_DT_DSPR_Experiment predictNoCollision = pure true := by
  simp only [TweakableHash.SM_DT_DSPR_Experiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl

private lemma baseline_predictNoCollision :
    TweakableHash.SM_DT_SP_Experiment predictNoCollision = pure false := by
  simp only [TweakableHash.SM_DT_SP_Experiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl

private lemma experiment_exceedCap :
    TweakableHash.SM_DT_DSPR_Experiment exceedCap = pure false := by
  simp only [TweakableHash.SM_DT_DSPR_Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_exceedCap]
  rfl

private lemma baseline_exceedCap :
    TweakableHash.SM_DT_SP_Experiment exceedCap = pure false := by
  simp only [TweakableHash.SM_DT_SP_Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_exceedCap]
  rfl

private lemma experiment_clashCollection :
    TweakableHash.SM_DT_DSPR_Experiment clashCollection = pure false := by
  simp only [TweakableHash.SM_DT_DSPR_Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_clashCollection]
  rfl

private lemma baseline_clashCollection :
    TweakableHash.SM_DT_SP_Experiment clashCollection = pure false := by
  simp only [TweakableHash.SM_DT_SP_Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_clashCollection]
  rfl

/-- Prediction success and `SPprob` differ on the no-second-preimage instance, while both equal one
on the collision instance. This pins the baseline subtraction: the corresponding advantages are
respectively one and zero. -/
theorem baseline_subtraction_canary :
    TweakableHash.SM_DT_DSPR_Experiment predictCollision = pure true ∧
      TweakableHash.SM_DT_SP_Experiment predictCollision = pure true ∧
      TweakableHash.SM_DT_DSPR_Advantage predictCollision = 0 ∧
      TweakableHash.SM_DT_DSPR_Experiment predictNoCollision = pure true ∧
      TweakableHash.SM_DT_SP_Experiment predictNoCollision = pure false ∧
      TweakableHash.SM_DT_DSPR_Advantage predictNoCollision = 1 := by
  simp [experiment_predictCollision, baseline_predictCollision, experiment_predictNoCollision,
    baseline_predictNoCollision, TweakableHash.SM_DT_DSPR_Advantage,
    TweakableHash.SM_DT_DSPR_Success, TweakableHash.SM_DT_SP_Probability]

/-- Invalid queries are not rejected: their concrete answers are visible in the private state, all
queries are recorded, and only the sticky final-validity bit makes both experiments lose. -/
theorem poison_not_rejection_canary :
    TweakableHash.SM_DT_DSPR_Experiment exceedCap = pure false ∧
      TweakableHash.SM_DT_SP_Experiment exceedCap = pure false ∧
      TweakableHash.SM_DT_DSPR_Experiment clashCollection = pure false ∧
      TweakableHash.SM_DT_SP_Experiment clashCollection = pure false := by
  exact ⟨experiment_exceedCap, baseline_exceedCap, experiment_clashCollection,
    baseline_clashCollection⟩

/-- The phase types themselves pin seed/oracle access: `choose` gets the oracle bundle but no seed,
whereas `guess` gets the seed but has type `ProbComp` and therefore no challenge oracle. -/
example : OracleComp (Specs collidingProblem) predictCollision.State :=
  predictCollision.choose

example : predictCollision.State → Seed → ProbComp (ℕ × Bool) := predictCollision.guess

end SMDTDSPRTest
