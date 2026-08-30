/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUDC

/-!
# SM-DT-UD-C final-validity canaries

These executable games pin real/ideal separation, always-answering cap/duplicate/cross poisoning,
and the fact that repeated collection-only tweaks remain valid.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SMDTUDCTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

/-- Real challenges are always `false`; ideal challenges are always `true`. -/
def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ m := m

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def problem : TweakableHash.SM_DT_UD_C_Problem Unit Seed Bool Bool Bool where
  th := hash
  inputGen := pure false
  outputGen := pure true
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec +
  (TweakableHash.SM_DT_UD_C_challengeSpec Bool Bool +
    TweakableHash.finalValidityCollectionSpec problem.thColl)

def challenge (t : Bool) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inl t)))

def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

/-- The response itself distinguishes the deliberately separated real and ideal generators. -/
def separate : TweakableHash.SM_DT_UD_C_Adversary problem where
  State := Bool
  pick := challenge false
  distinguish y _ := pure (!y)

/-- The reverse distinguisher pins the other direction of the symmetric advantage. -/
def separateReverse : TweakableHash.SM_DT_UD_C_Adversary problem where
  State := Bool
  pick := challenge false
  distinguish y _ := pure y

/-- The second distinct target exceeds the cap, but its answer is still returned. -/
def exceedCap : TweakableHash.SM_DT_UD_C_Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← challenge true
    return (y₁, y₂)
  distinguish _ _ := pure true

/-- Reusing a target tweak is answered twice and poisons final validity. -/
def duplicateTarget : TweakableHash.SM_DT_UD_C_Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← challenge false
    return (y₁, y₂)
  distinguish _ _ := pure true

/-- A collection query at a target tweak is answered and poisons final validity. -/
def crossClash : TweakableHash.SM_DT_UD_C_Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← collectionQuery false true
    return (y₁, y₂)
  distinguish _ _ := pure true

/-- Repeating a collection-only tweak is valid; collection tweaks need not be distinct. -/
def repeatCollection : TweakableHash.SM_DT_UD_C_Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← collectionQuery false false
    let y₂ ← collectionQuery false false
    return (y₁, y₂)
  distinguish _ _ := pure true

private lemma run_separate_real :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .real problem .only)
      separate.pick).run .initial =
      pure (false, ⟨[false], [], true⟩) := by
  rfl

private lemma run_separate_ideal :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .ideal problem .only)
      separate.pick).run .initial =
      pure (true, ⟨[false], [], true⟩) := by
  rfl

private lemma run_separateReverse_real :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .real problem .only)
      separateReverse.pick).run .initial =
      pure (false, ⟨[false], [], true⟩) := by
  rfl

private lemma run_separateReverse_ideal :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .ideal problem .only)
      separateReverse.pick).run .initial =
      pure (true, ⟨[false], [], true⟩) := by
  rfl

private lemma run_exceedCap_real :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .real problem .only)
      exceedCap.pick).run .initial =
      pure ((false, false), ⟨[false, true], [], false⟩) := by
  rfl

private lemma run_duplicateTarget_real :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .real problem .only)
      duplicateTarget.pick).run .initial =
      pure ((false, false), ⟨[false, false], [], false⟩) := by
  rfl

private lemma run_crossClash_real :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .real problem .only)
      crossClash.pick).run .initial =
      pure ((false, true), ⟨[false], [false], false⟩) := by
  rfl

private lemma run_repeatCollection_real :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .real problem .only)
      repeatCollection.pick).run .initial =
      pure ((false, false), ⟨[], [false, false], true⟩) := by
  rfl

private lemma run_repeatCollection_ideal :
    (simulateQ (TweakableHash.SM_DT_UD_C_oracles .ideal problem .only)
      repeatCollection.pick).run .initial =
      pure ((false, false), ⟨[], [false, false], true⟩) := by
  rfl

private lemma experiment_separate_real :
    TweakableHash.SM_DT_UD_C_Experiment .real separate = pure true := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_separate_real]
  rfl

private lemma experiment_separate_ideal :
    TweakableHash.SM_DT_UD_C_Experiment .ideal separate = pure false := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_separate_ideal]
  rfl

private lemma experiment_separateReverse_real :
    TweakableHash.SM_DT_UD_C_Experiment .real separateReverse = pure false := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_separateReverse_real]
  rfl

private lemma experiment_separateReverse_ideal :
    TweakableHash.SM_DT_UD_C_Experiment .ideal separateReverse = pure true := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_separateReverse_ideal]
  rfl

private lemma experiment_exceedCap_real :
    TweakableHash.SM_DT_UD_C_Experiment .real exceedCap = pure false := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_exceedCap_real]
  rfl

private lemma experiment_duplicateTarget_real :
    TweakableHash.SM_DT_UD_C_Experiment .real duplicateTarget = pure false := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_duplicateTarget_real]
  rfl

private lemma experiment_crossClash_real :
    TweakableHash.SM_DT_UD_C_Experiment .real crossClash = pure false := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_crossClash_real]
  rfl

private lemma experiment_repeatCollection_real :
    TweakableHash.SM_DT_UD_C_Experiment .real repeatCollection = pure true := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_repeatCollection_real]
  rfl

private lemma experiment_repeatCollection_ideal :
    TweakableHash.SM_DT_UD_C_Experiment .ideal repeatCollection = pure true := by
  simp only [TweakableHash.SM_DT_UD_C_Experiment, problem_seedGen, pure_bind]
  rw [run_repeatCollection_ideal]
  rfl

/-- The explicit input/output generators separate the worlds, and the symmetric gap is one. -/
theorem real_ideal_separation_canary :
    TweakableHash.SM_DT_UD_C_Experiment .real separate = pure true ∧
      TweakableHash.SM_DT_UD_C_Experiment .ideal separate = pure false ∧
      TweakableHash.SM_DT_UD_C_RealSuccess separate = 1 ∧
      TweakableHash.SM_DT_UD_C_IdealSuccess separate = 0 ∧
      TweakableHash.SM_DT_UD_C_Advantage separate = 1 ∧
      TweakableHash.SM_DT_UD_Advantage separate = 1 := by
  simp [experiment_separate_real, experiment_separate_ideal,
    TweakableHash.SM_DT_UD_C_RealSuccess, TweakableHash.SM_DT_UD_C_IdealSuccess,
    TweakableHash.SM_DT_UD_C_Advantage, TweakableHash.SM_DT_UD_Advantage]

/-- The reverse gap is also one. A one-sided `real - ideal` definition would make this zero. -/
theorem symmetric_gap_reverse_canary :
    TweakableHash.SM_DT_UD_C_Experiment .real separateReverse = pure false ∧
      TweakableHash.SM_DT_UD_C_Experiment .ideal separateReverse = pure true ∧
      TweakableHash.SM_DT_UD_C_RealSuccess separateReverse = 0 ∧
      TweakableHash.SM_DT_UD_C_IdealSuccess separateReverse = 1 ∧
      TweakableHash.SM_DT_UD_C_Advantage separateReverse = 1 := by
  simp [experiment_separateReverse_real, experiment_separateReverse_ideal,
    TweakableHash.SM_DT_UD_C_RealSuccess, TweakableHash.SM_DT_UD_C_IdealSuccess,
    TweakableHash.SM_DT_UD_C_Advantage]

/-- Cap, duplicate-target, and cross-oracle violations poison only the final conjunction: all
queries returned their concrete real-world answers and were recorded in the run lemmas above. -/
theorem final_validity_poison_canary :
    TweakableHash.SM_DT_UD_C_Experiment .real exceedCap = pure false ∧
      TweakableHash.SM_DT_UD_C_Experiment .real duplicateTarget = pure false ∧
      TweakableHash.SM_DT_UD_C_Experiment .real crossClash = pure false := by
  exact ⟨experiment_exceedCap_real, experiment_duplicateTarget_real,
    experiment_crossClash_real⟩

/-- Repeated collection-only tweaks remain valid in both worlds. -/
theorem repeated_collection_allowed_canary :
    TweakableHash.SM_DT_UD_C_Experiment .real repeatCollection = pure true ∧
      TweakableHash.SM_DT_UD_C_Experiment .ideal repeatCollection = pure true := by
  exact ⟨experiment_repeatCollection_real, experiment_repeatCollection_ideal⟩

/-- The phase types expose the challenge/collection bundle only before seed reveal. -/
example : OracleComp Specs separate.State := separate.pick

example : separate.State → Seed → ProbComp Bool := separate.distinguish

end SMDTUDCTest
