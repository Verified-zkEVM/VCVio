/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.OpenPREFromTCRDSPR

/-! # SM-DT-OpenPRE exact-game canaries -/

@[expose] public section

open OracleComp OracleSpec

namespace SMDTOpenPRETest

inductive Seed
  | only

inductive Input
  | only
  deriving DecidableEq, Inhabited

instance : Fintype Input where
  elems := {.only}
  complete x := by cases x; simp

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

instance : SampleableType Input where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

@[simp] lemma uniformSample_input : ($ᵗ Input : ProbComp Input) = pure .only := rfl

def hash : TweakableHash Seed Bool Input Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def problem1 : TweakableHash.SM_DT_OpenPRE_Problem Unit Seed Bool Input Bool where
  th := hash
  inputGen := $ᵗ Input
  thColl := collection
  numTargets := 1

def problem2 : TweakableHash.SM_DT_OpenPRE_Problem Unit Seed Bool Input Bool where
  th := hash
  inputGen := $ᵗ Input
  thColl := collection
  numTargets := 2

@[simp] lemma problem1_seedGen : problem1.th.seedGen = pure .only := rfl

@[simp] lemma problem2_seedGen : problem2.th.seedGen = pure .only := rfl

def collectionQuery1 (t m : Bool) :
    OracleComp (unifSpec + TweakableHash.finalValidityCollectionSpec problem1.thColl) Bool :=
  liftM ((unifSpec + TweakableHash.finalValidityCollectionSpec problem1.thColl).query
    (.inr ⟨(), t, m⟩))

def open1 (j : ℕ) :
    OracleComp (unifSpec + TweakableHash.SM_DT_OpenPRE_openSpec Input) Input :=
  liftM ((unifSpec + TweakableHash.SM_DT_OpenPRE_openSpec Input).query (.inr j))

def valid : TweakableHash.SM_DT_OpenPRE_Adversary problem1 where
  State := Unit
  pick := pure ((), [false])
  find _ _ _ := pure (0, .only)

/-- A committed list longer than the cap must be truncated, not used to poison validity. -/
def overlong : TweakableHash.SM_DT_OpenPRE_Adversary problem1 where
  State := Unit
  pick := pure ((), [false, true])
  find _ _ _ := pure (0, .only)

def collectionClash : TweakableHash.SM_DT_OpenPRE_Adversary problem1 where
  State := Bool
  pick := do
    let y ← collectionQuery1 false true
    return (y, [false])
  find _ _ _ := pure (0, .only)

def openedSelected : TweakableHash.SM_DT_OpenPRE_Adversary problem1 where
  State := Unit
  pick := pure ((), [false])
  find _ _ _ := do
    let _ ← open1 0
    return (0, .only)

def duplicateTargets : TweakableHash.SM_DT_OpenPRE_Adversary problem2 where
  State := Unit
  pick := pure ((), [false, false])
  find _ _ _ := pure (0, .only)

/-- Opening a different target remains legal. -/
def openedOther : TweakableHash.SM_DT_OpenPRE_Adversary problem2 where
  State := Unit
  pick := pure ((), [false, true])
  find _ _ _ := do
    let _ ← open1 1
    return (0, .only)

private lemma initialize_one :
    (TweakableHash.SM_DT_OpenPRE_initializeTargets problem1 .only [false]).run .initial =
      pure ([false], ⟨[(false, .only)], [], true⟩) := by
  rfl

/-- This pins the source's bounded-prefix behavior independently of the final winning predicate. -/
private lemma initialize_bounded_prefix :
    (TweakableHash.SM_DT_OpenPRE_initializeTargets problem1 .only
      ([false, true].take problem1.numTargets)).run .initial =
      pure ([false], ⟨[(false, .only)], [], true⟩) := by
  rfl

private lemma experiment_valid :
    TweakableHash.SM_DT_OpenPRE_Experiment valid = pure true := by
  rfl

private lemma experiment_overlong :
    TweakableHash.SM_DT_OpenPRE_Experiment overlong = pure true := by
  rfl

private lemma experiment_collectionClash :
    TweakableHash.SM_DT_OpenPRE_Experiment collectionClash = pure false := by
  rfl

private lemma experiment_openedSelected :
    TweakableHash.SM_DT_OpenPRE_Experiment openedSelected = pure false := by
  rfl

private lemma experiment_duplicateTargets :
    TweakableHash.SM_DT_OpenPRE_Experiment duplicateTargets = pure false := by
  rfl

private lemma experiment_openedOther :
    TweakableHash.SM_DT_OpenPRE_Experiment openedOther = pure true := by
  rfl

private lemma tcr_reduction_valid :
    TweakableHash.SM_DT_TCR_Experiment (TweakableHash.SM_DT_OpenPRE_toTCR valid) =
      pure false := by
  rfl

private lemma dspr_reduction_valid :
    TweakableHash.SM_DT_DSPR_Experiment (TweakableHash.SM_DT_OpenPRE_toDSPR valid) =
      pure true := by
  rfl

private lemma dspr_reduction_openedSelected :
    TweakableHash.SM_DT_DSPR_Experiment
      (TweakableHash.SM_DT_OpenPRE_toDSPR openedSelected) = pure false := by
  rfl

/-- Mutation-resistant pins for prefix truncation, final validity, and the adaptive opening
phase. -/
theorem exact_game_canary :
    TweakableHash.SM_DT_OpenPRE_Experiment valid = pure true ∧
      TweakableHash.SM_DT_OpenPRE_Experiment overlong = pure true ∧
      TweakableHash.SM_DT_OpenPRE_Experiment collectionClash = pure false ∧
      TweakableHash.SM_DT_OpenPRE_Experiment openedSelected = pure false ∧
      TweakableHash.SM_DT_OpenPRE_Experiment duplicateTargets = pure false ∧
      TweakableHash.SM_DT_OpenPRE_Experiment openedOther = pure true ∧
      TweakableHash.SM_DT_TCR_Experiment (TweakableHash.SM_DT_OpenPRE_toTCR valid) =
        pure false ∧
      TweakableHash.SM_DT_DSPR_Experiment (TweakableHash.SM_DT_OpenPRE_toDSPR valid) =
        pure true ∧
      TweakableHash.SM_DT_DSPR_Experiment
        (TweakableHash.SM_DT_OpenPRE_toDSPR openedSelected) = pure false :=
  ⟨experiment_valid, experiment_overlong, experiment_collectionClash,
    experiment_openedSelected, experiment_duplicateTargets, experiment_openedOther,
    tcr_reduction_valid, dspr_reduction_valid, dspr_reduction_openedSelected⟩

end SMDTOpenPRETest
