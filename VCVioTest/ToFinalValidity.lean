/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.ToFinalValidity

/-!
# Tweak-discipline bridge canary

`VCVioTest.MultiTargetCollection` pins that a rejection-on-arrival adversary which follows a
challenge with a colliding collection query **wins**: the collection query is refused, the state is
untouched, and the earlier target is still forgeable. `VCVioTest.SMDTTCRFinalValidity` pins that the
same transcript **loses** against the monitor: the collection query is answered and poisons final
validity.

This file pins that the conversion resolves that disagreement in the winning direction. It sends
that adversary to a source-final-validity adversary that wins, because the wrapper declines to
forward the poisoning query and synthesises the `none` its counterpart received. A conversion that
merely renamed the phases would inherit the losing outcome.

The SM-PRE section runs the same transcript at the game whose challenge oracle draws its own
message, over a one-element message subspace so the draw reduces.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash

namespace ToFinalValidityTest

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

def problem : SM_DT_TCR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec + (SM_DT_TCR_challengeSpec Bool Bool Bool +
  collectionSpec problem.thColl)

def challenge (tm : Bool × Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl tm)))

def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, then query the collection at that same tweak. The rejection-on-arrival oracles
refuse the second query, and the adversary branches on that refusal to forge against the target it
already holds. -/
def challengeThenCollection : SM_DT_TCR_Adversary problem where
  State := Option Bool
  choose := do
    let _ ← challenge (false, false)
    collectionQuery false false
  forge answer _ := match answer with
    | none => pure (0, true)
    | some _ => pure (0, false)

/-- The rejection-on-arrival game: the clash is refused and the adversary wins. -/
theorem experiment_challengeThenCollection :
    SM_DT_TCR_Experiment challengeThenCollection = pure true := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [show (simulateQ (SM_DT_TCR_oracles problem .only) challengeThenCollection.choose).run
      ([], []) = pure (none, ([(false, false)], [])) from rfl]
  rfl

/-- The converted adversary wins the source-final-validity game: the wrapper suppresses the
poisoning collection query, so the monitor is still valid at the end and the forgery counts. The
same transcript run naively against the monitor loses — that is what the conversion repairs. -/
theorem toSourceFinalValidity_suppresses_poison_canary :
    SM_DT_TCR_SourceFinalValidity.Experiment
        challengeThenCollection.toSourceFinalValidity = pure true := by
  rw [SM_DT_TCR_experiment_toSourceFinalValidity, experiment_challengeThenCollection]

/-- The conversion is advantage-preserving on this adversary, at advantage one. -/
theorem advantage_challengeThenCollection_canary :
    SM_DT_TCR_Advantage challengeThenCollection = 1 ∧
      SM_DT_TCR_SourceFinalValidity.Advantage
        challengeThenCollection.toSourceFinalValidity = 1 := by
  refine ⟨?_, ?_⟩ <;>
    simp [SM_DT_TCR_Advantage, SM_DT_TCR_SourceFinalValidity.Advantage,
      experiment_challengeThenCollection, toSourceFinalValidity_suppresses_poison_canary]

/-! ## SM-DT-PRE

The same transcript at the game whose challenge oracle draws its own message. `M'` is a one-element
subspace so the draw is deterministic and the run reduces. -/

inductive Input
  | only

instance : SampleableType Input where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_input : ($ᵗ Input : ProbComp Input) = pure .only := rfl

def preProblem : SM_DT_PRE_Problem Unit Seed Bool Bool Input Bool where
  th := hash
  emb := fun _ => false
  emb_injective a b _ := by cases a; cases b; rfl
  thColl := collection
  numTargets := 1

@[simp] lemma preProblem_seedGen : preProblem.th.seedGen = pure .only := rfl

abbrev PreSpecs := unifSpec + (SM_DT_PRE_challengeSpec Bool Bool +
  collectionSpec preProblem.thColl)

def preChallenge (t : Bool) : OracleComp PreSpecs (Option Bool) :=
  liftM (PreSpecs.query (.inr (.inl t)))

def preCollectionQuery (t : Bool) (m : preProblem.thColl.Msg ()) :
    OracleComp PreSpecs (Option Bool) :=
  liftM (PreSpecs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, then clash with it on the collection oracle. -/
def preChallengeThenCollection : SM_DT_PRE_Adversary preProblem where
  State := Option Bool
  choose := do
    let _ ← preChallenge false
    preCollectionQuery false false
  invert answer _ := match answer with
    | none => pure (0, .only)
    | some _ => pure (1, .only)

/-- End-to-end SM-PRE: the clash is refused, and the inversion at the recorded target wins. -/
theorem pre_experiment_challengeThenCollection :
    SM_DT_PRE_Experiment preChallengeThenCollection = pure true := by
  simp only [SM_DT_PRE_Experiment, preProblem_seedGen, pure_bind]
  rw [show (simulateQ (SM_DT_PRE_oracles preProblem .only) preChallengeThenCollection.choose).run
      ([], []) = pure (none, ([(false, Input.only)], [])) from rfl]
  rfl

/-- The SM-PRE conversion carries that win across to the monitor game. -/
theorem pre_toSourceFinalValidity_suppresses_poison_canary :
    SM_DT_PRE_SourceFinalValidity.Experiment
        preChallengeThenCollection.toSourceFinalValidity = pure true := by
  rw [SM_DT_PRE_experiment_toSourceFinalValidity, pre_experiment_challengeThenCollection]

end ToFinalValidityTest
