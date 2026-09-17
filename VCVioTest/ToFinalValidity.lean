/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.ToFinalValidity

/-!
# Tweak-discipline bridge canaries

One transcript separates the two presentations: take a target, then query the collection oracle at
that same tweak. The rejection-on-arrival oracles refuse the second query and leave the state
untouched, so the earlier target is still there to be used and the adversary **wins**. The monitor
answers that query and poisons final validity, so the same transcript run naively **loses** — the
sibling test modules for the two families pin both outcomes, and both are correct for their own
game.

This file pins that the conversion resolves the disagreement in the winning direction for
SM-DT-TCR and SM-DT-PRE. The wrapper declines to forward the poisoning query and synthesises
the `none` its counterpart received, so the converted adversary wins where the naive one would not.
A conversion that merely renamed the phases would inherit the losing outcome.

Every fixture is chosen so the experiments reduce to a closed `pure`: the seed type and the
SM-PRE message subspace are one-element. The SM-TCR challenge oracle draws nothing.
-/

public section

open OracleComp OracleSpec TweakableHash

namespace ToFinalValidityTest

/-! ## Shared fixtures -/

inductive Seed
  | only

instance : Unique Seed where
  default := .only
  uniq x := by cases x; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

inductive Input
  | only

instance : Unique Input where
  default := .only
  uniq x := by cases x; rfl

@[simp] lemma uniformSample_input : ($ᵗ Input : ProbComp Input) = pure .only := rfl

/-- A constant tweakable hash. Every message collides at every tweak, so the adversary wins exactly
when the game lets it keep its target. -/
@[expose] def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

@[expose] def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ _ := false

/-! ## SM-DT-TCR -/

@[expose] def problem : SM_DT_TCR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec + (SM_DT_TCR_challengeSpec Bool Bool Bool +
  collectionSpec problem.thColl)

@[expose] def challenge (tm : Bool × Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl tm)))

@[expose] def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) :
    OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, then query the collection at that same tweak. The rejection-on-arrival oracles
refuse the second query, and the adversary branches on that refusal to forge against the target it
already holds. -/
@[expose] def challengeThenCollection : SM_DT_TCR_Adversary problem where
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
poisoning collection query, so the monitor is still valid at the end and the collision counts. -/
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

The same transcript at the game whose challenge oracle draws its own message, over a one-element
subspace so the draw reduces. -/

@[expose] def preProblem : SM_DT_PRE_Problem Unit Seed Bool Bool Input Bool where
  th := hash
  emb := fun _ => false
  emb_injective a b _ := by cases a; cases b; rfl
  thColl := collection
  numTargets := 1

@[simp] lemma preProblem_seedGen : preProblem.th.seedGen = pure .only := rfl

abbrev PreSpecs := unifSpec + (SM_DT_PRE_challengeSpec Bool Bool +
  collectionSpec preProblem.thColl)

@[expose] def preChallenge (t : Bool) : OracleComp PreSpecs (Option Bool) :=
  liftM (PreSpecs.query (.inr (.inl t)))

@[expose] def preCollectionQuery (t : Bool) (m : preProblem.thColl.Msg ()) :
    OracleComp PreSpecs (Option Bool) :=
  liftM (PreSpecs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, then clash with it on the collection oracle. -/
@[expose] def preChallengeThenCollection : SM_DT_PRE_Adversary preProblem where
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
