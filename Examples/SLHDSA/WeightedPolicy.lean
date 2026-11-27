/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.ScalarPolicy

/-! # Input-sensitive scalar budgets of one shared counted experiment -/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.WeightedPolicy

/-- Signing-attempt and ambient phase/input events for the declared oracle output type. -/
abbrev Event (Output : Type) := ScalarPolicy.Event Output

/-- The candidate, raw signing log, verifier result and accumulated cost. -/
abbrev Observed (C : Type) := SigningView.Observation Message Bytes (Option Bytes) C

/-- Every signing attempt costs one; selected public hashes include raw byte input length. -/
@[expose] def policy {Output : Type} : Event Output → Nat
  | .signingAttempt _ => 1
  | .ambient .adversary (.inr input) => 1 + input.length
  | .ambient .verification (.inr input) => 1 + input.length
  | .ambient _ _ => 0

/-- Run a supplied scheme and adversary with the byte-sensitive scalar policy. -/
@[expose] def experiment {Output PK SK : Type} (scheme : Game.ExternalScheme Output PK SK)
    (adv : Game.Adversary Output PK) : OracleComp (Game.World Output) (Observed Nat) :=
  SigningView.countedExperiment policy (externalView scheme) (externalMain adv)

/-- Interpret the byte-sensitive experiment in the empty-cache shared random-oracle model. -/
@[expose] noncomputable def run {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adv : Game.Adversary Output PK) :
    ProbComp (Observed Nat) := RandomOracleModel.run (experiment scheme adv)

/-- The byte-sensitive policy dominates every original selected source charge. -/
theorem policy_domination {Output : Type} (event : Event Output) :
    ScalarPolicy.selectedWork (sourcePolicy event) ≤ policy event := by
  cases event with
  | signingAttempt request =>
    simp [ScalarPolicy.selectedWork, Game.adversaryWork, sourcePolicy, policy]
  | ambient phase input =>
    cases phase <;> cases input <;>
      simp [ScalarPolicy.selectedWork, Game.adversaryWork, sourcePolicy, sourceKind,
        Game.hashCost, RandomOracleModel.hashCost, policy]

/-- A zero-charge policy cannot dominate the original signing-attempt charge. -/
theorem zero_policy_not_dominate {Output : Type} :
    ¬ ∀ event : Event Output, ScalarPolicy.selectedWork (sourcePolicy event) ≤
      (fun _ : Event Output => (0 : Nat)) event := by
  intro hdom
  have hsign := hdom (.signingAttempt ⟨[], []⟩)
  simp [ScalarPolicy.selectedWork, Game.adversaryWork, sourcePolicy] at hsign

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.WeightedPolicy
