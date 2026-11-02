/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.CostMap
public import Mathlib.Algebra.FreeMonoid.Basic
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint

/-! # Declared scalar budgets of one shared counted experiment -/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.ScalarPolicy

/-- Signing attempts and ambient queries at their actual phase and input. -/
abbrev Event (Output : Type) := SigningView.Event (Game.World Output) Message

/-- The candidate, raw signing log, verifier result and accumulated cost. -/
abbrev Observed (C : Type) := SigningView.Observation Message Bytes (Option Bytes) C

/-- Map accumulated cost while retaining the complete signature-experiment outcome. -/
@[expose] def mapObserved {C D : Type} (f : C → D) (observed : Observed C) : Observed D :=
  { toOutcome := observed.toOutcome, cost := f observed.cost }

/-- Run the supplied scheme and adversary with the declared scalar event costs. -/
@[expose] def experiment {Output PK SK : Type} (policy : Event Output → Nat)
    (scheme : Game.ExternalScheme Output PK SK) (adv : Game.Adversary Output PK) :
    OracleComp (Game.World Output) (Observed Nat) :=
  SigningView.countedExperiment policy (externalView scheme) (externalMain adv)

/-- Interpret the scalar-cost experiment in the empty-cache shared random-oracle model. -/
@[expose] noncomputable def run {Output PK SK : Type} [SampleableType Output]
    (policy : Event Output → Nat) (scheme : Game.ExternalScheme Output PK SK)
    (adv : Game.Adversary Output PK) :
    ProbComp (Observed Nat) := RandomOracleModel.run (experiment policy scheme adv)

/-- Sum signing attempts, direct adversary hashes and final-verification hashes. -/
@[expose] def selectedWork (counts : SourceCounts) : Nat := ∑ kind ∈ Game.adversaryWork, counts kind

/-- Pair each event's original source charges with its declared scalar charge. -/
@[expose] def jointPolicy {Output : Type} (policy : Event Output → Nat) (event : Event Output) :
    SourceCounts × Nat :=
  (sourcePolicy event, policy event)

/-- Observe the full source vector and scalar cost on one complete execution. -/
@[expose] def jointExperiment {Output PK SK : Type} (policy : Event Output → Nat)
    (scheme : Game.ExternalScheme Output PK SK) (adv : Game.Adversary Output PK) :
    OracleComp (Game.World Output) (Observed (SourceCounts × Nat)) :=
  SigningView.countedExperiment (jointPolicy policy) (externalView scheme)
      (externalMain adv)

/-- Record one event as a singleton chronological event word. -/
@[expose] def wordPolicy {Output : Type} (event : Event Output) : FreeAddMonoid (Event Output) :=
  FreeAddMonoid.of event

/-- Fold a chronological event word into its full source counts and scalar cost. -/
@[expose] def jointFold {Output : Type} (policy : Event Output → Nat) :
    FreeAddMonoid (Event Output) →+ (SourceCounts × Nat) :=
  FreeAddMonoid.lift (jointPolicy policy)

private theorem selectedWork_add (left right : SourceCounts) :
    selectedWork (left + right) = selectedWork left + selectedWork right := by
  simp only [selectedWork, Pi.add_apply, Finset.sum_add_distrib]

/-- Every actual event word dominates selected work, independently of its feasibility. -/
theorem word_domination {Output : Type} (policy : Event Output → Nat)
    (hdom : ∀ event, selectedWork (sourcePolicy event) ≤ policy event)
    (word : FreeAddMonoid (Event Output)) :
    selectedWork (jointFold policy word).1 ≤ (jointFold policy word).2 := by
  refine FreeAddMonoid.recOn word ?_ (fun event rest ih => ?_)
  · simp [jointFold, selectedWork]
  · rw [map_add]
    change selectedWork
      ((jointFold policy (FreeAddMonoid.of event)).1 + (jointFold policy rest).1) ≤
      (jointFold policy (FreeAddMonoid.of event)).2 + (jointFold policy rest).2
    rw [selectedWork_add]
    exact Nat.add_le_add (hdom event) ih

/-- The paired source/scalar observation is the fold of the actual chronological events. -/
theorem word_joint_projection {Output PK SK : Type}
    (policy : Event Output → Nat) (scheme : Game.ExternalScheme Output PK SK)
    (adv : Game.Adversary Output PK) :
    mapObserved (jointFold policy) <$>
      SigningView.countedExperiment wordPolicy (externalView scheme) (externalMain adv) =
        jointExperiment policy scheme adv := by
  have mapped := SigningView.countedExperiment_mapCost (jointFold (Output := Output) policy)
    (wordPolicy (Output := Output)) (externalView scheme) (externalMain adv)
  have policies : (fun event : Event Output => jointFold policy (wordPolicy event)) =
      jointPolicy policy := by
    funext event
    exact FreeAddMonoid.lift_eval_of (jointPolicy policy) event
  rw [policies] at mapped
  exact mapped

/-- Original counts and scalar work are complete projections of a single paired execution. -/
theorem joint_projections {Output PK SK : Type}
    (policy : Event Output → Nat) (scheme : Game.ExternalScheme Output PK SK)
    (adv : Game.Adversary Output PK) :
    (mapObserved Prod.fst <$> jointExperiment policy scheme adv = canonicalExperiment scheme adv) ∧
    (mapObserved Prod.snd <$> jointExperiment policy scheme adv =
      experiment policy scheme adv) := by
  constructor
  · exact SigningView.countedExperiment_mapCost
      (AddMonoidHom.fst SourceCounts Nat) (jointPolicy policy) (externalView scheme)
      (externalMain adv)
  · exact SigningView.countedExperiment_mapCost
      (AddMonoidHom.snd SourceCounts Nat) (jointPolicy policy) (externalView scheme)
      (externalMain adv)

/-- The actual result and final cache remain together through every continuation. -/
theorem word_joint_run_bind {Output PK SK Cache β : Type} {m : Type → Type*}
    [Monad m] [LawfulMonad m] (policy : Event Output → Nat)
    (scheme : Game.ExternalScheme Output PK SK) (adv : Game.Adversary Output PK)
    (handler : QueryImpl (Game.World Output) (StateT Cache m)) (initial : Cache)
    (next : Observed (SourceCounts × Nat) × Cache → m β) :
    ((simulateQ handler
      (SigningView.countedExperiment wordPolicy (externalView scheme) (externalMain adv))).run
        initial >>= fun result => next (mapObserved (jointFold policy) result.1, result.2)) =
      ((simulateQ handler (jointExperiment policy scheme adv)).run initial >>= next) := by
  have equality := congrArg (fun program => (simulateQ handler program).run initial)
    (word_joint_projection policy scheme adv)
  simp only [simulateQ_map, StateT.run_map] at equality
  have continued := congrArg (fun program => program >>= next) equality
  simpa only [bind_map_left] using continued

/-- Selected work is bounded by weighted work on the same actual joint execution. -/
theorem selectedWork_le_cost {Output PK SK Cache : Type}
    (policy : Event Output → Nat)
    (hdom : ∀ event, selectedWork (sourcePolicy event) ≤ policy event)
    (scheme : Game.ExternalScheme Output PK SK) (adv : Game.Adversary Output PK)
    (handler : QueryImpl (Game.World Output) (StateT Cache ProbComp)) (initial : Cache)
    (result : Observed (SourceCounts × Nat) × Cache)
    (hsupport :
      result ∈ support ((simulateQ handler (jointExperiment policy scheme adv)).run initial)) :
    selectedWork result.1.cost.1 ≤ result.1.cost.2 := by
  rw [← word_joint_projection policy scheme adv, simulateQ_map, StateT.run_map, support_map]
    at hsupport
  rcases hsupport with ⟨wordResult, _, rfl⟩
  exact word_domination policy hdom wordResult.1.cost

private theorem run_map {Output α β : Type} [SampleableType Output]
    (f : α → β) (program : OracleComp (Game.World Output) α) :
    RandomOracleModel.run (f <$> program) = f <$> RandomOracleModel.run program := by
  simp only [RandomOracleModel.run, simulateQ_map, StateT.run'_map']

open scoped Classical in
/-- A probability-one weighted cap transports the original joint budget at the same cap. -/
theorem cap_transport {Output PK SK : Type} [SampleableType Output]
    (policy : Event Output → Nat)
    (hdom : ∀ event, selectedWork (sourcePolicy event) ≤ policy event)
    (scheme : Game.ExternalScheme Output PK SK) (adv : Game.Adversary Output PK) (q : Nat)
    (hcap : Pr{let observed ← run policy scheme adv}[observed.cost ≤ q] = 1) :
    (observedGame scheme).HasQueryBound () Game.adversaryWork adv q := by
  have pairedCap : Pr{let observed ← RandomOracleModel.run (jointExperiment policy scheme adv)}[
      observed.cost.2 ≤ q] = 1 := by
    rw [run, ← (joint_projections policy scheme adv).2, run_map] at hcap
    simpa only [prEvent_map, mapObserved] using hcap
  have pairedSelected :
      Pr{let observed ← RandomOracleModel.run (jointExperiment policy scheme adv)}[
        selectedWork observed.cost.1 ≤ q] = 1 := by
    have implication :
        ∀ observed ∈ support (RandomOracleModel.run (jointExperiment policy scheme adv)),
        observed.cost.2 ≤ q → selectedWork observed.cost.1 ≤ q := by
      intro observed hobs hcost
      rw [← word_joint_projection policy scheme adv, run_map, support_map] at hobs
      rcases hobs with ⟨wordResult, _, rfl⟩
      exact (word_domination policy hdom wordResult.cost).trans hcost
    apply le_antisymm (prEvent_le_one _)
    rw [← pairedCap]
    exact prEvent_mono_of_support _ _ _ implication
  change Pr{let result ← (observedGame scheme).experiment () adv}[
    selectedWork result.2 ≤ q] = 1
  change Pr{let result ← (fun observed =>
    (decide (SigningView.Wins id observed.toOutcome), observed.cost)) <$>
      RandomOracleModel.run (canonicalExperiment scheme adv)}[selectedWork result.2 ≤ q] = 1
  rw [← (joint_projections policy scheme adv).1, run_map]
  simpa only [prEvent_map, mapObserved] using pairedSelected

/-- Weighted observation retains the original success event with no resource premise. -/
theorem success_probability {Output PK SK : Type} [SampleableType Output]
    (policy : Event Output → Nat) (scheme : Game.ExternalScheme Output PK SK)
    (adv : Game.Adversary Output PK) :
    Pr{let observed ← run policy scheme adv}[SigningView.Wins id observed.toOutcome] =
      (observedGame scheme).advantage () adv := by
  have erasure := SigningView.countedExperiment_policy_erasure policy sourcePolicy
    (externalView scheme) (externalMain adv)
  have equality := congrArg RandomOracleModel.run erasure
  rw [run_map, run_map] at equality
  have events := congrArg (fun program =>
    Pr{let outcome ← program}[SigningView.Wins id outcome]) equality
  simpa only [run, experiment, canonicalExperiment, SecurityGame.advantage, observedGame,
    prEvent_map, SigningView.erase, decide_eq_true_eq] using events

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.ScalarPolicy
