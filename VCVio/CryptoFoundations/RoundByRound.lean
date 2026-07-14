/-
Copyright (c) 2026 Aristotle (Harmonic), Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Round-indexed event games

This module packages a family of probabilistic events indexed by rounds, with a potentially
different type of execution context at each round. Each event is exposed as a failure-based
`SecExp`, and `experiment_advantage` identifies its advantage with the probability of that event.
`IsBounded` states a separate error bound for each round.

`KnowledgeTransitionFamily` specializes this interface to the event that a fresh challenge changes
a knowledge-state predicate from false to true. This layer does not impose protocol-specific laws or
computational restrictions; those and any admissibility conditions belong in downstream adapters.

`KnowledgeExtractionFamily` gives the extensional clauses of generalized round-by-round knowledge
from Block, Garreta, Tiwari, and Zajac, *On Soundness Notions for Interactive Oracle Proofs*,
Definition 4.2. Its transcript context and prover message are fixed before sampling a fresh uniform
challenge. The API records the initial and terminal doomed-state conditions separately from the
extraction condition. It does not encode polynomial-time computability.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace RoundByRound

universe u v

/-- A family of probabilistic events whose execution-context type may depend on the round. -/
structure GameFamily (Round : Type u) (Context : Round → Type v) where
  /-- Results sampled in each round. -/
  Result : Round → Type
  /-- Distribution of the result for a context and round. -/
  sample : (round : Round) → Context round → ProbComp (Result round)
  /-- The event measured in a context and round. -/
  event : (round : Round) → Context round → Result round → Prop

namespace GameFamily

variable {Round : Type u} {Context : Round → Type v}

/-- The failure-based experiment that succeeds exactly when the indexed event occurs. -/
def experiment (games : GameFamily Round Context)
    (round : Round) (context : Context round) : SecExp (OptionT ProbComp) := by
  classical
  exact
    { toSPMFSemantics := SPMFSemantics.ofMonadLift (OptionT ProbComp)
      main := do
        let result ← OptionT.lift (games.sample round context)
        guard (games.event round context result) }

/-- The advantage of the indexed experiment is the probability of its event. -/
@[simp]
theorem experiment_advantage (games : GameFamily Round Context)
    (round : Round) (context : Context round) :
    (games.experiment round context).advantage =
      Pr[games.event round context | games.sample round context] := by
  classical
  change 1 - Pr[⊥ | (games.experiment round context).main] = _
  rw [← probEvent_True_eq_sub]
  change Pr[fun _ ↦ True | (do
    let result ← OptionT.lift (games.sample round context)
    guard (games.event round context result) : OptionT ProbComp Unit)] = _
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun result ↦ ?_
  by_cases h : games.event round context result <;> simp [h]

/-- Every indexed experiment has advantage at most its round's error bound.

The quantifier ranges over every round and every context at that round; use a subtype when only an
admissible class of contexts should be considered. -/
def IsBounded (games : GameFamily Round Context) (error : Round → ℝ≥0∞) : Prop :=
  ∀ round (context : Context round), (games.experiment round context).advantage ≤ error round

/-- Event-probability characterization of a bounded game family. -/
theorem isBounded_iff (games : GameFamily Round Context) (error : Round → ℝ≥0∞) :
    games.IsBounded error ↔
      ∀ round (context : Context round),
        Pr[games.event round context | games.sample round context] ≤ error round := by
  simp only [IsBounded, experiment_advantage]

end GameFamily

/-- Data defining a family of knowledge-transition events.

The context at a round is fixed before `sampleChallenge` draws the fresh challenge. The two witness
types represent knowledge immediately before and after that challenge. -/
structure KnowledgeTransitionFamily (Round : Type u) (Context : Round → Type v) where
  /-- Challenges sampled at each round. -/
  Challenge : Round → Type
  /-- Witnesses for the state immediately before each challenge. -/
  WitnessBefore : Round → Type
  /-- Witnesses for the state immediately after each challenge. -/
  WitnessAfter : Round → Type
  /-- Distribution of the fresh challenge at each round. -/
  sampleChallenge : (round : Round) → ProbComp (Challenge round)
  /-- Extracts a pre-challenge witness from a challenge and post-challenge witness. -/
  extractBefore : (round : Round) →
    Context round → Challenge round → WitnessAfter round → WitnessBefore round
  /-- Knowledge-state predicate immediately before the challenge. -/
  preState : (round : Round) → Context round → WitnessBefore round → Prop
  /-- Knowledge-state predicate immediately after the challenge. -/
  postState : (round : Round) →
    Context round → Challenge round → WitnessAfter round → Prop

namespace KnowledgeTransitionFamily

variable {Round : Type u} {Context : Round → Type v}

/-- The event that some post-challenge witness has a true post-state while its extracted
pre-challenge witness has a false pre-state. -/
def badEvent (games : KnowledgeTransitionFamily Round Context)
    (round : Round) (context : Context round) (challenge : games.Challenge round) : Prop :=
  ∃ witnessAfter,
    ¬ games.preState round context
        (games.extractBefore round context challenge witnessAfter) ∧
      games.postState round context challenge witnessAfter

/-- The generic event-game family associated to a knowledge-transition family. -/
def toGameFamily (games : KnowledgeTransitionFamily Round Context) : GameFamily Round Context where
  Result := games.Challenge
  sample := fun round _ ↦ games.sampleChallenge round
  event := games.badEvent

/-- The failure-based experiment for a bad knowledge transition. -/
def experiment (games : KnowledgeTransitionFamily Round Context)
    (round : Round) (context : Context round) : SecExp (OptionT ProbComp) :=
  games.toGameFamily.experiment round context

/-- The advantage of the transition experiment is the probability of a bad transition. -/
@[simp]
theorem experiment_advantage (games : KnowledgeTransitionFamily Round Context)
    (round : Round) (context : Context round) :
    (games.experiment round context).advantage =
      Pr[games.badEvent round context | games.sampleChallenge round] := by
  simp [experiment, toGameFamily]

/-- Every bad-transition experiment has advantage at most its round's error bound. -/
def IsBounded (games : KnowledgeTransitionFamily Round Context)
    (error : Round → ℝ≥0∞) : Prop :=
  games.toGameFamily.IsBounded error

/-- Bad-transition probability characterization of a bounded transition family. -/
theorem isBounded_iff (games : KnowledgeTransitionFamily Round Context)
    (error : Round → ℝ≥0∞) :
    games.IsBounded error ↔
      ∀ round (context : Context round),
        Pr[games.badEvent round context | games.sampleChallenge round] ≤ error round := by
  simp [IsBounded, GameFamily.isBounded_iff, toGameFamily]

end KnowledgeTransitionFamily

/-! ## Source-shaped knowledge extraction -/

/-- Data defining the extensional clauses of generalized round-by-round knowledge extraction.

`Context` is a single family of statement-and-transcript states indexed by the stages from zero
through `rounds`. `extend` appends the prover message and verifier challenge of one interaction
round while preserving the projected statement. The sole `doomed` predicate therefore applies
uniformly to the initial and terminal stages and every stage between them.

At a fixed round, the pre-message context and prover message are fixed before the verifier samples
a fresh uniform challenge. The doomed predicate does not depend on a witness; `extract` directly
returns the candidate witness required by `ExtractionCondition`. -/
structure KnowledgeExtractionFamily (rounds : ℕ) where
  /-- Statements proved by the protocol. -/
  Statement : Type
  /-- Witnesses for the protocol's fixed relation. -/
  Witness : Type
  /-- Statement-and-transcript contexts at every protocol stage. -/
  Context : Fin (rounds + 1) → Type
  /-- Prover messages fixed before the verifier samples the challenge at each round. -/
  Message : Fin rounds → Type
  /-- Fresh verifier challenges at each round. -/
  Challenge : Fin rounds → Type
  /-- Final prover messages supplied after all interaction rounds. -/
  FinalMessage : Type
  /-- Canonical uniform-sampling data for each verifier challenge type. -/
  challengeSampleable : (round : Fin rounds) → SampleableType (Challenge round)
  /-- Projects the common statement from a context at any stage. -/
  statement : (stage : Fin (rounds + 1)) → Context stage → Statement
  /-- The protocol context containing only the input statement. -/
  initialContext : Statement → Context 0
  /-- Appends the prover message and verifier challenge of an interaction round. -/
  extend : (round : Fin rounds) →
    Context round.castSucc → Message round → Challenge round → Context round.succ
  /-- The initial context projects to the statement used to construct it. -/
  statement_initial (input : Statement) : statement 0 (initialContext input) = input
  /-- Extending a context by one interaction round preserves its statement. -/
  statement_extend (round : Fin rounds) (context : Context round.castSucc)
      (message : Message round) (challenge : Challenge round) :
    statement round.succ (extend round context message challenge) =
      statement round.castSucc context
  /-- The single doomed-set predicate on stage-indexed contexts. -/
  doomed : (stage : Fin (rounds + 1)) → Context stage → Prop
  /-- Extracts a candidate witness from the transcript through the fixed prover message. -/
  extract : (round : Fin rounds) → Context round.castSucc → Message round → Witness
  /-- The fixed statement-witness relation proved by the protocol. -/
  relation : Statement → Witness → Prop
  /-- Whether the verifier rejects after a terminal context and final prover message. -/
  rejects : Context (Fin.last rounds) → FinalMessage → Prop

namespace KnowledgeExtractionFamily

variable {rounds : ℕ}

/-- Canonical uniform sampling of the fresh verifier challenge at a round. -/
def sampleChallenge (games : KnowledgeExtractionFamily rounds)
    (round : Fin rounds) : ProbComp (games.Challenge round) :=
  letI := games.challengeSampleable round
  uniformSample (games.Challenge round)

/-- The event that the fresh challenge escapes the doomed set. -/
def escapeEvent (games : KnowledgeExtractionFamily rounds)
    (round : Fin rounds) (context : games.Context round.castSucc)
    (message : games.Message round)
    (challenge : games.Challenge round) : Prop :=
  ¬games.doomed round.succ (games.extend round context message challenge)

/-- The generic event-game family for escape from the doomed set after a fixed prover message. -/
def toGameFamily (games : KnowledgeExtractionFamily rounds) :
    GameFamily (Fin rounds)
      (fun round ↦ games.Context round.castSucc × games.Message round) where
  Result := games.Challenge
  sample := fun round _ ↦ games.sampleChallenge round
  event := fun round contextAndMessage ↦
    games.escapeEvent round contextAndMessage.1 contextAndMessage.2

/-- The failure-based experiment for escape from the doomed set after a fixed prover message. -/
def experiment (games : KnowledgeExtractionFamily rounds)
    (round : Fin rounds) (context : games.Context round.castSucc)
    (message : games.Message round) :
    SecExp (OptionT ProbComp) :=
  games.toGameFamily.experiment round (context, message)

/-- The advantage of the extraction experiment is the probability of escaping the doomed set. -/
@[simp]
theorem experiment_advantage (games : KnowledgeExtractionFamily rounds)
    (round : Fin rounds) (context : games.Context round.castSucc)
    (message : games.Message round) :
    (games.experiment round context message).advantage =
      Pr[games.escapeEvent round context message | games.sampleChallenge round] := by
  simp [experiment, toGameFamily]

/-- Every protocol state is doomed before the first interaction round. -/
def InitialCondition (games : KnowledgeExtractionFamily rounds) : Prop :=
  ∀ input, games.doomed 0 (games.initialContext input)

/-- Every final prover message is rejected from a doomed terminal context. -/
def TerminalCondition (games : KnowledgeExtractionFamily rounds) : Prop :=
  ∀ (context : games.Context (Fin.last rounds)) (message : games.FinalMessage),
    games.doomed (Fin.last rounds) context → games.rejects context message

/-- The extensional extraction clause with a separate error for each round.

For every fixed context and prover message whose preceding state is doomed, an escape probability
strictly greater than the round's error requires the directly extracted witness to be valid. -/
def ExtractionCondition (games : KnowledgeExtractionFamily rounds)
    (error : Fin rounds → ℝ≥0∞) : Prop :=
  ∀ round (context : games.Context round.castSucc) (message : games.Message round),
    games.doomed round.castSucc context →
      error round < Pr[games.escapeEvent round context message | games.sampleChallenge round] →
        games.relation (games.statement round.castSucc context)
          (games.extract round context message)

/-- The extensional initial, terminal, and extraction conditions.

This predicate deliberately omits the polynomial-time requirement on the extractor and asymptotic
negligibility of the error family, so it does not by itself assert the full computational notion. -/
def ExtensionalConditions (games : KnowledgeExtractionFamily rounds)
    (error : Fin rounds → ℝ≥0∞) : Prop :=
  games.InitialCondition ∧ games.TerminalCondition ∧ games.ExtractionCondition error

end KnowledgeExtractionFamily

end RoundByRound
