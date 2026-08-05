/-
Copyright (c) 2026 Aristotle (Harmonic), Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

module

public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.Constructions.SampleableType

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
from Block, Garreta, Tiwari, and Zając, *On Soundness Notions for Interactive Oracle Proofs*
(Cryptology ePrint Archive 2023/1256), generalized RBR knowledge, Definition 3.12. The protocol
model is strictly alternating: at every interaction round the prover sends one message and the
verifier then samples one fresh uniform challenge, so a partial transcript is
`(m₁, c₁, …, m_i, c_i)`. Schedules that are not message/challenge alternating (for example two
consecutive prover messages, or a challenge-first round) are represented in this model by padding
the appropriate message or challenge type with `Unit`; this is a faithful encoding, not a claim
that arbitrary scheduling has been added. Its transcript context and prover message are fixed
before sampling a fresh uniform challenge. The API records the all-inputs initial doomed condition
and the terminal doomed-implies-rejection condition separately from the strict extraction
condition.

This layer is **extensional**: `extract` is data returning a candidate witness and
`ExtractionCondition` only asserts that this witness is valid whenever the strict escape trigger
`error < Pr[escape]` fires. It is therefore the soundness-strength/existence content of Definition
3.12, **not** the paper's full computational round-by-round knowledge claim; it carries no security
parameter, encoding, runtime bound, or polynomial-time predicate on the extractor.

TODO: the deferred computational layer needs a security-indexed family of encoded polynomial-time
extractors together with negligible per-round error, and lives behind the separate polytime
framework. This module deliberately does not add that layer or depend on an unmerged branch.
-/

@[expose] public section

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
    (round : Round) (context : Context round) : SecExp (OptionT ProbComp) :=
  letI : DecidablePred (games.event round context) := fun _ => Classical.propDecidable _
  { toSPMFSemantics := SPMFSemantics.ofMonadLift (OptionT ProbComp)
    main := do
      let result ← games.sample round context
      guard (games.event round context result) }

/-- The advantage of the indexed experiment is the probability of its event. -/
@[simp]
theorem experiment_advantage (games : GameFamily Round Context)
    (round : Round) (context : Context round) :
    (games.experiment round context).advantage =
      Pr[games.event round context | games.sample round context] := by
  classical
  calc (games.experiment round context).advantage
      = 1 - Pr[⊥ | (games.experiment round context).main] := by
        simp only [SecExp.advantage]
        exact congrArg (1 - ·) (SPMFSemantics.ofMonadLift_probFailure _)
    _ = Pr[= () | (games.experiment round context).main] :=
        probOutput_punit_eq_sub_probFailure.symm
    _ = Pr[games.event round context | games.sample round context] :=
        probOutput_bind_guard_eq_probEvent _ _

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
  /-- A total candidate-witness extractor from the transcript through the fixed prover message.
  Storing a *total* function here is a representational totalization: the source definition permits
  the extractor to fail off-trigger, and `ExtractionCondition` requires this output to satisfy the
  relation only when the strict escape trigger `error < Pr[escape]` fires. This field is therefore
  not by itself the paper's polynomial-time extractor. -/
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

/-- Every input's canonical initial context is doomed: for every possible input, the context that
contains only that input lies in the doomed set. This is the all-inputs initial clause of
generalized round-by-round knowledge (Definition 3.12); it strengthens the initial clause of
generalized round-by-round soundness, which only requires doom when the statement is false. -/
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

/-! ## Bridge to the generic knowledge-transition family

For each round we restrict a `KnowledgeTransitionFamily` to the subtype of fixed
`(context, message)` pairs whose pre-message context is doomed. The pre-state is validity of the
directly extracted witness, the post-state is escape from the doomed set after that fixed message
and the fresh challenge, and the after-witness is `Unit`. The transition bad event is then,
challenge by challenge, the conjunction of a failed extracted relation with escape, so the
transition family is bounded by the per-round error exactly when the strict extraction trigger
holds. -/

/-- Fixed `(context, message)` pairs at a round whose pre-message context is doomed. -/
@[reducible] def DoomedContext (games : KnowledgeExtractionFamily rounds) (round : Fin rounds) :
    Type :=
  {cm : games.Context round.castSucc × games.Message round // games.doomed round.castSucc cm.1}

/-- The knowledge-transition family carried by a knowledge-extraction family, on the doomed subtype
of fixed `(context, message)` pairs.

The challenge sampler is the existing `sampleChallenge`; `WitnessBefore` is the protocol witness
type; `WitnessAfter` is `Unit`; the pre-witness ignores that unit and is the existing
`extract round context message`; the pre-state says this extracted witness satisfies the relation
at the statement projected from the context; and the post-state is exactly the escape event for the
fixed context/message and the fresh challenge. -/
def toKnowledgeTransitionFamily (games : KnowledgeExtractionFamily rounds) :
    KnowledgeTransitionFamily (Fin rounds) games.DoomedContext where
  Challenge := games.Challenge
  WitnessBefore := fun _ => games.Witness
  WitnessAfter := fun _ => Unit
  sampleChallenge := games.sampleChallenge
  extractBefore := fun round cm _ _ => games.extract round cm.val.1 cm.val.2
  preState := fun round cm witnessBefore =>
    games.relation (games.statement round.castSucc cm.val.1) witnessBefore
  postState := fun round cm challenge _ =>
    games.escapeEvent round cm.val.1 cm.val.2 challenge

/-- On the doomed subtype, the transition bad event is, challenge by challenge, the conjunction of
a failed extracted relation with escape from the doomed set. -/
lemma toKnowledgeTransitionFamily_badEvent_iff (games : KnowledgeExtractionFamily rounds)
    (round : Fin rounds) (context : games.Context round.castSucc) (message : games.Message round)
    (hdoomed : games.doomed round.castSucc context) (challenge : games.Challenge round) :
    games.toKnowledgeTransitionFamily.badEvent round ⟨(context, message), hdoomed⟩ challenge ↔
      (¬ games.relation (games.statement round.castSucc context)
            (games.extract round context message)
        ∧ games.escapeEvent round context message challenge) := by
  constructor
  · rintro ⟨_, hnr, hesc⟩; exact ⟨hnr, hesc⟩
  · rintro ⟨hnr, hesc⟩; exact ⟨(), hnr, hesc⟩

/-- When the directly extracted witness fails the relation, the transition bad-event probability on
the doomed subtype is exactly the escape probability. -/
lemma probEvent_toKnowledgeTransitionFamily_badEvent_of_not_relation
    (games : KnowledgeExtractionFamily rounds) (round : Fin rounds)
    (context : games.Context round.castSucc) (message : games.Message round)
    (hdoomed : games.doomed round.castSucc context)
    (hrel : ¬ games.relation (games.statement round.castSucc context)
        (games.extract round context message)) :
    Pr[games.toKnowledgeTransitionFamily.badEvent round ⟨(context, message), hdoomed⟩
        | games.toKnowledgeTransitionFamily.sampleChallenge round] =
      Pr[games.escapeEvent round context message | games.sampleChallenge round] := by
  refine probEvent_ext (fun challenge _ => ?_)
  rw [games.toKnowledgeTransitionFamily_badEvent_iff round context message hdoomed challenge]
  exact ⟨fun h => h.2, fun h => ⟨hrel, h⟩⟩

/-- **Extensional round-by-round extraction bridge.** The extensional extraction condition with a
per-round error holds exactly when the doomed-subtype knowledge-transition family is bounded by the
same error. This is a genuine equivalence: the forward direction turns each bad-event bound into the
strict extraction trigger's contrapositive, and the backward direction recovers a valid extracted
witness from a bad-event bound via the strict trigger `error < Pr[escape]`. -/
theorem extractionCondition_iff_isBounded (games : KnowledgeExtractionFamily rounds)
    (error : Fin rounds → ℝ≥0∞) :
    games.ExtractionCondition error ↔
      games.toKnowledgeTransitionFamily.IsBounded error := by
  rw [KnowledgeTransitionFamily.isBounded_iff]
  constructor
  · intro hEC round cm
    obtain ⟨⟨context, message⟩, hdoomed⟩ := cm
    by_cases hR : games.relation (games.statement round.castSucc context)
        (games.extract round context message)
    · refine le_of_eq_of_le (probEvent_eq_zero (fun challenge _ hbad => ?_)) zero_le
      exact ((games.toKnowledgeTransitionFamily_badEvent_iff round context message hdoomed
        challenge).mp hbad).1 hR
    · rw [games.probEvent_toKnowledgeTransitionFamily_badEvent_of_not_relation round context
        message hdoomed hR]
      by_contra hle
      rw [not_le] at hle
      exact hR (hEC round context message hdoomed hle)
  · intro hIB round context message hdoomed hlt
    by_contra hR
    have hbound := hIB round ⟨(context, message), hdoomed⟩
    rw [games.probEvent_toKnowledgeTransitionFamily_badEvent_of_not_relation round context
      message hdoomed hR] at hbound
    exact absurd hbound (not_le.mpr hlt)

end KnowledgeExtractionFamily

end RoundByRound
