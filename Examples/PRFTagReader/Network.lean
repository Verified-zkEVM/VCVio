/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.DirectCoupling.Compose
public import VCVio.Interaction.UC.OracleNetwork.Serial
public import VCVio.OracleComp.QueryTracking.QueryBound.Partition

/-!
# PRF tag/reader games over FIFO packet delivery

The adversary is an adaptive network client. Tag and reader requests share the original
stateful service and travel through the FIFO runtime before their responses resume that client.
Separate tag and reader query budgets derive a schedule of `3 * (qReader + qTag)` activations.
The network's complete response transcript is the traced oracle game's transcript. Its verdict
and bad-state observation consequently satisfy the original direct-coupling bound, with the
same three loss terms and no reader-nonce distinctness hypothesis.

This consumer uses an explicit serial schedule and atomic oracle service calls. It does not
identify adversarially reordered schedules or claim asynchronous UC security.
-/

public section

open OracleComp OracleSpec Interaction.UC.OracleNetwork

namespace PRFTagReader.Network

variable {TagId Nonce Digest S : Type}

/-- The separate reader and tag budgets cover every operation of the protocol interface. -/
theorem totalQueryBound (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    IsTotalQueryBound adversary (qReader + qTag) :=
  isTotalQueryBound_of_partition adversary _ _
    (fun a => by cases a <;> simp) qReader qTag hReader hTag

variable [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]

/-- Observe the verdict of the actual bounded packet run. An unfinished client rejects. -/
@[expose] def verdict
    (impl : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest) (state : S) : ProbComp Bool :=
  (fun out => out.1.1.getD false) <$> serialObservation impl budget adversary state

/-- Observe a predicate of the service state after actual bounded packet execution. -/
@[expose] def stateEvent
    (impl : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest) (state : S)
    (event : S → Bool) : ProbComp Bool :=
  (fun out => event out.2) <$> serialObservation impl budget adversary state

/-- Packet execution preserves the complete ordered response transcript and verdict. -/
theorem transcript_eq
    (impl : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (adversary : UnlinkAdversary TagId Nonce Digest) (state : S) (qReader qTag : ℕ)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    serialObservation impl (qReader + qTag) adversary state =
      (fun out => ((some out.1.1, out.1.2), out.2)) <$> loggedRun impl () adversary state :=
  serialObservation_eq_loggedRun impl _ adversary
    (totalQueryBound adversary qReader qTag hReader hTag) state

/-- Every bounded client's network verdict is exactly its original oracle-game verdict. -/
theorem verdict_eq
    (impl : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S) :
    verdict impl budget adversary state = (simulateQ impl adversary).run' state := by
  have h := congrArg (fun action : ProbComp (Option Bool × S) =>
    (fun out => out.1.getD false) <$> action)
    (map_serialObservation impl budget adversary hbound state)
  simpa [verdict, Functor.map_map, StateT.run'_eq] using h

/-- Packet execution preserves any Boolean observation of the final private service state. -/
theorem stateEvent_eq
    (impl : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S) (event : S → Bool) :
    stateEvent impl budget adversary state event =
      (fun out => event out.2) <$> (simulateQ impl adversary).run state := by
  have h := congrArg (fun action : ProbComp (Option Bool × S) =>
    (fun out => event out.2) <$> action)
    (map_serialObservation impl budget adversary hbound state)
  simpa [stateEvent, Functor.map_map] using h

open UnlinkReduction ENNReal

variable [Fintype TagId] [SampleableType Nonce] [SampleableType Digest]
  [Fintype Nonce] [Fintype Digest] {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- The direct-coupling loss holds for actual FIFO network execution under the derived schedule.
The bad-event term is also observed from a packet run, including its final private service state. -/
theorem multiple_le_single_add_bad (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    Pr[= true | verdict (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
      (qReader + qTag) adversary (UnlinkState.init, ∅)] ≤
    Pr[= true | verdict (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
      (qReader + qTag) adversary (UnlinkState.init, ∅)] +
    Pr[= true | stateEvent (multipleBadQueryImpl _ _ _ sessionsPerTag)
      (qReader + qTag) adversary ((UnlinkState.init, ∅), UnlinkBadState.init)
      (fun state => state.2.bad)] +
    ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
    ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
    ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
      (Fintype.card Digest : ℝ≥0∞) := by
  have hbound := totalQueryBound adversary qReader qTag hReader hTag
  rw [verdict_eq _ _ _ hbound, verdict_eq _ _ _ hbound, stateEvent_eq _ _ _ hbound]
  simpa only [probOutput_map] using
    multipleIdeal_le_singleIdeal_add_bad_DC (sessionsPerTag := sessionsPerTag)
      adversary qReader qTag hReader hTag

end PRFTagReader.Network
