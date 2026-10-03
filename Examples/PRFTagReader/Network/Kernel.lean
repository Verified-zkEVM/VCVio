/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.Network
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Local joint-kernel contracts for the PRF packet experiment

Each contract compares the full response and retained service-state measure of a local call.
The generic adaptive-oracle fold transports it to the bounded FIFO experiment. Both the final
verdict and measurable bad-state observations are retained, so implementations satisfying these
contracts can use the same direct-coupling reduction without changing its loss terms.
-/

public section

namespace PRFTagReader.Network

open OracleComp OracleSpec MeasureTheory

variable {TagId Nonce Digest S : Type}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]

/-- Local joint-kernel replacement preserves the actual bounded FIFO verdict law. -/
theorem verdict_law_congr
    (left right : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (hlocal : ∀ operation state, (left operation).run state =ᵈ (right operation).run state)
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S) :
    verdict left budget adversary state =ᵈ verdict right budget adversary state := by
  rw [verdict_eq _ _ _ hbound, verdict_eq _ _ _ hbound]
  simp only [StateT.run'_eq]
  exact (evalDistEq_simulateQ_run left right hlocal adversary state).map Prod.fst

/-- Local replacement preserves the bad-state event as well as the protocol's verdict. -/
theorem stateEvent_law_congr
    (left right : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (hlocal : ∀ operation state, (left operation).run state =ᵈ (right operation).run state)
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S) (event : S → Bool) :
    stateEvent left budget adversary state event =ᵈ
      stateEvent right budget adversary state event := by
  rw [stateEvent_eq _ _ _ hbound, stateEvent_eq _ _ _ hbound]
  exact (evalDistEq_simulateQ_run left right hlocal adversary state).map (event ∘ Prod.snd)

end PRFTagReader.Network

namespace PRFTagReader.Network

open OracleComp OracleSpec MeasureTheory UnlinkReduction ENNReal

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [Fintype TagId] [SampleableType Nonce] [SampleableType Digest]
  [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag]

/-- Retained counters and random-function cache of the multiple-session ideal service. -/
abbrev MultipleServiceState (TagId Nonce Digest : Type) :=
  UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache

/-- Retained counters and slot-indexed cache of the single-session ideal service. -/
abbrev SingleServiceState (TagId Nonce Digest : Type) (sessionsPerTag : ℕ) :=
  UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache

/-- Joint local contracts transport the direct-coupling bound, for either verdict `out`, with all
three loss terms intact. The bad-world contract retains the final private state needed by the
original reduction. -/
theorem multiple_le_single_add_bad_of_joint_law
    (multiple : QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (MultipleServiceState TagId Nonce Digest) ProbComp))
    (single : QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (SingleServiceState TagId Nonce Digest sessionsPerTag) ProbComp))
    (bad : QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp))
    (hmultiple : ∀ operation state, (multiple operation).run state =ᵈ
      (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) operation).run state)
    (hsingle : ∀ operation state, (single operation).run state =ᵈ
      (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag) operation).run state)
    (hbad : ∀ operation state, (bad operation).run state =ᵈ
      (multipleBadQueryImpl _ _ _ sessionsPerTag operation).run state)
    (out : Bool) (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : ℕ)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    𝒟[verdict multiple (qReader + qTag) adversary (UnlinkState.init, ∅)] {out} ≤
    𝒟[verdict single (qReader + qTag) adversary (UnlinkState.init, ∅)] {out} +
    𝒟[stateEvent bad (qReader + qTag) adversary
      ((UnlinkState.init, ∅), UnlinkBadState.init) (fun state => state.2.bad)] {true} +
    ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
    ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
    ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
      (Fintype.card Digest : ℝ≥0∞) := by
  have hbound := totalQueryBound adversary qReader qTag hReader hTag
  rw [(verdict_law_congr _ _ hmultiple _ _ hbound _).evalDist_eq,
    (verdict_law_congr _ _ hsingle _ _ hbound _).evalDist_eq,
    (stateEvent_law_congr _ _ hbad _ _ hbound _ _).evalDist_eq]
  exact multiple_le_single_add_bad (sessionsPerTag := sessionsPerTag)
    out adversary qReader qTag hReader hTag

end PRFTagReader.Network
