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
  [MeasurableSpace S]
  [∀ operation : (UnlinkOracleSpec TagId Nonce Digest).Domain,
    MeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range operation)]
  [∀ operation : (UnlinkOracleSpec TagId Nonce Digest).Domain,
    DiscreteMeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range operation × S)]

/-- Local joint-kernel replacement preserves the actual bounded FIFO verdict law. -/
theorem verdict_law_congr
    (left right : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (hlocal : ∀ operation state,
      𝒟[(left operation).run state] = 𝒟[(right operation).run state])
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S) :
    𝒟[verdict left budget adversary state] = 𝒟[verdict right budget adversary state] := by
  rw [verdict_eq _ _ _ hbound, verdict_eq _ _ _ hbound]
  simp only [StateT.run'_eq]
  rw [evalDist_map _ measurable_fst, evalDist_map _ measurable_fst,
    evalDist_simulateQ_run_congr left right hlocal]

/-- Local replacement preserves the bad-state event as well as the protocol's verdict. -/
theorem stateEvent_law_congr
    (left right : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (hlocal : ∀ operation state,
      𝒟[(left operation).run state] = 𝒟[(right operation).run state])
    (budget : ℕ) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S)
    (event : S → Bool) (hevent : Measurable event) :
    𝒟[stateEvent left budget adversary state event] =
      𝒟[stateEvent right budget adversary state event] := by
  rw [stateEvent_eq _ _ _ hbound, stateEvent_eq _ _ _ hbound]
  change 𝒟[(event ∘ Prod.snd) <$> (simulateQ left adversary).run state] =
    𝒟[(event ∘ Prod.snd) <$> (simulateQ right adversary).run state]
  rw [evalDist_map _ (hevent.comp measurable_snd),
    evalDist_map _ (hevent.comp measurable_snd), evalDist_simulateQ_run_congr left right hlocal]

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

variable
  [MeasurableSpace (MultipleServiceState TagId Nonce Digest)]
  [MeasurableSpace (SingleServiceState TagId Nonce Digest sessionsPerTag)]
  [MeasurableSpace (MultipleBadState TagId Nonce Digest sessionsPerTag)]
  [∀ operation : (UnlinkOracleSpec TagId Nonce Digest).Domain,
    MeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range operation)]
  [∀ operation : (UnlinkOracleSpec TagId Nonce Digest).Domain,
    DiscreteMeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range operation ×
      MultipleServiceState TagId Nonce Digest)]
  [∀ operation : (UnlinkOracleSpec TagId Nonce Digest).Domain,
    DiscreteMeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range operation ×
      SingleServiceState TagId Nonce Digest sessionsPerTag)]
  [∀ operation : (UnlinkOracleSpec TagId Nonce Digest).Domain,
    DiscreteMeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range operation ×
      MultipleBadState TagId Nonce Digest sessionsPerTag)]

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
    (hmultiple : ∀ operation state, 𝒟[(multiple operation).run state] =
      𝒟[(multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) operation).run state])
    (hsingle : ∀ operation state, 𝒟[(single operation).run state] =
      𝒟[(singleIdealQueryImpl (sessionsPerTag := sessionsPerTag) operation).run state])
    (hbad : ∀ operation state, 𝒟[(bad operation).run state] =
      𝒟[(multipleBadQueryImpl _ _ _ sessionsPerTag operation).run state])
    (hmeas : Measurable (fun state : MultipleBadState TagId Nonce Digest sessionsPerTag =>
      state.2.bad))
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
  rw [verdict_law_congr _ _ hmultiple _ _ hbound,
    verdict_law_congr _ _ hsingle _ _ hbound,
    stateEvent_law_congr _ _ hbad _ _ hbound _ _ hmeas]
  simpa only [evalDist_apply_singleton] using
    multiple_le_single_add_bad (sessionsPerTag := sessionsPerTag)
      out adversary qReader qTag hReader hTag

end PRFTagReader.Network
