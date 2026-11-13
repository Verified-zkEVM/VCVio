/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.VectorCommitment
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Online extraction for deterministic vector commitments

A classical, random-oracle-model extraction game for a `DetVectorCommitment` relative to one oracle
`X →ₒ Y`. A two-phase adversary (`DetVectorCommitment.OnlineAdversary`) first outputs a commitment,
then receives a public challenge drawn from `sampleChal` and outputs claimed values together with
an opening proof. Both phases and the final `check` query one shared lazy random oracle
(`OracleSpec.randomOracle`), run from the empty cache.

An extractor reads a total vector off the commitment and the adversary's query log *at the moment
of commitment*, before the challenge is drawn. The online extraction error of the extractor against
an adversary (`DetVectorCommitment.onlineExtractionError`) is the probability that the final
opening is accepted although some claimed value disagrees with the extracted vector.

Since the extracted vector is fixed before the challenge, a protocol built on the commitment may
reason about it as if the prover had committed to that vector: this is the step that makes the
Kilian transformation sound in the random-oracle model
(`VCVio.CryptoFoundations.ChallengeVerifyProtocol.Kilian.Soundness`).

## Adversaries

The adversary's computations query only the oracle `X →ₒ Y` and sample no coins of their own. Its
strength is unbounded, so this is the model of soundness against unbounded provers, in which coins
do not help. The online extraction error of a concrete commitment is bounded in terms of the
adversary's query counts.

## Main definitions

* `DetVectorCommitment.OnlineAdversary`: the two-phase adversary.
* `DetVectorCommitment.OnlineTranscript`: the commitment, the commitment-phase query log, the
  challenge, the response and the verdict of one run.
* `DetVectorCommitment.onlineRun`: the run of the game in the random-oracle model, and
  `DetVectorCommitment.onlineGame`, its oracle syntax for a fixed challenge.
* `DetVectorCommitment.onlineExtractionError`: the probability that an accepted opening disagrees
  with the extracted vector.

## Main results

* `DetVectorCommitment.prEvent_onlineRun_le`: an event of the commitment phase and the challenge is
  bounded by its worst case over commitment phases with an independent challenge.
* `DetVectorCommitment.bind_onlineRun_eq`: for a fixed challenge, the run after the commitment phase
  is the random-oracle interpretation of `onlineGame`.
* `DetVectorCommitment.prEvent_onlineRun_le_of_forall_chal`: with a countable challenge type, an
  event of the run is bounded by a bound for every fixed challenge.
-/

public section

open OracleComp OracleSpec

open scoped ENNReal

namespace DetVectorCommitment

variable {X Y Msg Cm Td Pf : Type} {ℓ : ℕ}

/-- A two-phase adversary against a vector commitment relative to the oracle `X →ₒ Y`, with
private state `St`: it commits, and then, given a public challenge `Chal`, responds. Both phases
query the oracle. -/
structure OnlineAdversary (X Y Cm St Chal Resp : Type) where
  /-- Output a commitment together with private state. -/
  commit : OracleComp (X →ₒ Y) (Cm × St)
  /-- Given the private state and the challenge, output a response. -/
  respond : St → Chal → OracleComp (X →ₒ Y) Resp

/-- The observable record of one run of the online extraction game: the commitment `cm`, the log
`log` of the oracle queries of the commitment phase, the challenge `chal`, the response `resp`
(claimed values and an opening proof), and the verdict `accepted` of the commitment's check on that
response. -/
structure OnlineTranscript (X Y Cm Chal Resp : Type) where
  /-- The adversary's commitment. -/
  cm : Cm
  /-- The oracle queries of the commitment phase, with their answers, in order. -/
  log : (X →ₒ Y).QueryLog
  /-- The public challenge. -/
  chal : Chal
  /-- The adversary's response. -/
  resp : Resp
  /-- Whether the commitment's check accepted the response. -/
  accepted : Bool

/-- The oracle syntax of the online extraction game for a fixed challenge `chal`: the adversary
commits under a query log, responds to `chal`, and the commitment's `check` evaluates the
response. -/
@[expose]
def onlineGame (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) {St Chal : Type}
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf)) (chal : Chal) :
    OracleComp (X →ₒ Y) (OnlineTranscript X Y Cm Chal (PartialVec ℓ Msg × Pf)) := do
  let z ← A.commit.withQueryLog
  let resp ← A.respond z.1.2 chal
  let b ← vc.check z.1.1 resp.1 resp.2
  return ⟨z.1.1, z.2, chal, resp, b⟩

variable [DecidableEq X] [SampleableType Y]

/-- The online extraction game in the random-oracle model, from the empty cache: the adversary
commits, the challenge is drawn from `sampleChal`, the adversary responds with claimed values and an
opening proof, and the commitment's `check` evaluates the response against the same oracle. -/
@[expose]
noncomputable def onlineRun (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) {St Chal : Type}
    (sampleChal : ProbComp Chal)
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf)) :
    ProbComp (OnlineTranscript X Y Cm Chal (PartialVec ℓ Msg × Pf)) := do
  let z ← (simulateQ (X →ₒ Y).randomOracle A.commit.withQueryLog).run ∅
  let chal ← sampleChal
  let r ← (simulateQ (X →ₒ Y).randomOracle (A.respond z.1.1.2 chal)).run z.2
  let b ← (simulateQ (X →ₒ Y).randomOracle (vc.check z.1.1.1 r.1.1 r.1.2)).run' r.2
  return ⟨z.1.1.1, z.1.2, chal, r.1, b⟩

/-- The claimed values `ans` agree with the total vector `f` wherever they are defined. -/
abbrev ClaimsAgree (f : Fin ℓ → Msg) (ans : PartialVec ℓ Msg) : Prop :=
  PartialVec.Agrees (fun i => some (f i)) ans

omit [DecidableEq X] [SampleableType Y] in
theorem claimsAgree_iff (f : Fin ℓ → Msg) (ans : PartialVec ℓ Msg) :
    ClaimsAgree f ans ↔ ∀ i v, ans i = some v → v = f i := by
  refine forall₂_congr fun i v => imp_congr_right fun _ => ?_
  exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩

/-- The **online extraction error** of the extractor `extract` against the adversary `A`, with
challenges drawn from `sampleChal`: the probability that the commitment's check accepts the
adversary's response although its claimed values disagree with the vector that `extract` reads off
the commitment and the commitment-phase query log. -/
@[expose]
noncomputable def onlineExtractionError (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ)
    (extract : (X →ₒ Y).QueryLog → Cm → Fin ℓ → Msg) {St Chal : Type}
    (sampleChal : ProbComp Chal)
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf)) : ℝ≥0∞ :=
  Pr{let t ← vc.onlineRun sampleChal A}[t.accepted = true ∧
    ¬ ClaimsAgree (extract t.log t.cm) t.resp.1]

/-- In the online extraction game, the probability of an event of the commitment, the
commitment-phase log and the challenge is bounded by its worst case over commitments and logs,
taken with an independently drawn challenge: the challenge is sampled after the commitment phase
and independently of it. -/
theorem prEvent_onlineRun_le (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) {St Chal : Type}
    (sampleChal : ProbComp Chal)
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf))
    (P : Cm → (X →ₒ Y).QueryLog → Chal → Prop) {ε : ℝ≥0∞}
    (h : ∀ cm log, Pr{let chal ← sampleChal}[P cm log chal] ≤ ε) :
    Pr{let t ← vc.onlineRun sampleChal A}[P t.cm t.log t.chal] ≤ ε := by
  classical
  unfold onlineRun
  refine prEvent_bind_le_of_forall_le _ _ _ fun z => ?_
  refine le_trans ?_ (h z.1.1.1 z.1.2)
  conv_rhs => rw [← bind_pure sampleChal]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun chal => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun r => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun b => ?_
  rw [prEvent_pure, prEvent_pure]

/-- For a fixed challenge, the online run after the commitment phase is the random-oracle
interpretation of `onlineGame`, from the empty cache. -/
theorem bind_onlineRun_eq (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) {St Chal : Type}
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf)) (chal : Chal) :
    ((simulateQ (X →ₒ Y).randomOracle A.commit.withQueryLog).run ∅ >>= fun z => do
      let r ← (simulateQ (X →ₒ Y).randomOracle (A.respond z.1.1.2 chal)).run z.2
      let b ← (simulateQ (X →ₒ Y).randomOracle (vc.check z.1.1.1 r.1.1 r.1.2)).run' r.2
      return (⟨z.1.1.1, z.1.2, chal, r.1, b⟩ :
        OnlineTranscript X Y Cm Chal (PartialVec ℓ Msg × Pf))) =
      (simulateQ (X →ₒ Y).randomOracle (vc.onlineGame A chal)).run' ∅ := by
  simp [onlineGame, StateT.run'_eq, map_bind]

/-- With a countable challenge type, an event of the online run is bounded by a bound on the
random-oracle interpretation of `onlineGame` for every fixed challenge: the challenge is drawn
independently of the commitment phase, so it may be drawn first. -/
theorem prEvent_onlineRun_le_of_forall_chal (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ)
    {St Chal : Type} [Countable Chal] (sampleChal : ProbComp Chal)
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf))
    (q : OnlineTranscript X Y Cm Chal (PartialVec ℓ Msg × Pf) → Prop) {ε : ℝ≥0∞}
    (h : ∀ chal, Pr{let t ← (simulateQ (X →ₒ Y).randomOracle (vc.onlineGame A chal)).run' ∅}[q t]
      ≤ ε) :
    Pr{let t ← vc.onlineRun sampleChal A}[q t] ≤ ε := by
  unfold onlineRun
  rw [← prEvent_bind_bind_swap_of_countable]
  refine prEvent_bind_le_of_forall_le _ _ _ fun chal => ?_
  rw [bind_onlineRun_eq]
  exact h chal

end DetVectorCommitment
