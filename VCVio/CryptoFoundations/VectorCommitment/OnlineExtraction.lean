/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.VectorCommitment
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Online extraction for deterministic vector commitments

A classical, random-oracle-model extraction game for a `DetVectorCommitment` relative to one oracle
`X →ₒ Y`. A two-phase adversary (`DetVectorCommitment.OnlineAdversary`) first outputs a commitment,
then receives a public challenge drawn from `sampleChal` and outputs claimed values together with
an opening proof. Both phases and the final `check` query one shared lazy random oracle
(`OracleSpec.romImpl`), run from the empty cache.

An extractor reads a total vector off the random-oracle cache *at the moment of commitment*,
before the challenge is drawn. The online extraction error of the extractor against an adversary
(`DetVectorCommitment.onlineExtractionError`) is the probability that the final opening is accepted
although some claimed value disagrees with the extracted vector.

Since the extracted vector is fixed before the challenge, a protocol built on the commitment may
reason about it as if the prover had committed to that vector: this is the step that makes the
Kilian transformation sound in the random-oracle model
(`VCVio.CryptoFoundations.ChallengeVerifyProtocol.Kilian.Soundness`).

## Main definitions

* `DetVectorCommitment.OnlineAdversary`: the two-phase adversary.
* `DetVectorCommitment.OnlineTranscript`: the commitment, the commitment-time cache, the challenge,
  the response and the verdict of one run.
* `DetVectorCommitment.onlineRun`: the run of the game in the random-oracle model.
* `DetVectorCommitment.onlineExtractionError`: the probability that an accepted opening disagrees
  with the extracted vector.
-/

public section

open OracleComp OracleSpec

open scoped ENNReal

namespace DetVectorCommitment

variable {X Y Msg Cm Td Pf : Type} {ℓ : ℕ}

/-- A two-phase adversary against a vector commitment relative to the oracle `X →ₒ Y`, with
private state `St`: it commits, and then, given a public challenge `Chal`, responds. Both phases
may sample coins and query the oracle. -/
structure OnlineAdversary (X Y Cm St Chal Resp : Type) where
  /-- Output a commitment together with private state. -/
  commit : OracleComp (unifSpec + (X →ₒ Y)) (Cm × St)
  /-- Given the private state and the challenge, output a response. -/
  respond : St → Chal → OracleComp (unifSpec + (X →ₒ Y)) Resp

/-- The observable record of one run of the online extraction game: the commitment `cm`, the
random-oracle cache `cache` right after the commitment phase, the challenge `chal`, the response
`resp` (claimed values and an opening proof), and the verdict `accepted` of the commitment's
check on that response. -/
structure OnlineTranscript (X Y Cm Chal Resp : Type) where
  /-- The adversary's commitment. -/
  cm : Cm
  /-- The random-oracle cache when the commitment was output. -/
  cache : (X →ₒ Y).QueryCache
  /-- The public challenge. -/
  chal : Chal
  /-- The adversary's response. -/
  resp : Resp
  /-- Whether the commitment's check accepted the response. -/
  accepted : Bool

variable [DecidableEq X] [SampleableType Y]

/-- The online extraction game in the random-oracle model, from the empty cache: the adversary
commits, the challenge is drawn from `sampleChal`, the adversary responds with claimed values and an
opening proof, and the commitment's `check` evaluates the response against the same oracle. -/
@[expose]
noncomputable def onlineRun (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) {St Chal : Type}
    (sampleChal : ProbComp Chal)
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf)) :
    ProbComp (OnlineTranscript X Y Cm Chal (PartialVec ℓ Msg × Pf)) := do
  let z ← (simulateQ (romImpl (X →ₒ Y)) A.commit).run ∅
  let chal ← sampleChal
  let r ← (simulateQ (romImpl (X →ₒ Y)) (A.respond z.1.2 chal)).run z.2
  let b ← (simulateQ (X →ₒ Y).randomOracle (vc.check z.1.1 r.1.1 r.1.2)).run' r.2
  return ⟨z.1.1, z.2, chal, r.1, b⟩

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
the commitment-time cache. -/
@[expose]
noncomputable def onlineExtractionError (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ)
    (extract : (X →ₒ Y).QueryCache → Cm → Fin ℓ → Msg) {St Chal : Type}
    (sampleChal : ProbComp Chal)
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf)) : ℝ≥0∞ :=
  Pr{let t ← vc.onlineRun sampleChal A}[t.accepted = true ∧
    ¬ ClaimsAgree (extract t.cache t.cm) t.resp.1]

/-- In the online extraction game, the probability of an event of the commitment, the
commitment-time cache and the challenge is bounded by its worst case over commitments and caches,
taken with an independently drawn challenge: the challenge is sampled after the commitment phase
and independently of it. -/
theorem prEvent_onlineRun_le (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) {St Chal : Type}
    (sampleChal : ProbComp Chal)
    (A : OnlineAdversary X Y Cm St Chal (PartialVec ℓ Msg × Pf))
    (P : Cm → (X →ₒ Y).QueryCache → Chal → Prop) {ε : ℝ≥0∞}
    (h : ∀ cm cache, Pr{let chal ← sampleChal}[P cm cache chal] ≤ ε) :
    Pr{let t ← vc.onlineRun sampleChal A}[P t.cm t.cache t.chal] ≤ ε := by
  classical
  unfold onlineRun
  refine prEvent_bind_le_of_forall_le _ _ _ fun z => ?_
  refine le_trans ?_ (h z.1.1 z.2)
  conv_rhs => rw [← bind_pure sampleChal]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun chal => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun r => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun b => ?_
  rw [prEvent_pure, prEvent_pure]

end DetVectorCommitment
