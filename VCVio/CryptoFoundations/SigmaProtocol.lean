/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.TVDist
public import VCVio.CryptoFoundations.IdenSchemeWithAbort

/-!
# Challenge-Verify Protocols and Sigma Protocols

This file defines two structure types, along with standard security properties:
completeness, special soundness, and honest-verifier zero-knowledge (HVZK).

`ChallengeVerifyProtocol` is the bare commit–challenge–response interaction: the prover commits,
the verifier replies with a single challenge drawn from its own randomness, the prover responds,
and the verifier deterministically accepts or rejects. It carries no witness-extraction or
simulation data, so it is the right interface for consumers that only run the protocol.

`SigmaProtocol` extends it with `sim` and `extract` fields, packaging a Σ-protocol together with
the simulator and the witness extractor that special soundness refers to. Both conventions appear
in the literature — Damgård's canonical treatment leaves the extractor existentially quantified
inside the special soundness property, whereas bundling it as data lets consumers such as the
Fischlin transform and the Fiat-Shamir Σ-layer name and run it. Splitting the two records supports
both readings: use `ChallengeVerifyProtocol` when the extractor is irrelevant, `SigmaProtocol`
when it is needed.

Properties that only concern the interaction — `PerfectlyComplete`, `HVZK`, `PerfectHVZK`,
`UniqueResponses`, and the transcript distribution `realTranscript` — are stated on
`ChallengeVerifyProtocol`, and are available on a `SigmaProtocol` through the parent projection.
`SpeciallySound` lives on `SigmaProtocol`, since it is the property that consumes `extract`.

## Type Parameters

- `Stmt`: statement (public key)
- `Wit`: witness (secret key)
- `Commit`: public commitment
- `PrvState`: private prover state (retained between commit and respond)
- `Chal`: verifier challenge (drawn uniformly)
- `Resp`: prover response
- `rel`: the relation proven by the protocol

## Coercion to `IdenSchemeWithAbort`

Every `ChallengeVerifyProtocol` can be viewed as a non-aborting `IdenSchemeWithAbort` via
`ChallengeVerifyProtocol.toIdenSchemeWithAbort`, which wraps `respond` with `some`.
-/

@[expose] public section

universe u v

open OracleSpec OracleComp

/-- A commit–challenge–response protocol for statements in `Stmt` and witnesses in `Wit`, where
`rel : Stmt → Wit → Bool` is the proposition proven by the protocol.

Commitments are split into a public part `Commit` (revealed to the verifier) and a private part
`PrvState` (retained by the prover). The verifier sends a single challenge, drawn uniformly from
`Chal`; since that challenge is its only message, the protocol is public-coin. Prover responses
are in `Resp`, and verification is deterministic.

This is the interaction alone. A Σ-protocol additionally carries a witness extractor; see
`SigmaProtocol`, which extends this structure. -/
structure ChallengeVerifyProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool) where
  /-- Generate a commitment to prove knowledge of a valid witness. -/
  commit (stmt : Stmt) (wit : Wit) : ProbComp (Commit × PrvState)
  /-- Given a previous private state, respond to the challenge. -/
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) : ProbComp Resp
  /-- Deterministic verification: check that the response satisfies the challenge. -/
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool

/-- A Σ-protocol: a `ChallengeVerifyProtocol` together with the simulator and the witness
extractor that special soundness refers to (`SigmaProtocol.SpeciallySound`).

The extractor is bundled as data rather than existentially quantified so that consumers can run
it — the Fischlin transform and the Fiat-Shamir Σ-layer both do. Consumers that need neither it
nor `sim` should take a `ChallengeVerifyProtocol` instead; every `SigmaProtocol` provides one
through its parent projection. -/
structure SigmaProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool)
    extends ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel where
  /-- Simulate public commitment generation while only knowing the statement. -/
  sim (stmt : Stmt) : ProbComp Commit
  /-- Extract a witness to the statement from two accepting transcripts. -/
  extract (chal₁ : Chal) (resp₁ : Resp) (chal₂ : Chal) (resp₂ : Resp) : ProbComp Wit

namespace ChallengeVerifyProtocol

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section complete

variable [SampleableType Chal] [IsUniformSpec unifSpec]

/-- A protocol is perfectly complete if the honest prover always convinces the verifier
on valid statement-witness pairs. -/
def PerfectlyComplete (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ x w, rel x w = true →
    Pr[= true | do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Chal
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π] = 1

end complete

end ChallengeVerifyProtocol

namespace SigmaProtocol

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section speciallySound

/-- Special soundness at a particular statement: given two accepting transcripts with the same
commitment but different challenges, the extracted witness is valid. -/
def SpeciallySoundAt (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (x : Stmt) : Prop :=
  ∀ pc ω₁ ω₂ p₁ p₂, ω₁ ≠ ω₂ →
    σ.verify x pc ω₁ p₁ = true → σ.verify x pc ω₂ p₂ = true →
    ∀ w ∈ support (σ.extract ω₁ p₁ ω₂ p₂), rel x w = true

/-- A Σ-protocol is specially sound if `SpeciallySoundAt` holds for all statements. -/
def SpeciallySound (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ x, SpeciallySoundAt σ x

/-- Special soundness immediately validates any witness returned by the Σ-protocol extractor from
two accepting transcripts with the same statement and commitment and with distinct challenges. -/
theorem extract_sound_of_speciallySoundAt
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) {x : Stmt}
    (hss : σ.SpeciallySoundAt x)
    {pc : Commit} {ω₁ ω₂ : Chal} {p₁ p₂ : Resp} (hω : ω₁ ≠ ω₂)
    (hv₁ : σ.verify x pc ω₁ p₁ = true) (hv₂ : σ.verify x pc ω₂ p₂ = true)
    {w : Wit} (hw : w ∈ support (σ.extract ω₁ p₁ ω₂ p₂)) :
    rel x w = true :=
  hss pc ω₁ ω₂ p₁ p₂ hω hv₁ hv₂ w hw

end speciallySound

end SigmaProtocol

namespace ChallengeVerifyProtocol

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section hvzk

variable [SampleableType Chal] [IsUniformSpec unifSpec]

/-- The honest prover's transcript distribution. -/
def realTranscript (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (x : Stmt) (w : Wit) :
    ProbComp (Commit × Chal × Resp) := do
  let (pc, sc) ← σ.commit x w
  let ω ← $ᵗ Chal
  let π ← σ.respond x w sc ω
  return (pc, ω, π)

/-- Honest-verifier zero-knowledge: the real transcript distribution is within total variation
distance `ζ_zk` of the simulated one.

The real transcript is `σ.realTranscript x w`.
The simulated transcript is produced by `simTranscript` given only the statement `x`.

Note: the `sim` field of `SigmaProtocol` only produces a public commitment. For HVZK we need
a full transcript simulator `Stmt → ProbComp (Commit × Chal × Resp)`. We parameterize by this
simulator, which also keeps the property available on a bare `ChallengeVerifyProtocol`. -/
def HVZK (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (ζ_zk : ℝ) : Prop :=
  ∀ x w, rel x w = true →
    tvDist (σ.realTranscript x w) (simTranscript x) ≤ ζ_zk

/-- Exact honest-verifier zero-knowledge: the real transcript distribution equals the
simulated one. -/
def PerfectHVZK (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) : Prop :=
  ∀ x w, rel x w = true →
    𝒟[σ.realTranscript x w] = 𝒟[simTranscript x]

/-- The perfect HVZK property is equivalent to the approximate HVZK property with `ζ_zk = 0`. -/
@[grind =]
lemma perfectHVZK_iff_hvzk_zero
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) :
    σ.PerfectHVZK simTranscript ↔ σ.HVZK simTranscript 0 := by
  refine ⟨fun h x w hx => ?_, fun h x w hx => ?_⟩
  · exact le_of_eq ((tvDist_eq_zero_iff _ _).2 (h x w hx))
  · exact (tvDist_eq_zero_iff _ _).1 (le_antisymm (h x w hx) (tvDist_nonneg _ _))

open scoped ENNReal in
/-- The simulator's commitment marginal has predictability at most `β`: no single
commitment value is output with probability exceeding `β`. Equivalently, the commitment
has min-entropy at least `-log₂ β`.

This is a companion assumption to `HVZK` that bounds the collision probability of
programmed cache entries in the Fiat-Shamir CMA-to-NMA reduction. For Schnorr,
`β = 1/|G|` because the commitment `g^r` is uniform over the group.

The `_σ : SigmaProtocol …` argument is dummy (the predicate only depends on
`simTranscript` and `β`); it is present to enable field-notation usage like
`σ.simCommitPredictability simTranscript β`. -/
def simCommitPredictability
    (_σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (β : ℝ≥0∞) : Prop :=
  ∀ x : Stmt, ∀ c₀ : Commit, probOutput (Prod.fst <$> simTranscript x) c₀ ≤ β

open scoped ENNReal in
/-- Conditional uniformity of the simulator's challenge given its commitment, expressed
in product form: for any statement `x` admitting a witness, any commit value `c₀`, and
any challenge value `ch₀`, the joint marginal `Pr[(commit, chal) = (c₀, ch₀)]` factors as
`Pr[commit = c₀] * (1 / |Chal|)`.

This is a strengthening of `simCommitPredictability` (which only bounds the commit
marginal). Where the latter says "no commit value is too likely", `simChalUniformGivenCommit`
says "the challenge is uniform conditional on any commit value", which is exactly the
hypothesis required by `identical_until_bad_with_flag` when bridging the Fiat-Shamir
programming-oracle and no-programming-oracle worlds: cache misses on programmed points
return the simulator's challenge, and the bridge needs that challenge to be marginally
uniform conditional on the simulator's commit (which is what gets compared against the
random oracle's would-be answer).

The product form `P[(c₀, ch₀)] = P[c₀] * 1/|Chal|` avoids conditional-probability
ambiguities when `P[c₀] = 0` and is the most directly-usable shape inside the `tvDist`
calculation.

The `rel pk sk = true` hypothesis is needed because typical Schnorr-style simulators only
satisfy this when `pk` admits a witness (the proof uses a witness-indexed bijection on the
response variable); for statements outside the relation's image, the simulator's joint may
have any structure. -/
def simChalUniformGivenCommit [Fintype Chal]
    (_σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) : Prop :=
  ∀ (pk : Stmt) (sk : Wit), rel pk sk = true →
    ∀ (c₀ : Commit) (ch₀ : Chal),
      Pr[fun t : Commit × Chal × Resp => t.1 = c₀ ∧ t.2.1 = ch₀ | simTranscript pk] =
        Pr[fun t : Commit × Chal × Resp => t.1 = c₀ | simTranscript pk] *
          (Fintype.card Chal : ℝ≥0∞)⁻¹

end hvzk

section uniqueResponses

/-- A protocol has unique responses if for any statement, commitment, and challenge,
there is at most one valid response. This property is required by the Fischlin transform
and holds for most common Σ-protocols (Schnorr, Guillou-Quisquater, etc.). -/
def UniqueResponses (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ x pc ω p₁ p₂,
    σ.verify x pc ω p₁ = true → σ.verify x pc ω p₂ = true → p₁ = p₂

end uniqueResponses

section toIdenSchemeWithAbort

/-- Every `ChallengeVerifyProtocol` can be viewed as a non-aborting `IdenSchemeWithAbort` by
wrapping the response in `some`. -/
def toIdenSchemeWithAbort (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel) :
    IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel where
  commit := σ.commit
  respond := fun stmt wit prvState chal => some <$> σ.respond stmt wit prvState chal
  verify := σ.verify

instance : Coe (ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) :=
  ⟨toIdenSchemeWithAbort⟩

end toIdenSchemeWithAbort

end ChallengeVerifyProtocol
