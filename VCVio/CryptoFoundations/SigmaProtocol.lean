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
the verifier replies with a single uniformly drawn challenge, the prover responds, and the
verifier deterministically accepts or rejects. It carries no witness-extraction or simulation
data, so it is the right interface for consumers that only run the protocol.

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

Both records are parameterized by the monad `m` in which the participants compute, so the prover
may query oracles as well as sample randomness. Every probability- or support-bearing property
assumes the *lawful* semantic lifts `[LawfulMonadLiftT m SPMF]` and `[LawfulMonadLiftT m SetM]`
together with the bridge `[EvalDistCompatible m]`: lawfulness is what lets probability statements
about the composite protocol decompose along its `bind`s, and the bridge ties the support-based
notions (`SpeciallySound`) and the probability-based ones (`PerfectlyComplete`, `HVZK`) to a
single coherent semantics of the same protocol.

`PerfectlyComplete` quantifies over the verifier's challenge pointwise, so its statement needs no
sampling structure on `m`; at `m := ProbComp` it is equivalent to the sampled form
(`perfectlyComplete_iff_probOutput_uniform_challenge_eq_one`, with the two directions available
separately as `PerfectlyComplete.probOutput_uniform_challenge_eq_one` and
`perfectlyComplete_of_probOutput_uniform_challenge_eq_one`). The transcript-facing properties
(`realTranscript`, `HVZK`, `PerfectHVZK`) draw the challenge as `liftM ($ᵗ Chal)`, which requires
`[MonadLiftT ProbComp m]`; at `m := ProbComp` this is definitionally the plain uniform sample
(`realTranscript_probComp`).

## Type Parameters

- `Stmt`: statement (public key)
- `Wit`: witness (secret key)
- `Commit`: public commitment
- `PrvState`: private prover state (retained between commit and respond)
- `Chal`: verifier challenge (drawn uniformly)
- `Resp`: prover response
- `rel`: the relation proven by the protocol
- `m`: the monad in which the participants' computations live

## Coercion to `IdenSchemeWithAbort`

Every `ProbComp`-valued `ChallengeVerifyProtocol` can be viewed as a non-aborting
`IdenSchemeWithAbort` via `ChallengeVerifyProtocol.toIdenSchemeWithAbort`, which wraps
`respond` with `some`.
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

The prover's computations live in an arbitrary monad `m`. Probability-bearing properties assume
the lawful lift `[MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]`, support-bearing ones the lawful
lift `[MonadLiftT m SetM] [LawfulMonadLiftT m SetM]`, and both carry the bridge
`[EvalDistCompatible m]` so that the two routes describe one semantics of the same protocol
(a `MonadLiftT ProbComp m` lift is additionally used where the uniform challenge is drawn inside
the transcript). Taking `m := ProbComp` recovers the usual notion of a protocol whose only
randomness is uniform sampling.

A general `m` also admits provers that query oracles, with one semantic caveat: the probability
denotation of `OracleComp spec` under `[IsProbabilitySpec spec]` samples a *fresh independent*
response for every query, so instantiating these properties at a bare oracle monad is meaningful
only for oracles where independent per-query responses are the intended semantics (e.g. genuine
sampling oracles). A shared random oracle — such as the hash oracle of the Kilian or Fiat-Shamir
transforms, where equal inputs must receive equal answers — must first be interpreted through the
caching layer (`OracleSpec.cachingOracle` / `withCacheOverlay`) before lifting into `SPMF` /
`SetM`.

This is the interaction alone. A Σ-protocol additionally carries a witness extractor; see
`SigmaProtocol`, which extends this structure. -/
structure ChallengeVerifyProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool)
    (m : Type → Type) where
  /-- Generate a commitment to prove knowledge of a valid witness. -/
  commit (stmt : Stmt) (wit : Wit) : m (Commit × PrvState)
  /-- Given a previous private state, respond to the challenge. -/
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) : m Resp
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
    (m : Type → Type)
    extends ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m where
  /-- Simulate public commitment generation while only knowing the statement. -/
  sim (stmt : Stmt) : m Commit
  /-- Extract a witness to the statement from two accepting transcripts. -/
  extract (chal₁ : Chal) (resp₁ : Resp) (chal₂ : Chal) (resp₂ : Resp) : m Wit

namespace ChallengeVerifyProtocol

variable {m : Type → Type} [Monad m]
  {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section complete

/-- A protocol is perfectly complete if, on valid statement-witness pairs, the honest prover
convinces the verifier with probability `1` on every challenge the verifier might send.

Since the verifier's challenge is drawn uniformly, quantifying over the challenge pointwise is
equivalent to drawing it and asking for acceptance probability `1` — but the pointwise form
needs no sampling structure on `m`, and is the shape consumers such as the Fischlin transform
extract anyway. At `m := ProbComp` the equivalence with the sampled form is
`perfectlyComplete_iff_probOutput_uniform_challenge_eq_one`. -/
def PerfectlyComplete [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m) :
    Prop :=
  ∀ x w, rel x w = true → ∀ ω,
    Pr[= true | do
      let (pc, sc) ← σ.commit x w
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π] = 1

/-- Sampled-challenge form of `PerfectlyComplete` for `ProbComp`-valued protocols: the honest
run that draws its challenge uniformly accepts with probability `1`. -/
lemma PerfectlyComplete.probOutput_uniform_challenge_eq_one [SampleableType Chal]
    {σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp}
    (hc : σ.PerfectlyComplete) {x : Stmt} {w : Wit} (h : rel x w = true) :
    Pr[= true | do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Chal
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π] = 1 := by
  change Pr[= true | σ.commit x w >>= fun a =>
      ($ᵗ Chal : ProbComp Chal) >>= fun ω =>
        σ.respond x w a.2 ω >>= fun π => pure (σ.verify x a.1 ω π)] = 1
  rw [probOutput_bind_bind_swap]
  have hc' : ∀ ω : Chal, Pr[= true | σ.commit x w >>= fun a =>
      σ.respond x w a.2 ω >>= fun π => pure (σ.verify x a.1 ω π)] = 1 :=
    fun ω => hc x w h ω
  rw [probOutput_bind_eq_tsum]
  simp only [hc', mul_one]
  exact tsum_probOutput_eq_one' (by simp)

/-- Converse of `PerfectlyComplete.probOutput_uniform_challenge_eq_one` at `m := ProbComp`:
if the honest run that draws its challenge uniformly accepts with probability `1`, then it
accepts with probability `1` on every individual challenge. This holds because the uniform
draw puts positive weight on every challenge, so no challenge can be rejected with positive
probability. Together with the forward direction this gives
`perfectlyComplete_iff_probOutput_uniform_challenge_eq_one`. -/
lemma perfectlyComplete_of_probOutput_uniform_challenge_eq_one [SampleableType Chal]
    {σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp}
    (hc : ∀ x w, rel x w = true →
      Pr[= true | do
        let (pc, sc) ← σ.commit x w
        let ω ← $ᵗ Chal
        let π ← σ.respond x w sc ω
        return σ.verify x pc ω π] = 1) :
    σ.PerfectlyComplete := by
  intro x w h ω
  have h1 := hc x w h
  rw [show (do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Chal
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π) = σ.commit x w >>= fun a =>
        ($ᵗ Chal : ProbComp Chal) >>= fun ω =>
          σ.respond x w a.2 ω >>= fun π => pure (σ.verify x a.1 ω π) from rfl,
    probOutput_bind_bind_swap, probOutput_bind_eq_tsum] at h1
  by_contra hω
  have hlt : Pr[= true | σ.commit x w >>= fun a =>
      σ.respond x w a.2 ω >>= fun π => pure (σ.verify x a.1 ω π)] < 1 :=
    lt_of_le_of_ne probOutput_le_one hω
  have hpos : 0 < Pr[= ω | ($ᵗ Chal : ProbComp Chal)] :=
    (probOutput_pos_iff _ _).2 (by simp)
  refine absurd (h1.trans (tsum_probOutput_eq_one' (mx := ($ᵗ Chal : ProbComp Chal))
    (by simp)).symm) (ne_of_lt (ENNReal.tsum_lt_tsum (i := ω) ?_ ?_ ?_))
  · rw [h1]; exact ENNReal.one_ne_top
  · exact fun ω' => mul_le_of_le_one_right' probOutput_le_one
  · calc Pr[= ω | ($ᵗ Chal : ProbComp Chal)] * _
        = _ * Pr[= ω | ($ᵗ Chal : ProbComp Chal)] := mul_comm _ _
      _ < 1 * Pr[= ω | ($ᵗ Chal : ProbComp Chal)] :=
          (ENNReal.mul_lt_mul_iff_left hpos.ne' probOutput_ne_top).2 hlt
      _ = Pr[= ω | ($ᵗ Chal : ProbComp Chal)] := one_mul _

/-- At `m := ProbComp`, the pointwise-challenge form `PerfectlyComplete` is equivalent to the
sampled form that draws the challenge uniformly and asks for acceptance probability `1`. -/
lemma perfectlyComplete_iff_probOutput_uniform_challenge_eq_one [SampleableType Chal]
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp) :
    σ.PerfectlyComplete ↔ ∀ x w, rel x w = true →
      Pr[= true | do
        let (pc, sc) ← σ.commit x w
        let ω ← $ᵗ Chal
        let π ← σ.respond x w sc ω
        return σ.verify x pc ω π] = 1 :=
  ⟨fun hc _ _ h => hc.probOutput_uniform_challenge_eq_one h,
    perfectlyComplete_of_probOutput_uniform_challenge_eq_one⟩

end complete

end ChallengeVerifyProtocol

namespace SigmaProtocol

variable {m : Type → Type} [Monad m]
  {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section speciallySound

/-- Special soundness at a particular statement: given two accepting transcripts with the same
commitment but different challenges, the extracted witness is valid. -/
def SpeciallySoundAt [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (x : Stmt) : Prop :=
  ∀ pc ω₁ ω₂ p₁ p₂, ω₁ ≠ ω₂ →
    σ.verify x pc ω₁ p₁ = true → σ.verify x pc ω₂ p₂ = true →
    ∀ w ∈ support (σ.extract ω₁ p₁ ω₂ p₂), rel x w = true

/-- A Σ-protocol is specially sound if `SpeciallySoundAt` holds for all statements. -/
def SpeciallySound [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel m) : Prop :=
  ∀ x, SpeciallySoundAt σ x

/-- Special soundness immediately validates any witness returned by the Σ-protocol extractor from
two accepting transcripts with the same statement and commitment and with distinct challenges. -/
theorem extract_sound_of_speciallySoundAt
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel m) {x : Stmt}
    (hss : σ.SpeciallySoundAt x)
    {pc : Commit} {ω₁ ω₂ : Chal} {p₁ p₂ : Resp} (hω : ω₁ ≠ ω₂)
    (hv₁ : σ.verify x pc ω₁ p₁ = true) (hv₂ : σ.verify x pc ω₂ p₂ = true)
    {w : Wit} (hw : w ∈ support (σ.extract ω₁ p₁ ω₂ p₂)) :
    rel x w = true :=
  hss pc ω₁ ω₂ p₁ p₂ hω hv₁ hv₂ w hw

end speciallySound

end SigmaProtocol

namespace ChallengeVerifyProtocol

variable {m : Type → Type} [Monad m]
  {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section hvzk

variable [SampleableType Chal] [MonadLiftT ProbComp m]

/-- The honest prover's transcript distribution. -/
def realTranscript (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (x : Stmt) (w : Wit) :
    m (Commit × Chal × Resp) := do
  let (pc, sc) ← σ.commit x w
  let ω ← (liftM ($ᵗ Chal) : m Chal)
  let π ← σ.respond x w sc ω
  return (pc, ω, π)

/-- At `m := ProbComp` the lifted challenge draw is the plain uniform sample, so `realTranscript`
is the ordinary Σ-protocol transcript distribution. -/
lemma realTranscript_probComp
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
    (x : Stmt) (w : Wit) :
    σ.realTranscript x w = do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Chal
      let π ← σ.respond x w sc ω
      return (pc, ω, π) := rfl

/-- Honest-verifier zero-knowledge: the real transcript distribution is within total variation
distance `ζ_zk` of the simulated one.

The real transcript is `σ.realTranscript x w`.
The simulated transcript is produced by `simTranscript` given only the statement `x`.

Note: the `sim` field of `SigmaProtocol` only produces a public commitment. For HVZK we need
a full transcript simulator `Stmt → m (Commit × Chal × Resp)`. We parameterize by this
simulator, which also keeps the property available on a bare `ChallengeVerifyProtocol`. -/
def HVZK [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) (ζ_zk : ℝ) : Prop :=
  ∀ x w, rel x w = true →
    tvDist (σ.realTranscript x w) (simTranscript x) ≤ ζ_zk

/-- Exact honest-verifier zero-knowledge: the real transcript distribution equals the
simulated one. -/
def PerfectHVZK [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) : Prop :=
  ∀ x w, rel x w = true →
    𝒮[σ.realTranscript x w] = 𝒮[simTranscript x]

/-- The perfect HVZK property is equivalent to the approximate HVZK property with `ζ_zk = 0`. -/
@[grind =]
lemma perfectHVZK_iff_hvzk_zero
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) :
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

The `_σ : ChallengeVerifyProtocol …` argument is dummy (the predicate only depends on
`simTranscript` and `β`); it is present to enable field-notation usage like
`σ.simCommitPredictability simTranscript β`. -/
def simCommitPredictability [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (_σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) (β : ℝ≥0∞) : Prop :=
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
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (_σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) : Prop :=
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
def UniqueResponses (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m) : Prop :=
  ∀ x pc ω p₁ p₂,
    σ.verify x pc ω p₁ = true → σ.verify x pc ω p₂ = true → p₁ = p₂

end uniqueResponses

section toIdenSchemeWithAbort

/-- Every `ProbComp`-valued `ChallengeVerifyProtocol` can be viewed as a non-aborting
`IdenSchemeWithAbort` by wrapping the response in `some`. -/
def toIdenSchemeWithAbort
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp) :
    IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel where
  commit := σ.commit
  respond := fun stmt wit prvState chal => some <$> σ.respond stmt wit prvState chal
  verify := σ.verify

instance : Coe (ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
    (IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) :=
  ⟨toIdenSchemeWithAbort⟩

end toIdenSchemeWithAbort

end ChallengeVerifyProtocol
