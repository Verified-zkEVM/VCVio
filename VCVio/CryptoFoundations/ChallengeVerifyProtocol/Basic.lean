/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import VCVio.CryptoFoundations.SigmaProtocol

/-!
# Soundness Of Challenge-Verify Protocols

`ChallengeVerifyProtocol`, the monad-generic commit–challenge–response interaction, is defined in
`VCVio.CryptoFoundations.SigmaProtocol` together with completeness, honest-verifier zero-knowledge,
and unique responses. This file adds the soundness notions that read a protocol as an interactive
*argument*:

- `ChallengeVerifyProtocol.Sound` / `ChallengeVerifyProtocol.PerfectlySound`: statistical soundness
  against arbitrary provers, obtained by quantifying existentially over the response once the
  challenge has been drawn from the verifier's challenge sampler, which these properties take as
  an argument.
- `ChallengeVerifyProtocol.SpeciallySoundAt` / `ChallengeVerifyProtocol.SpeciallySound`: special
  soundness relative to an extractor supplied as a parameter, for protocols whose interaction is
  not packaged with an extractor. When the extractor *is* bundled as data, use the corresponding
  `SigmaProtocol` properties instead.

These are the properties the Kilian transformation
(`VCVio.CryptoFoundations.ChallengeVerifyProtocol.Kilian`) is stated against.

## Probability assumptions

The conventions are those of `VCVio.CryptoFoundations.SigmaProtocol`. The soundness properties
bound the probability of an event over the verifier's challenge, so they are stated against the
measure semantics `[EvalDistSemantics m]`. Special soundness quantifies over the possible outputs
of the extractor, given by `[MonadAttach m]`, and needs no probability semantics.

`ChallengeVerifyProtocol` has no challenge-sampling field, and its completeness notion
`ChallengeVerifyProtocol.PerfectlyComplete` quantifies over the challenge pointwise. Soundness does
depend on how the verifier draws its challenge, so `ChallengeVerifyProtocol.Sound` and
`ChallengeVerifyProtocol.PerfectlySound` take the sampler `sampleChal : m Chal` as an argument.
-/

public section

universe u v

namespace ChallengeVerifyProtocol

variable {m : Type → Type} {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section sound

open scoped NNReal

variable [Monad m] [EvalDistSemantics m]

/-- Soundness of a challenge-verify protocol as an interactive argument, against arbitrary — even
computationally unbounded and adaptive — provers: for every statement outside the relation's
language and every adversarially chosen commitment, the probability over the verifier's challenge,
drawn by `sampleChal`, that *some* response would be accepted is at most `soundnessError`.

Because the protocol is public-coin and `verify` is deterministic, quantifying existentially over
the response after the challenge is drawn dominates every prover strategy, so no prover model is
needed: whatever computation produces the response, it can do no better than the best response for
the sampled challenge. -/
@[expose]
def Sound (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (sampleChal : m Chal) (soundnessError : ℝ≥0) : Prop :=
  ∀ x : Stmt, (¬ ∃ w : Wit, rel x w) → ∀ pc : Commit,
    Pr{let chal ← sampleChal}[∃ resp : Resp, σ.verify x pc chal resp = true]
      ≤ soundnessError

/-- A protocol is perfectly sound for the challenge sampler `sampleChal` if it is sound with no
error: outside the language, the set of challenges admitting any accepted response has probability
zero. -/
@[expose]
def PerfectlySound (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (sampleChal : m Chal) : Prop :=
  σ.Sound sampleChal 0

end sound

section speciallySound

variable [MonadAttach m]

/-- Special soundness at a particular statement, relative to an extractor `extract` that recovers a
witness from two accepting transcripts: given two accepting transcripts with the same commitment but
different challenges, the extracted witness is valid.

The extractor is taken as a parameter rather than being a field of `ChallengeVerifyProtocol`, since
a protocol's interaction (`commit`/`respond`/`verify`) is independent of any particular
witness-extraction strategy. For a protocol that does bundle an extractor, see
`SigmaProtocol.SpeciallySoundAt`. -/
@[expose]
def SpeciallySoundAt (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (extract : Chal → Resp → Chal → Resp → m Wit) (x : Stmt) : Prop :=
  ∀ pc ω₁ ω₂ p₁ p₂, ω₁ ≠ ω₂ →
    σ.verify x pc ω₁ p₁ = true → σ.verify x pc ω₂ p₂ = true →
    ∀ w ∈ support (extract ω₁ p₁ ω₂ p₂), rel x w = true

/-- A protocol is specially sound (relative to `extract`) if `SpeciallySoundAt` holds for all
statements. -/
@[expose]
def SpeciallySound (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (extract : Chal → Resp → Chal → Resp → m Wit) : Prop :=
  ∀ x, SpeciallySoundAt σ extract x

/-- Special soundness immediately validates any witness returned by the extractor from two accepting
transcripts with the same statement and commitment and with distinct challenges. -/
theorem extract_sound_of_speciallySoundAt
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    {extract : Chal → Resp → Chal → Resp → m Wit} {x : Stmt}
    (hss : σ.SpeciallySoundAt extract x)
    {pc : Commit} {ω₁ ω₂ : Chal} {p₁ p₂ : Resp} (hω : ω₁ ≠ ω₂)
    (hv₁ : σ.verify x pc ω₁ p₁ = true) (hv₂ : σ.verify x pc ω₂ p₂ = true)
    {w : Wit} (hw : w ∈ support (extract ω₁ p₁ ω₂ p₂)) :
    rel x w = true :=
  hss pc ω₁ ω₂ p₁ p₂ hω hv₁ hv₂ w hw

end speciallySound

end ChallengeVerifyProtocol
