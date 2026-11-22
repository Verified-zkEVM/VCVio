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
  challenge has been drawn uniformly.
- `ChallengeVerifyProtocol.SpeciallySoundAt` / `ChallengeVerifyProtocol.SpeciallySound`: special
  soundness relative to an extractor supplied as a parameter, for protocols whose interaction is
  not packaged with an extractor. When the extractor *is* bundled as data, use the corresponding
  `SigmaProtocol` properties instead.

`ChallengeVerifyProtocol.Sound` allows unbounded provers, so it is too strong for protocols whose
soundness rests on a computational or idealized assumption. The Kilian transformation is one such
protocol: its soundness is stated in the random-oracle model (`KilianTransformation_rom_sound`, in
`VCVio.CryptoFoundations.ChallengeVerifyProtocol.Kilian.Soundness`).

## Probability assumptions

The conventions are those of `VCVio.CryptoFoundations.SigmaProtocol`: the verifier's challenge is
uniform. The only randomness in the soundness properties is that challenge, since the commitment
and response are quantified and `verify` is deterministic. They therefore draw `$ᵗ Chal` in
`ProbComp` under `[SampleableType Chal]`, and need neither a lift into the participants' monad `m`
nor a probability semantics on it. Special soundness quantifies over the possible outputs of the
extractor, given by `[MonadAttach m]`, and needs no probability semantics.
-/

public section

universe u v

namespace ChallengeVerifyProtocol

variable {m : Type → Type} {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section sound

open scoped NNReal

variable [SampleableType Chal]

/-- Soundness of a challenge-verify protocol as an interactive argument, against arbitrary — even
computationally unbounded and adaptive — provers: for every statement outside the relation's
language and every adversarially chosen commitment, the probability over the verifier's uniform
challenge that *some* response would be accepted is at most `soundnessError`.

Because the protocol is public-coin and `verify` is deterministic, quantifying existentially over
the response after the challenge is drawn dominates every prover strategy, so no prover model is
needed: whatever computation produces the response, it can do no better than the best response for
the sampled challenge. -/
@[expose]
def Sound (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ x : Stmt, (¬ ∃ w : Wit, rel x w) → ∀ pc : Commit,
    Pr{let chal ← $ᵗ Chal}[∃ resp : Resp, σ.verify x pc chal resp = true]
      ≤ soundnessError

/-- A protocol is perfectly sound if it is sound with no error: outside the language, the set of
challenges admitting any accepted response has probability zero. -/
@[expose]
def PerfectlySound (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m) :
    Prop :=
  σ.Sound 0

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
