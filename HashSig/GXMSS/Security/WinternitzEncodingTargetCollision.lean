/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.EncodingTargetCollisionReduction
public import HashSig.GXMSS.Encoding.Winternitz

/-!
# Checksum-word encoding collision bridge

The hash target predicate is always true. The full checksum word is used in the source game;
its payload projection is injective because the payload occupies the first coordinates.
-/

public section

namespace GXMSS.Encoding.WinternitzCollision

open TargetCollisionReduction

variable {PP M R E Tweak : Type} {n₀ w : ℕ}

/-- The full checksum word uniquely determines its hash payload. -/
theorem word_injective (hw : 0 < w) :
    Function.Injective (Winternitz.word (n₀ := n₀) hw) := by
  intro x y h
  funext i
  have hi := congrFun h (Fin.castAdd (Winternitz.checksumWidth n₀ w) i)
  simpa [Winternitz.word] using hi

/-- The accepted checksum encoding instantiates the shared bridge without a failure predicate. -/
@[expose] def bridge (params : Winternitz.Parameters PP M R E Tweak n₀ w)
    (hEpoch : Function.Injective params.epochToTweak) :
    Bridge PP M R E Tweak (Codeword n₀ (2 ^ w))
      (n₀ + Winternitz.checksumWidth n₀ w) (2 ^ w) where
  enc := Winternitz.encoding params
  th := params.thf
  epochToTweak := params.epochToTweak
  epochToTweak_injective := hEpoch
  accepts := fun _ => true
  word := Winternitz.word params.digitWidthPositive
  word_injective := word_injective params.digitWidthPositive
  value_eq := by
    intro pp msg r ep
    simp [Winternitz.value_eq_some]

/-- Identification with a uniformly sampled paper parameter requires this separate seed law. -/
@[expose] def UniformSeedLaw [Fintype PP]
    (params : Winternitz.Parameters PP M R E Tweak n₀ w) : Prop :=
  UniformSampler ProbCompRuntime.probComp params.thf.seedGen

/-- A checksum-word collision adversary transfers to the pinned SM-DT-rTCR game at the same
record and retry capacities, including zero. This native bound uses `thf.seedGen` directly and
does not require the separate uniform seed law. -/
theorem advantage_le_hash [SampleableType R]
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq (Codeword n₀ (2 ^ w))]
    (params : Winternitz.Parameters PP M R E Tweak n₀ w)
    (hEpoch : Function.Injective params.epochToTweak) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary
      (encodingProblem (bridge params hEpoch) p K)) :
    TargetCollisionResistance.advantage source ≤
      TweakableHash.SM_DT_RTCR_Advantage
        (reduction (bridge params hEpoch) p K source) :=
  TargetCollisionReduction.advantage_le_hash (bridge params hEpoch) p K source

end GXMSS.Encoding.WinternitzCollision
