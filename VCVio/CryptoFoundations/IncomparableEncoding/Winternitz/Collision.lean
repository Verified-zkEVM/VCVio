/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz.Encoding
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction

/-!
# Target-collision resistance of the Winternitz encoding

`bridge` connects the Winternitz encoding to its message hash, with every hash output accepted.
`advantage_le_hash` then bounds the target-collision advantage against the encoding by the
SM-DT-rTCR advantage against the message hash (Lemma 6 of DKKW25). The bound uses the hash's own
seed sampler `thf.seedGen` and the same record and retry capacities, including zero.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 5 and Lemma 6.
-/

public section

namespace IncomparableEncoding.Winternitz

open IncomparableEncoding TargetCollisionReduction

variable {PP M R E Tweak : Type} {n₀ w : ℕ}

/-- The checksum word determines its payload. -/
theorem word_injective : Function.Injective (word (n₀ := n₀) (w := w)) := by
  intro x y h
  funext i
  simpa [word] using congrFun h (Fin.castAdd (checksumWidth n₀ w) i)

/-- The Winternitz encoding as a `Bridge`: every hash output is accepted, and its word is the
payload followed by its checksum digits. -/
@[expose] def bridge (params : Parameters PP M R E Tweak n₀ w)
    (hEpoch : Function.Injective params.epochToTweak) :
    Bridge PP M R E Tweak (Codeword n₀ (2 ^ w)) (n₀ + checksumWidth n₀ w) (2 ^ w) where
  enc := encoding params
  th := params.thf
  epochToTweak := params.epochToTweak
  epochToTweak_injective := hEpoch
  accepts := fun _ => true
  word := word
  word_injective := word_injective
  encode_eq _ _ _ _ := rfl

/-- Lemma 6 of DKKW25: a target-collision adversary against the Winternitz encoding gives an
SM-DT-rTCR adversary against the message hash with at least the same advantage, at the same
record and retry capacities. -/
theorem advantage_le_hash [SampleableType R]
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq (Codeword n₀ (2 ^ w))]
    (params : Parameters PP M R E Tweak n₀ w)
    (hEpoch : Function.Injective params.epochToTweak) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary
      (encodingProblem (bridge params hEpoch) p K)) :
    TargetCollisionResistance.advantage source ≤
      TweakableHash.SM_DT_RTCR_Advantage
        (reduction (bridge params hEpoch) p K source) :=
  TargetCollisionReduction.advantage_le_hash (bridge params hEpoch) p K source

end IncomparableEncoding.Winternitz
