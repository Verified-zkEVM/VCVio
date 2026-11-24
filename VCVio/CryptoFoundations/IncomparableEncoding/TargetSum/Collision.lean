/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Basic
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction

/-!
# Target-collision resistance of the target-sum encoding

`bridge` connects the target-sum encoding to its message hash: the encoding accepts a hash output
when its digit sum is `target`, and the word is the hash output itself. `advantage_le_hash` then
bounds the target-collision advantage against the encoding by the SM-DT-rTCR advantage against the
message hash (Lemma 8 of DKKW25). The bound uses the hash's own seed sampler `thf.seedGen` and the
same record and retry capacities, including zero. A challenge whose retries all fail still uses up
a record.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 6 and Lemma 8. The statement of
  Lemma 8 names Construction 5, but the lemma is about the target-sum encoding, Construction 6.
-/

public section

namespace IncomparableEncoding.TargetSum

open IncomparableEncoding TargetCollisionReduction

variable {PP M R E Tweak : Type} {v w target : ℕ}

/-- The target-sum encoding as a `Bridge`: a hash output is accepted when its digit sum is
`target`, and its word is the hash output itself. -/
@[expose] def bridge (params : Parameters PP M R E Tweak v w target)
    (hEpoch : Function.Injective params.epochToTweak) :
    Bridge PP M R E Tweak (Codeword v (2 ^ w)) v (2 ^ w) where
  enc := encoding params
  th := params.thf
  epochToTweak := params.epochToTweak
  epochToTweak_injective := hEpoch
  accepts := accepts target
  word := id
  word_injective := Function.injective_id
  encode_eq := by
    intro pp msg r ep
    simp [encoding, accepts]

/-- Lemma 8 of DKKW25: a target-collision adversary against the target-sum encoding gives an
SM-DT-rTCR adversary against the message hash, with predicate `accepts target`, with at least the
same advantage, at the same record and retry capacities. -/
theorem advantage_le_hash [SampleableType R]
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq (Codeword v (2 ^ w))]
    (params : Parameters PP M R E Tweak v w target)
    (hEpoch : Function.Injective params.epochToTweak) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary
      (encodingProblem (bridge params hEpoch) p K)) :
    TargetCollisionResistance.advantage source ≤
      TweakableHash.SM_DT_RTCR_Advantage
        (reduction (bridge params hEpoch) p K source) :=
  TargetCollisionReduction.advantage_le_hash (bridge params hEpoch) p K source

end IncomparableEncoding.TargetSum
