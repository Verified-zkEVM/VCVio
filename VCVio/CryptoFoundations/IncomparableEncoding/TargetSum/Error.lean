/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Counting
public import VCVio.CryptoFoundations.IncomparableEncoding.Error
public import ToMathlib.Data.ENNReal.AbsDiff

/-!
# Target-sum error bound

`failureMass_le` is Lemma 7 of DKKW25. If the message hash is `ε`-close to uniform on every event
(`EpsilonUniform`), then one draw of the target-sum encoding fails with probability at most
`ε + 1 - η_T / 2^(wv)`. The bound holds for any randomizer sampler. Missing sampler mass is not
counted as failure; `IncomparableEncoding.ErrorAtMost` asks for a lossless sampler separately.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 6 and Lemma 7.
-/

public section

namespace IncomparableEncoding.TargetSum

open IncomparableEncoding

open ENNReal

variable {m : Type → Type} [Monad m] {PP M R E Tweak : Type} {v w target : ℕ}

/-- The probability that the hash output at tweak `tw` lands in `event`, over one draw of the
randomizer from `sample`. -/
@[expose] noncomputable def outputEventMass
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R)
    (pp : PP) (tw : Tweak) (msg : M)
    (event : Finset (Codeword v (2 ^ w))) : ℝ≥0∞ :=
  runtime.evalDist
    ((fun r => decide (p.thf.eval pp tw (msg, r) ∈ event)) <$> sample) {true}

/-- For every public parameter, tweak and message, the probability of each set of hash outputs
differs from its uniform probability by at most `ε`. This is the `ε`-uniformity premise of
DKKW25 (Definition 2). Statistical distance (`Measure.statEDist`, used by `measureETVDist`) is the
largest such difference over all events, so this premise says that each hash output distribution
is within statistical distance `ε` of uniform. The premise covers every tweak, not only those of
the form `epochToTweak ep`. -/
@[expose] def EpsilonUniform
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R) (ε : ℝ≥0∞) : Prop :=
  ∀ pp tw msg (event : Finset (Codeword v (2 ^ w))),
    ENNReal.absDiff (outputEventMass p runtime sample pp tw msg event)
      (uniformEventMass v w event) ≤ ε

/-- The encoding fails exactly when the hash output is a rejected word. -/
theorem failureMass_eq_rejectedEventMass
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    (encoding p).failureMass runtime sample pp msg ep =
      outputEventMass p runtime sample pp (p.epochToTweak ep) msg (rejectedWords v w target) := by
  rw [IncomparableEncoding.failureMass_eq_probability]
  have hobs : (fun r => ((encoding p).encode pp msg r ep).isNone) =
      fun r => decide (p.thf.eval pp (p.epochToTweak ep) (msg, r) ∈ rejectedWords v w target) := by
    funext r
    by_cases h : digitSum (p.thf.eval pp (p.epochToTweak ep) (msg, r)) = target <;>
      simp [encoding, rejectedWords, h]
  rw [hobs]
  rfl

/-- Lemma 7 of DKKW25: if the message hash is `ε`-uniform, then one draw of the target-sum
encoding fails with probability at most `ε + 1 - η_T / 2^(wv)`. -/
theorem failureMass_le
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R) (ε : ℝ≥0∞)
    (hε : EpsilonUniform p runtime sample ε) (pp : PP) (msg : M) (ep : E) :
    (encoding p).failureMass runtime sample pp msg ep ≤
      ε + uniformRejectionMass v w target := by
  rw [failureMass_eq_rejectedEventMass]
  calc
    outputEventMass p runtime sample pp (p.epochToTweak ep) msg (rejectedWords v w target) ≤
        uniformEventMass v w (rejectedWords v w target) + ε :=
      (ENNReal.absDiff_le_iff.mp
        (hε pp (p.epochToTweak ep) msg (rejectedWords v w target))).1
    _ = ε + uniformRejectionMass v w target := by
      rw [uniformRejected_eq_uniformRejectionMass]
      exact add_comm _ _

end IncomparableEncoding.TargetSum
