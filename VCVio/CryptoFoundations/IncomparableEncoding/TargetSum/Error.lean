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
# Target-sum error bounds

An explicit finite-event deviation premise bounds returned encoding failure. The sampler law
separately controls missing randomizer mass, retaining the unconditioned error observation.
-/

public section

namespace IncomparableEncoding.TargetSum

open IncomparableEncoding

open ENNReal

/-- The returned mass of an arbitrary finite hash-output event at any tweak, under
an explicit randomizer sampler. The Boolean observation avoids conditioning on success. -/
@[expose] noncomputable def outputEventMass {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R)
    (pp : PP) (tw : Tweak) (msg : M)
    (event : Finset (Codeword v (2 ^ w))) : ℝ≥0∞ :=
  runtime.evalDist
    ((fun r => decide (p.thf.eval pp tw (msg, r) ∈ event)) <$> sample) {true}

/-- Every hash-output event differs from the corresponding uniform word event by at
most `ε`, for every public parameter, tweak, and message. This is the finite
statistical-distance premise of Definition 2 of ePrint 2025/055. It quantifies
over the entire output alphabet, including events beyond epoch-reachable tweaks. -/
@[expose] def EpsilonUniform {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R) (ε : ℝ≥0∞) : Prop :=
  ∀ pp tw msg (event : Finset (Codeword v (2 ^ w))),
    ENNReal.absDiff (outputEventMass p runtime sample pp tw msg event)
      (uniformEventMass v w event) ≤ ε

/-- The rejected-output event is exactly the encoding's returned-failure event. -/
theorem failureMass_eq_rejectedEventMass {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    (encoding p).failureMass runtime sample pp msg ep =
      outputEventMass p runtime sample pp (p.epochToTweak ep) msg (rejectedWords v w target) := by
  rw [IncomparableEncoding.failureMass_eq_probability]
  have hobs : (encoding p).failed pp msg ep =
      fun r => decide (p.thf.eval pp (p.epochToTweak ep) (msg, r) ∈ rejectedWords v w target) := by
    funext r
    by_cases h : (∑ i : Fin v, (p.thf.eval pp (p.epochToTweak ep) (msg, r) i).val) = target
    · simp [IncomparableEncoding.failed, encoding, IncomparableEncoding.value,
        rejectedWords, h]
    · simp [IncomparableEncoding.failed, encoding, IncomparableEncoding.value,
        rejectedWords, h]
  rw [hobs]
  rfl

/-- A pointwise hash-event deviation bounds returned failure for any explicit sampler. -/
theorem failureMass_le {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {v w target : ℕ}
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

/-- A lossless uniform sampler gives the paper-facing error statement, including its
separate losslessness assertion. The pointwise failure estimate uses the event premise. -/
theorem uniformErrorAtMost {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} [Fintype R] {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R) (ε : ℝ≥0∞)
    (hu : UniformSampler runtime sample)
    (hε : EpsilonUniform p runtime sample ε) :
    (encoding p).UniformErrorAtMost runtime sample
      (ε + uniformRejectionMass v w target) :=
  ⟨hu, hu.1, failureMass_le p runtime sample ε hε⟩

/-- Canonical pointwise error under the explicit hash-output deviation premise. -/
theorem canonicalErrorAtMost
    {PP M R E Tweak : Type} [SampleableType R] {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target) (ε : ℝ≥0∞)
    (hε : EpsilonUniform p ProbCompRuntime.probComp ($ᵗ R) ε) :
    (encoding p).CanonicalErrorAtMost (ε + uniformRejectionMass v w target) :=
  failureMass_le p ProbCompRuntime.probComp ($ᵗ R) ε hε

/-- The pointwise error bound with VCVio's canonical finite uniform randomizer
sampler. Hash-output uniformity remains an explicit premise. -/
theorem probComp_uniformErrorAtMost
    {PP M R E Tweak : Type} [Fintype R] [SampleableType R] {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target) (ε : ℝ≥0∞)
    (hε : EpsilonUniform p ProbCompRuntime.probComp ($ᵗ R) ε) :
    (encoding p).UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R)
      (ε + uniformRejectionMass v w target) :=
  ((encoding p).uniformErrorAtMost_uniformSample_iff
    (ε + uniformRejectionMass v w target)).2 (canonicalErrorAtMost p ε hε)

end IncomparableEncoding.TargetSum
