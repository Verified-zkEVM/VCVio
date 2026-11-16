/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Retry.Basic
public import VCVio.CryptoFoundations.IncomparableEncoding.Error

/-!
# Probability laws for encoding retries

Encoding retries specialize the shared first-success mass laws. Returned exhaustion, success and
missing execution mass remain distinct; a canonical pointwise encoding bound controls exhaustion
without any additional uniformity premise.
-/

public section

namespace IncomparableEncoding.Retry

open ENNReal VCVio.Algorithms

variable {PP M R E : Type} {n radix : ℕ} {m : Type → Type*} [Monad m]

/-- Failure of a selected word/randomizer payload is exactly failure of the encoding value. -/
private theorem failureMass_attempt_eq (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    FirstSuccess.failureMass runtime sample (enc.attempt pp msg ep) =
      enc.failureMass runtime sample pp msg ep := by
  have hclass : (fun draw => (enc.attempt pp msg ep draw).isNone) = enc.failed pp msg ep := by
    funext draw
    simp [attempt, IncomparableEncoding.failed]
  unfold FirstSuccess.failureMass FirstSuccess.failureIndicatorDist
    IncomparableEncoding.failureMass IncomparableEncoding.failureIndicatorDist
  rw [hclass]

/-- Successful selected payloads have exactly the encoding's one-draw success mass. -/
private theorem successMass_attempt_eq (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    FirstSuccess.successMass runtime sample (enc.attempt pp msg ep) =
      enc.successMass runtime sample pp msg ep := by
  have hclass : (fun draw => (enc.attempt pp msg ep draw).isNone) = enc.failed pp msg ep := by
    funext draw
    simp [attempt, IncomparableEncoding.failed]
  unfold FirstSuccess.successMass FirstSuccess.failureIndicatorDist
    IncomparableEncoding.successMass IncomparableEncoding.failureIndicatorDist
  rw [hclass]

/-- Boolean exhaustion observation of the complete encoding retry program. -/
@[expose] noncomputable def failureIndicatorDist (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    MeasureTheory.Measure Bool :=
  FirstSuccess.failureIndicatorDist runtime (enc.retry sample pp msg ep k) id

/-- Unnormalized returned exhaustion mass. -/
@[expose] noncomputable def failureMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  FirstSuccess.failureMass runtime (enc.retry sample pp msg ep k) id

/-- Unnormalized returned word/randomizer mass. -/
@[expose] noncomputable def successMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  FirstSuccess.successMass runtime (enc.retry sample pp msg ep k) id

/-- Missing execution mass of encoding retries. -/
@[expose] noncomputable def missingMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  FirstSuccess.missingMass runtime (enc.retry sample pp msg ep k)

/-- The three retry observations retain all returned and missing mass. -/
theorem failureMass_add_missingMass_add_successMass
    (enc : IncomparableEncoding PP M R E n radix) (runtime : ProbCompRuntime m)
    (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k + missingMass enc runtime sample pp msg ep k +
      successMass enc runtime sample pp msg ep k = 1 :=
  FirstSuccess.failureMass_add_missingMass_add_successMass runtime (enc.retry sample pp msg ep k) id

/-- Exhaustion is exactly the returned optional none event. -/
theorem failureMass_eq_probability (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k =
      runtime.evalDist ((fun o => o = none) <$> enc.retry sample pp msg ep k) {True} :=
  FirstSuccess.failureMass_eq_probability runtime (enc.retry sample pp msg ep k) id

/-- Zero budget returns exhaustion without a draw. -/
theorem failureMass_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : failureMass enc runtime sample pp msg ep 0 = 1 :=
  FirstSuccess.failureMass_runWith_zero runtime laws sample (enc.attempt pp msg ep)

/-- Zero budget has no missing execution mass. -/
theorem missingMass_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : missingMass enc runtime sample pp msg ep 0 = 0 :=
  FirstSuccess.missingMass_runWith_zero runtime laws sample (enc.attempt pp msg ep)

/-- Zero budget returns no successful encoding. -/
theorem successMass_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : successMass enc runtime sample pp msg ep 0 = 0 :=
  FirstSuccess.successMass_runWith_zero runtime laws sample (enc.attempt pp msg ep)

/-- A further retry multiplies exhaustion by one-draw failure mass. -/
theorem failureMass_succ (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep (k + 1) =
      enc.failureMass runtime sample pp msg ep * failureMass enc runtime sample pp msg ep k := by
  simpa only [failureMass, retry, failureMass_attempt_eq] using
    FirstSuccess.failureMass_runWith_succ runtime laws sample (enc.attempt pp msg ep) k

/-- Exhaustion has the exact power of one-draw returned failure mass. -/
theorem failureMass_eq_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k =
      (enc.failureMass runtime sample pp msg ep) ^ k := by
  simpa only [failureMass, retry, failureMass_attempt_eq] using
    FirstSuccess.failureMass_runWith_eq_pow runtime laws sample (enc.attempt pp msg ep) k

/-- Missing mass comes from this draw or a later reached retry. -/
theorem missingMass_succ (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    missingMass enc runtime sample pp msg ep (k + 1) =
      IncomparableEncoding.missingMass runtime sample +
        enc.failureMass runtime sample pp msg ep * missingMass enc runtime sample pp msg ep k := by
  simpa only [missingMass, retry, IncomparableEncoding.missingMass, FirstSuccess.missingMass,
    failureMass_attempt_eq] using
    FirstSuccess.missingMass_runWith_succ runtime laws sample (enc.attempt pp msg ep) k

/-- Missing mass accumulates along returned-failure prefixes. -/
theorem missingMass_eq_mul_sum (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    missingMass enc runtime sample pp msg ep k =
      IncomparableEncoding.missingMass runtime sample *
        ∑ j ∈ Finset.range k, (enc.failureMass runtime sample pp msg ep) ^ j := by
  simpa only [missingMass, retry, IncomparableEncoding.missingMass, FirstSuccess.missingMass,
    failureMass_attempt_eq] using
    FirstSuccess.missingMass_runWith_eq_mul_sum runtime laws sample (enc.attempt pp msg ep) k

/-- A further retry succeeds immediately or after a returned failure. -/
theorem successMass_succ_aux (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep (k + 1) =
      enc.successMass runtime sample pp msg ep +
        enc.failureMass runtime sample pp msg ep * successMass enc runtime sample pp msg ep k := by
  simpa only [successMass, retry, failureMass_attempt_eq, successMass_attempt_eq] using
    FirstSuccess.successMass_runWith_succ runtime laws sample (enc.attempt pp msg ep) k

/-- Successful mass accumulates along returned-failure prefixes. -/
theorem successMass_eq_mul_sum (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep k =
      enc.successMass runtime sample pp msg ep *
        ∑ j ∈ Finset.range k, (enc.failureMass runtime sample pp msg ep) ^ j := by
  simpa only [successMass, retry, failureMass_attempt_eq, successMass_attempt_eq] using
    FirstSuccess.successMass_runWith_eq_mul_sum runtime laws sample (enc.attempt pp msg ep) k

/-- A one-draw pointwise bound controls returned exhaustion without a losslessness premise. -/
theorem failureMass_le_pow_of_le (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (δ : ℝ≥0∞)
    (h : enc.failureMass runtime sample pp msg ep ≤ δ) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k ≤ δ ^ k := by
  rw [failureMass_eq_pow enc runtime laws]
  exact pow_le_pow_left' h k

/-- An explicit-sampler encoding bound controls exhaustion at every fixed input. -/
theorem failureMass_le_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (δ : ℝ≥0∞) (h : enc.ErrorAtMost runtime sample δ)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k ≤ δ ^ k :=
  failureMass_le_pow_of_le enc runtime laws sample pp msg ep δ (h.2 pp msg ep) k

/-- Canonical pointwise encoding error controls canonical retry exhaustion. -/
theorem failureMass_uniformSample_le_pow [SampleableType R]
    (enc : IncomparableEncoding PP M R E n radix) (δ : ℝ≥0∞)
    (h : enc.CanonicalErrorAtMost δ) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc ProbCompRuntime.probComp ($ᵗ R) pp msg ep k ≤ δ ^ k :=
  failureMass_le_pow_of_le enc ProbCompRuntime.probComp ProbCompRuntime.samplingLaws_probComp
    ($ᵗ R) pp msg ep δ (h pp msg ep) k

/-- Lossless sampling prevents missing mass in every finite retry budget. -/
theorem missingMass_eq_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (hl : LosslessSampler runtime sample) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    missingMass enc runtime sample pp msg ep k = 0 := by
  apply FirstSuccess.missingMass_runWith_eq_zero runtime laws sample (enc.attempt pp msg ep) ?_ k
  simp [FirstSuccess.missingMass, show runtime.evalDist ((fun _ => true) <$> sample) {true} = 1
    from hl]

/-- Under losslessness, successful mass is one minus exact exhaustion mass. -/
theorem successMass_eq_one_sub_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (hl : LosslessSampler runtime sample) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep k =
      1 - (enc.failureMass runtime sample pp msg ep) ^ k := by
  have hm : FirstSuccess.missingMass runtime sample = 0 := by
    simp [FirstSuccess.missingMass, show runtime.evalDist ((fun _ => true) <$> sample) {true} = 1
      from hl]
  simpa only [successMass, retry, failureMass_attempt_eq] using
    FirstSuccess.successMass_runWith_eq_one_sub_pow runtime laws sample (enc.attempt pp msg ep) hm k

end IncomparableEncoding.Retry
