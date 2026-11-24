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

Encoding retries run `FirstSuccess.runWith`, and the one-draw masses are the `FirstSuccess`
masses of `enc.attempt`, so every `FirstSuccess` retry law applies to encodings directly. This
file names the retry masses and states the laws that the GXMSS proofs use. `exhaustionMass` is
the probability that all `k` draws fail; `IncomparableEncoding.failureMass` is the one-draw
failure probability.
-/

public section

namespace IncomparableEncoding.Retry

open ENNReal VCVio.Algorithms

variable {PP M E : Type*} {R : Type} {n radix : ℕ} {m : Type → Type*} [Monad m]

/-- The probability that `k` retries all fail and return `none`. -/
@[expose] noncomputable def exhaustionMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  FirstSuccess.failureMass runtime (enc.retry sample pp msg ep k) id

/-- The probability that `k` retries return a word and its randomizer. -/
@[expose] noncomputable def successMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  FirstSuccess.successMass runtime (enc.retry sample pp msg ep k) id

/-- Exhaustion mass is the probability that the retry returns `none`. -/
theorem exhaustionMass_eq_probability (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    exhaustionMass enc runtime sample pp msg ep k =
      runtime.evalDist ((fun o => o = none) <$> enc.retry sample pp msg ep k) {True} :=
  FirstSuccess.failureMass_eq_probability runtime (enc.retry sample pp msg ep k) id

/-- `k` retries are all exhausted with the `k`-th power of the one-draw failure mass. -/
theorem exhaustionMass_eq_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    exhaustionMass enc runtime sample pp msg ep k =
      (enc.failureMass runtime sample pp msg ep) ^ k :=
  FirstSuccess.failureMass_runWith_eq_pow runtime laws sample (enc.attempt pp msg ep) k

/-- With a lossless sampler, `k` retries succeed with probability one minus the `k`-th power of
the one-draw failure mass. -/
theorem successMass_eq_one_sub_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : runtime.SamplingLaws) (sample : m R)
    (hl : LosslessSampler runtime sample) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep k =
      1 - (enc.failureMass runtime sample pp msg ep) ^ k := by
  have hm : FirstSuccess.missingMass runtime sample = 0 := by
    simp [FirstSuccess.missingMass, show runtime.evalDist ((fun _ => true) <$> sample) {true} = 1
      from hl]
  exact FirstSuccess.successMass_runWith_eq_one_sub_pow runtime laws sample
    (enc.attempt pp msg ep) hm k

end IncomparableEncoding.Retry
