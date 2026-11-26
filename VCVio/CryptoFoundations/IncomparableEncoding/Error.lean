/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Basic
public import VCVio.OracleComp.Constructions.FirstSuccess.Measure
public import ToMathlib.MeasureTheory.Measure.Bool
public import VCVio.EvalDist.Defs.Measure
public import VCVio.EvalDist.Monad.Map
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.ProbCompLift

/-!
# Encoding error under explicit sampling

Definition 14 of ePrint 2025/055 (printed page 17) fixes every public parameter, message and
epoch and samples only the randomness. `ErrorAtMost` includes losslessness of that sampler.
`failureMass` records only returned encoding failure; `FirstSuccess.missingMass` separately
records sampler divergence. Both one-draw masses are the `FirstSuccess` masses of `enc.attempt`.
`UniformSampler` and `UniformErrorAtMost` state the finite uniform specialization without
imposing finiteness on `IncomparableEncoding`.
-/

public section

namespace IncomparableEncoding

open ENNReal

universe v

variable {m : Type → Type v} [Monad m] {PP M E : Type*} {R : Type} {n radix : ℕ}

/-- The sampler has no missing output mass in the supplied runtime. -/
@[expose] def LosslessSampler (runtime : ProbCompRuntime m) {α : Type} (sample : m α) : Prop :=
  runtime.evalDist ((fun _ => true) <$> sample) {true} = 1

/-- Uniform finite sampling is lossless and assigns each element inverse-cardinality mass. -/
@[expose] def UniformSampler (runtime : ProbCompRuntime m) {α : Type} [Fintype α]
    (sample : m α) : Prop :=
  LosslessSampler runtime sample ∧
    ∀ x, runtime.evalDist ((fun y => y = x) <$> sample) {True} =
      (Fintype.card α : ℝ≥0∞)⁻¹

/-- The canonical type sampler has the specified uniform, lossless observation. -/
theorem uniformSampler_uniformSample (α : Type) [Fintype α] [SampleableType α] :
    UniformSampler ProbCompRuntime.probComp ($ᵗ α) := by
  constructor
  · simp [LosslessSampler]
  · intro x
    rw [ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_map]
    exact SampleableType.prEvent_uniformSample_eq_singleton x

/-- The probability that one draw from `sample` fails to encode. This is
`FirstSuccess.failureMass` with acceptance function `enc.attempt`, so the `FirstSuccess` retry
laws apply to it directly. Missing sampler mass is not counted as failure. -/
@[expose] noncomputable def failureMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) : ℝ≥0∞ :=
  VCVio.Algorithms.FirstSuccess.failureMass runtime sample (enc.attempt pp msg ep)

/-- The probability that one draw from `sample` encodes successfully. -/
@[expose] noncomputable def successMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) : ℝ≥0∞ :=
  VCVio.Algorithms.FirstSuccess.successMass runtime sample (enc.attempt pp msg ep)

/-- Definition 14's pointwise error bound for a lossless explicit randomizer sampler. -/
@[expose] def ErrorAtMost (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (δ : ℝ≥0∞) : Prop :=
  LosslessSampler runtime sample ∧
    ∀ pp msg ep, enc.failureMass runtime sample pp msg ep ≤ δ

/-- Definition 14 specialized to the paper's uniform finite randomness space. -/
@[expose] def UniformErrorAtMost [Fintype R] (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (δ : ℝ≥0∞) : Prop :=
  UniformSampler runtime sample ∧ enc.ErrorAtMost runtime sample δ

/-- One-draw failure mass is the probability that the drawn randomizer fails to encode. -/
theorem failureMass_eq_probability (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    enc.failureMass runtime sample pp msg ep =
      runtime.evalDist ((fun r => (enc.encode pp msg r ep).isNone) <$> sample) {true} := by
  simp only [failureMass, VCVio.Algorithms.FirstSuccess.failureMass,
    VCVio.Algorithms.FirstSuccess.failureIndicatorDist, isNone_attempt]

/-- Canonical pointwise failure bound, with only the encoding randomizer sampled. -/
@[expose] def CanonicalErrorAtMost [SampleableType R]
    (enc : IncomparableEncoding PP M R E n radix) (δ : ℝ≥0∞) : Prop :=
  ∀ pp msg ep, enc.failureMass ProbCompRuntime.probComp ($ᵗ R) pp msg ep ≤ δ

/-- Canonical sampling supplies the losslessness part of the explicit-sampler error predicate. -/
theorem errorAtMost_uniformSample_iff [SampleableType R]
    (enc : IncomparableEncoding PP M R E n radix) (δ : ℝ≥0∞) :
    enc.ErrorAtMost ProbCompRuntime.probComp ($ᵗ R) δ ↔ enc.CanonicalErrorAtMost δ := by
  simp [ErrorAtMost, CanonicalErrorAtMost, LosslessSampler]

/-- The uniform paper-facing bound agrees with the canonical pointwise bound. -/
theorem uniformErrorAtMost_uniformSample_iff [Fintype R] [SampleableType R]
    (enc : IncomparableEncoding PP M R E n radix) (δ : ℝ≥0∞) :
    enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) δ ↔
      enc.CanonicalErrorAtMost δ := by
  constructor
  · intro h
    exact (enc.errorAtMost_uniformSample_iff δ).1 h.2
  · intro h
    exact ⟨uniformSampler_uniformSample R, (enc.errorAtMost_uniformSample_iff δ).2 h⟩

end IncomparableEncoding
