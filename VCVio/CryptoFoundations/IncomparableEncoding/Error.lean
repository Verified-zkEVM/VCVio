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
`failureMass` alone records returned encoding failure; `FirstSuccess.missingMass` separately
records sampler divergence. The Boolean observation maps a returned randomizer to whether its
attempt fails, preserving missing mass. `UniformSampler` and `UniformErrorAtMost` state the
finite uniform specialization without imposing finiteness on `IncomparableEncoding`.
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

/-- A returned randomizer is observed as encoding failure exactly when no word is returned. -/
@[expose] def failed (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (r : R) : Bool := (enc.value pp msg r ep).isNone

/-- The measure of the encoding-failure indicator after interpreting the randomizer sampler.
`true` denotes returned encoding failure and `false` denotes a returned codeword. Mapping with
`<$>` classifies returned randomizers; `𝒟` converts the resulting subdistribution to a measure.
Missing sampler mass remains missing, independently of the returned encoding-failure mass. -/
@[expose] noncomputable def failureIndicatorDist (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    MeasureTheory.Measure Bool := runtime.evalDist (enc.failed pp msg ep <$> sample)

/-- The probability of returned encoding failure, before any conditioning on termination. -/
@[expose] noncomputable def failureMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) : ℝ≥0∞ :=
  enc.failureIndicatorDist runtime sample pp msg ep {true}

/-- The probability of successful encoding from the same unnormalized observation. -/
@[expose] noncomputable def successMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) : ℝ≥0∞ :=
  enc.failureIndicatorDist runtime sample pp msg ep {false}

/-- Definition 14's pointwise error bound for a lossless explicit randomizer sampler. -/
@[expose] def ErrorAtMost (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (δ : ℝ≥0∞) : Prop :=
  LosslessSampler runtime sample ∧
    ∀ pp msg ep, enc.failureMass runtime sample pp msg ep ≤ δ

/-- Definition 14 specialized to the paper's uniform finite randomness space. -/
@[expose] def UniformErrorAtMost [Fintype R] (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (δ : ℝ≥0∞) : Prop :=
  UniformSampler runtime sample ∧ enc.ErrorAtMost runtime sample δ

/-- The error measure agrees with the Boolean output probability of the observation. -/
theorem failureMass_eq_probability (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    enc.failureMass runtime sample pp msg ep =
      runtime.evalDist (enc.failed pp msg ep <$> sample) {true} := rfl

/-- Returned error and successful encoding together retain precisely the returned sampler mass. -/
theorem failureMass_add_successMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    enc.failureMass runtime sample pp msg ep + enc.successMass runtime sample pp msg ep =
      1 - VCVio.Algorithms.FirstSuccess.missingMass runtime sample := by
  change runtime.evalDist (enc.failed pp msg ep <$> sample) {true} +
      runtime.evalDist (enc.failed pp msg ep <$> sample) {false} =
    1 - (1 - runtime.evalDist ((fun _ => true) <$> sample) {true})
  let : MeasurableSpace R := ⊤
  rw [runtime.evalDist_map (enc.failed pp msg ep) Measurable.of_discrete sample,
    MeasureTheory.Measure.apply_true_add_apply_false,
    runtime.evalDist_map (fun _ : R => true) Measurable.of_discrete sample]
  simp only [MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
    Set.preimage_univ,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpreimage : (fun _ : R => true) ⁻¹' ({true} : Set Bool) = Set.univ := by
    ext
    simp
  rw [hpreimage]
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top (runtime.evalDist_apply_univ_le_one sample)]

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
