/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Incomparable
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Defs.Measure
import VCVio.EvalDist.Monad.Map
import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Encoding error under explicit sampling

Definition 14 of ePrint 2025/055 (printed page 17) fixes every public parameter, message and
epoch and samples only the randomness. `ErrorAtMost` includes losslessness of that sampler.
`failureMass` alone records returned encoding failure; `missingMass` separately records
sampler divergence. The Boolean observation maps a returned randomizer to whether its attempt
fails, preserving missing mass. `UniformSampler` and `UniformErrorAtMost` state the finite uniform
specialization without imposing finiteness on `IncomparableEncoding`.
-/

public section

namespace GXMSS.Encoding

open ENNReal

universe v

variable {m : Type → Type v} [Monad m] {PP M R E : Type} {n radix : ℕ}

/-- The sampler has no missing output mass in the supplied runtime. -/
@[expose] def LosslessSampler (runtime : ProbCompRuntime m) {α : Type} (sample : m α) : Prop :=
  runtime.evalDist ((fun _ => True) <$> sample) {True} = 1

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

/-- Runtime laws needed to interpret successive draws as independent monadic sampling.
They are explicit because a bare `ProbCompRuntime` does not provide a monad morphism. -/
structure SamplingLaws (runtime : ProbCompRuntime m) : Prop where
  /-- Pure computations have their native Dirac denotation. -/
  pure_eq : ∀ {α : Type} (x : α),
    letI : MeasurableSpace α := ⊤
    runtime.evalDist (pure x) = MeasureTheory.Measure.dirac x
  /-- Sequential native events integrate their continuation-event masses, with no normalization. -/
  bind_eq : ∀ {α β : Type} (c : m α) (f : α → m β) (p : β → Prop),
    letI : MeasurableSpace α := ⊤
    runtime.evalDist (p <$> (c >>= f)) {True} =
      ∫⁻ x, runtime.evalDist (p <$> f x) {True} ∂runtime.evalDist c

namespace IncomparableEncoding

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

/-- Missing randomizer mass remains distinct from a returned encoding failure. -/
@[expose] noncomputable def missingMass (runtime : ProbCompRuntime m) (sample : m R) : ℝ≥0∞ :=
  1 - runtime.evalDist ((fun _ => True) <$> sample) {True}

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
      1 - missingMass runtime sample := by
  change runtime.evalDist (enc.failed pp msg ep <$> sample) {true} +
      runtime.evalDist (enc.failed pp msg ep <$> sample) {false} =
    1 - (1 - runtime.evalDist ((fun _ => True) <$> sample) {True})
  let : MeasurableSpace R := ⊤
  rw [runtime.evalDist_map (enc.failed pp msg ep) Measurable.of_discrete sample,
    MeasureTheory.Measure.apply_true_add_apply_false,
    runtime.evalDist_map (fun _ : R => True) Measurable.of_discrete sample]
  simp only [MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
    Set.preimage_univ,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
  have hpreimage : (fun _ : R => True) ⁻¹' ({True} : Set Prop) = Set.univ := by
    ext
    simp
  rw [hpreimage]
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top (runtime.evalDist_apply_univ_le_one sample)]

/-- Under losslessness, failure and success exhaust probability one. -/
theorem failureMass_add_successMass_eq_one (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (hl : LosslessSampler runtime sample)
    (pp : PP) (msg : M) (ep : E) :
    enc.failureMass runtime sample pp msg ep + enc.successMass runtime sample pp msg ep = 1 := by
  rw [failureMass_add_successMass]
  have hl' : runtime.evalDist ((fun _ => True) <$> sample) {True} = 1 := hl
  rw [missingMass, hl']
  simp

/-- Moving the observation inside the surface computation requires the runtime laws. -/
theorem failureMass_eq_runtime (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (_laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    enc.failureMass runtime sample pp msg ep =
      runtime.evalDist (sample >>= fun r => pure (enc.failed pp msg ep r)) {true} := by
  rw [failureMass_eq_probability]
  let : MeasurableSpace R := ⊤
  rw [runtime.evalDist_map (enc.failed pp msg ep) Measurable.of_discrete sample,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  calc
    runtime.evalDist sample ((enc.failed pp msg ep) ⁻¹' {true}) =
        ∫⁻ r, runtime.evalDist
          ((fun b : Bool => b = true) <$> pure (enc.failed pp msg ep r)) {True}
          ∂runtime.evalDist sample := by
      simp_rw [runtime.evalDist_map (fun b : Bool => b = true) Measurable.of_discrete]
      simp_rw [_laws.pure_eq]
      simp_rw [MeasureTheory.Measure.map_apply Measurable.of_discrete
        (MeasurableSet.singleton True)]
      simp_rw [MeasureTheory.Measure.dirac_apply' _ MeasurableSet.of_discrete]
      rw [← MeasureTheory.lintegral_indicator_one (μ := runtime.evalDist sample)
        (MeasurableSet.of_discrete
          (s := (enc.failed pp msg ep) ⁻¹' ({true} : Set Bool)))]
      apply MeasureTheory.lintegral_congr
      intro r
      by_cases h : enc.failed pp msg ep r = true <;>
        simp [h]
    _ = runtime.evalDist
        ((fun b : Bool => b = true) <$>
          (sample >>= fun r => pure (enc.failed pp msg ep r))) {True} :=
      (_laws.bind_eq sample (fun r => pure (enc.failed pp msg ep r))
        (fun b : Bool => b = true)).symm
    _ = runtime.evalDist (sample >>= fun r => pure (enc.failed pp msg ep r)) {true} := by
      rw [runtime.evalDist_map (fun b : Bool => b = true) Measurable.of_discrete,
        MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
      congr 1
      ext b
      cases b <;> simp

/-- Increasing the allowed error preserves the pointwise bound and losslessness. -/
theorem ErrorAtMost.mono {enc : IncomparableEncoding PP M R E n radix} {runtime : ProbCompRuntime m}
    {sample : m R} {δ δ' : ℝ≥0∞} (h : enc.ErrorAtMost runtime sample δ) (hle : δ ≤ δ') :
    enc.ErrorAtMost runtime sample δ' :=
  ⟨h.1, fun pp msg ep => (h.2 pp msg ep).trans hle⟩

end IncomparableEncoding

end GXMSS.Encoding
