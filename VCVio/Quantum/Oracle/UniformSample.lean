/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.Quantum.Oracle.Model

/-!
# Sampled quantum oracles and classical uniform sampling

`Quantum.sampledEvalDist R I x ρ` chooses the oracle parameter `ω : Ω` by Mathlib's uniform measure
`uniformOn Set.univ` (`VCVio.Quantum.Oracle.Model`). When `Ω` carries a classical uniform sampler
`SampleableType Ω`, that measure is the output measure `𝒟[$ᵗ Ω]` of the sampler, so each sampled
distribution is the sampler's output measure bound to the runtime distributions. These forms connect
the quantum random-oracle model to VCVio's classical experiments (`VCVio.Quantum.Oracle.Classical`).

## Main results

* `Quantum.sampledEvalDistMap_eq_bind_uniformSample` and
  `Quantum.sampledEvalDist_eq_bind_uniformSample`: the observed and leaf distributions.
* `Quantum.sampledEvalDistMap₂_eq_bind_uniformSample` and
  `Quantum.sampledEvalDist₂_eq_bind_uniformSample`: their fixed-final-register forms.
-/

public section

open MeasureTheory ProbabilityTheory

universe u v u₁ v₁ w w₁

namespace Quantum

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w} {A B : QReg}
  {α : Type w} {β : Type w₁}

variable {Ω : Type} [SampleableType Ω]

/-- For a classical uniform sampler, the observed finite mixture agrees with binding its
output measure to the observed runtime distributions. -/
theorem sampledEvalDistMap_eq_bind_uniformSample [MeasurableSpace β]
    (R : Ω → QuantumRuntime spec) (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A)
    (f : Ω → (Σ u, W u) → β) :
    sampledEvalDistMap R I x ρ f =
      letI : MeasurableSpace Ω := ⊤
      (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).evalDistMap I x ρ (f ω) := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledEvalDistMap, SampleableType.evalDist_uniformSample]

/-- For a classical uniform sampler, the leaf mixture agrees with binding its output measure
to the runtime leaf distributions. -/
theorem sampledEvalDist_eq_bind_uniformSample [MeasurableSpace (Σ u, W u)]
    (R : Ω → QuantumRuntime spec) (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) :
    sampledEvalDist R I x ρ =
      letI : MeasurableSpace Ω := ⊤
      (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).evalDist I x ρ := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledEvalDist, SampleableType.evalDist_uniformSample]

/-- The observed fixed-register mixture agrees with the classical uniform sampler followed
by the relabelled runtime distributions. -/
theorem sampledEvalDistMap₂_eq_bind_uniformSample [MeasurableSpace β]
    (R : Ω → QuantumRuntime spec) (I : L.Interp) (x : QuantumComp₂ L spec A B α) (ρ : SubState A)
    (f : Ω → α → β) :
    sampledEvalDistMap₂ R I x ρ f =
      letI : MeasurableSpace Ω := ⊤
      (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).evalDist₂ I (x.map (f ω)) ρ := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledEvalDistMap₂_eq_bind, SampleableType.evalDist_uniformSample]

/-- The fixed-register mixture agrees with the classical uniform sampler followed by the
runtime output distributions. -/
theorem sampledEvalDist₂_eq_bind_uniformSample [MeasurableSpace α]
    (R : Ω → QuantumRuntime spec) (I : L.Interp) (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    sampledEvalDist₂ R I x ρ =
      letI : MeasurableSpace Ω := ⊤
      (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).evalDist₂ I x ρ := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledEvalDist₂_eq_bind, SampleableType.evalDist_uniformSample]

end Quantum
