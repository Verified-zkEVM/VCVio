/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.Quantum.Comp.QueryBound
public import VCVio.Quantum.Comp.Simulation
public import QuantumFoundations.Oracle.Unitary

/-!
# Sampled quantum oracles and the quantum random-oracle model

In the quantum random-oracle model (QROM), a function `H : X → Y` is sampled uniformly once, before
the program runs, and every call of the program is answered by the same `H`, through the unitary

`U_H |x, y⟩ = |x, y + H x⟩`.

The program may call `U_H` on a superposition of inputs. Nothing is measured by the oracle. Here
`X` is finite and `Y` is a finite additive commutative group. For bitstrings with addition modulo
two, `y + H x` is `y XOR H x`, and `U_H` is the usual oracle, which is its own inverse; for a
general group the inverse is `U_{-H}`.

## The experiment

The program `x`, its interpretation `I` and its input substate `ρ` are fixed first. Then:

* `Quantum.qromSpec X Y` is the signature: one port on the register `X × Y` (query input, then
  response), with result `Unit`. It names no function.
* `Quantum.additiveOracleRuntime H` is the runtime answering every call with `U_H`, with no
  private memory.
* `Quantum.qromEvalDist I x ρ` is the distribution of the leaf reached, averaged over `H`:
  `qromEvalDist I x ρ S = |Y|^(-|X|) * ∑_H (additiveOracleRuntime H).evalDist I x ρ S`.

This averages complete runs, each against one function; it does not sample afresh at each call.
The program brings its own workspace: a call exposes `X × Y` as a factor of its register and
carries the rest. Programs may be adaptive, allocate registers and make any number of calls on each
path (`VCVio.Quantum.Comp.Basic`).

## What is observed

`Quantum.qromEvalDist` is a measure on leaves `p = ⟨u, a⟩`, which record the final register and the
returned data. These distributions are subprobability measures: for a lossless program from a
normalized state the total mass is one (`Quantum.isProbabilityMeasure_qromEvalDist`).
`Quantum.qromEvalDistMap I x ρ f` observes `f H p` instead, so that the challenger can check a
relation between the returned data and the hidden function, such as `y = H x`; the program does not
receive `H`. Observations are sums of weighted point masses, so `f` need not be measurable. The
suffix `₂` gives the distribution of the returned value of a fixed-final-register program
(`Quantum.qromEvalDist₂`, `Quantum.qromEvalDistMap₂`).

## Other sampled oracles

`Quantum.sampledEvalDist R I x ρ` and `Quantum.sampledEvalDistMap` are the same construction for any
parameter type `Ω` and family of runtimes `R ω`, which may have private memory. The parameter has
the discrete measurable structure and may lie in any universe; its uniform measure is
`uniformOn Set.univ`, which is the zero measure unless `Ω` is finite and nonempty. The definitions
assume nothing about `Ω`; each theorem assumes the finiteness it uses. For a `SampleableType Ω`
in `Type`, this agrees with `𝒟[$ᵗ Ω]`. The QROM is the instance `R = additiveOracleRuntime`.
Showing that two implementations of an oracle are indistinguishable is an equation between two
values of `sampledEvalDist`.

## Main results

* `Quantum.qromEvalDist_eq_sum`: the distribution is the average over all functions of the
  distributions of the runs.
* `Quantum.qromEvalDist_apply_univ_of_lossless`: a lossless program has total mass the trace of its
  input; `Quantum.isProbabilityMeasure_qromEvalDist` for a normalized input.
* `Quantum.run_additiveOracleRuntime_eq_of_isQueryBound_zero`: a program that makes no calls runs
  in the same way against every function. Hence `Quantum.qromEvalDistMap_guess_zero`: such a program
  guesses a pair `(x, H x)` with probability its total weight divided by `|Y|`, which is `1 / |Y|`
  for a lossless program from a normalized state.
* `Quantum.evalDist_additiveOracleRuntime_eq_of_eqOn` and
  `Quantum.jointPost_additiveOracleRuntime_eq_of_eqOn`: if every call receives inputs in `S`
  (`Quantum.QueriesWithin`), the run against any `H'` that agrees with `H` on `S` has the same
  distribution and the same joint post-states.
* In `VCVio.Quantum.Oracle.Classical`, `Quantum.qromEvalDist₂_toQuantum_eq_randomOracle`: a
  classical algorithm has the same distribution in the QROM as under VCVio's lazily sampled random
  oracle.

The general-program results also have fixed-register forms with `₂` in their names.

## References

* D. Boneh, Ö. Dagdelen, M. Fischlin, A. Lehmann, C. Schaffner, M. Zhandry, *Random Oracles in a
  Quantum World*, ASIACRYPT 2011, arXiv:1008.0931v2, §2.1 (PDF p. 7), for bitstrings and XOR.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder

universe u v u₁ v₁ w w₁ uΩ

namespace Quantum

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w} {A B : QReg}
  {α : Type w} {β : Type w₁}

/-! ## Outcome distributions against a sampled runtime -/

section sampled

variable {Ω : Type uΩ}

/-- The observed output measure obtained by choosing a parameter `ω` uniformly from `Ω`, then
running the fixed program `x` under `I` against `R ω` from `ρ`. For finite `Ω` it is the mixture
`|Ω|⁻¹ • ∑ ω, (R ω).evalDistMap I x ρ (f ω)` (`Quantum.sampledEvalDistMap_eq_sum`); it is the
zero measure when `Ω` is empty or infinite.

The parameter is sampled once for the whole run. The observer sees `ω` and the classical
leaf, including its final-register label; the program receives neither through this
construction. Observations are sums of weighted point masses, so `f` need not be measurable.
The parameter and observation types may lie in independent universes. -/
@[expose]
noncomputable def sampledEvalDistMap
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    Measure β :=
  letI : MeasurableSpace Ω := ⊤
  (uniformOn (Set.univ : Set Ω)).bind fun ω ↦ (R ω).evalDistMap I x ρ (f ω)

/-- The distribution of the leaf reached by `x` when `ω` is drawn uniformly and the oracle is
realized by the runtime `R ω`: the mixture over `ω` of the outcome distributions of `x` under `I`
against `R ω` from `ρ`. -/
@[expose]
noncomputable def sampledEvalDist
    [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) : Measure (Σ u, W u) :=
  letI : MeasurableSpace Ω := ⊤
  (uniformOn (Set.univ : Set Ω)).bind fun ω ↦ (R ω).evalDist I x ρ

/-- Observing the leaf itself, without looking at the sampled value, gives the distribution of the
leaf. -/
theorem sampledEvalDistMap_id
    [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) :
    sampledEvalDistMap R I x ρ (fun _ p ↦ p) = sampledEvalDist R I x ρ :=
  rfl

/-- The observed distribution of a measurable set averages, over the sampled values, its measure
under the observed runs. -/
theorem sampledEvalDistMap_apply [Fintype Ω]
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) {s : Set β}
    (hs : MeasurableSet s) :
    sampledEvalDistMap R I x ρ f s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).evalDistMap I x ρ (f ω) s := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledEvalDistMap, uniformOn_univ_bind_apply _ _ hs]

/-- The observed distribution is the average, over the sampled values, of the observed distributions
of the runs. -/
theorem sampledEvalDistMap_eq_sum [Fintype Ω]
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    sampledEvalDistMap R I x ρ f =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).evalDistMap I x ρ (f ω) := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledEvalDistMap_apply _ _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]

/-- The distribution of a measurable set of leaves averages, over the sampled values, its measure
under the runs. -/
theorem sampledEvalDist_apply [Fintype Ω]
    [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) {s : Set (Σ u, W u)}
    (hs : MeasurableSet s) :
    sampledEvalDist R I x ρ s = ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).evalDist I x ρ s := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledEvalDist, uniformOn_univ_bind_apply _ _ hs]

/-- The distribution is the average, over the sampled values, of the outcome distributions of the
runs. -/
theorem sampledEvalDist_eq_sum [Fintype Ω]
    [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) :
    sampledEvalDist R I x ρ = (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).evalDist I x ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledEvalDist_apply _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

/-- When every run is lossless and every initial substate has trace `c`, the distribution has total
mass the trace of `ρ` times `c`. -/
theorem sampledEvalDist_apply_univ [Finite Ω] [Nonempty Ω]
    [MeasurableSpace (Σ u, W u)] {R : Ω → QuantumRuntime spec}
    {I : L.Interp} {x : QuantumComp L spec W A} (h : ∀ ω, ((R ω).run I x).Lossless) {c : ℝ}
    (hc : ∀ ω, (R ω).init.matrix.trace.re = c) (ρ : SubState A) :
    sampledEvalDist R I x ρ Set.univ = ENNReal.ofReal (ρ.matrix.trace.re * c) := by
  have := Fintype.ofFinite Ω
  rw [sampledEvalDist_apply _ _ _ _ MeasurableSet.univ]
  simp only [(R _).evalDist_apply_univ_of_lossless I (h _), hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-! ### Programs on a fixed final register -/

/-- The distribution of the value returned by the fixed-register program `x`, relabelled by a
function that sees the sampled value: the general observed distribution, reading each leaf `p`
through its value `(leafEquiv B α).symm p`. It is the mixture over `ω` of the outcome distributions
of `x.map (f ω)` (`Quantum.sampledEvalDistMap₂_eq_bind`). -/
@[expose]
noncomputable def sampledEvalDistMap₂
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) :
    Measure β :=
  sampledEvalDistMap R I x ρ fun ω p ↦ f ω ((QuantumComp₂.leafEquiv B α).symm p)

/-- The distribution of the value returned by the fixed-register program `x`: the general observed
distribution, reading each leaf through its value. It is the mixture over `ω` of the outcome
distributions of `x` (`Quantum.sampledEvalDist₂_eq_bind`). -/
@[expose]
noncomputable def sampledEvalDist₂
    [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) : Measure α :=
  sampledEvalDistMap R I x ρ fun _ p ↦ (QuantumComp₂.leafEquiv B α).symm p

/-- The relabelled distribution of a fixed-register program is the mixture of the outcome
distributions of its relabellings. -/
theorem sampledEvalDistMap₂_eq_bind
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) :
    sampledEvalDistMap₂ R I x ρ f =
      letI : MeasurableSpace Ω := ⊤
      (uniformOn (Set.univ : Set Ω)).bind fun ω ↦ (R ω).evalDist₂ I (x.map (f ω)) ρ := by
  simp only [QuantumRuntime.evalDist₂_map_eq_evalDistMap]
  rfl

/-- The distribution of the value of a fixed-register program is the mixture of its outcome
distributions. -/
theorem sampledEvalDist₂_eq_bind
    [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    sampledEvalDist₂ R I x ρ =
      letI : MeasurableSpace Ω := ⊤
      (uniformOn (Set.univ : Set Ω)).bind fun ω ↦ (R ω).evalDist₂ I x ρ := by
  simp only [QuantumRuntime.evalDist₂_eq_evalDistMap]
  rfl

/-- Relabelling the value without looking at the sampled value or changing it gives the distribution
of the value. -/
theorem sampledEvalDistMap₂_id
    [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    sampledEvalDistMap₂ R I x ρ (fun _ a ↦ a) = sampledEvalDist₂ R I x ρ :=
  rfl

/-- The relabelled distribution of a measurable set averages, over the sampled values, its measure
under the relabelled runs. -/
theorem sampledEvalDistMap₂_apply [Fintype Ω]
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) {s : Set β}
    (hs : MeasurableSet s) :
    sampledEvalDistMap₂ R I x ρ f s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).evalDist₂ I (x.map (f ω)) ρ s := by
  refine (sampledEvalDistMap_apply R I x ρ _ hs).trans ?_
  simp only [QuantumRuntime.evalDist₂_map_eq_evalDistMap]

/-- The relabelled distribution is the average, over the sampled values, of the outcome
distributions of the relabelled runs. -/
theorem sampledEvalDistMap₂_eq_sum [Fintype Ω]
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) :
    sampledEvalDistMap₂ R I x ρ f =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).evalDist₂ I (x.map (f ω)) ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledEvalDistMap₂_apply _ _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]

/-- The distribution of a measurable set of values averages, over the sampled values, its measure
under the runs. -/
theorem sampledEvalDist₂_apply [Fintype Ω]
    [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) {s : Set α} (hs : MeasurableSet s) :
    sampledEvalDist₂ R I x ρ s = ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).evalDist₂ I x ρ s := by
  refine (sampledEvalDistMap_apply R I x ρ _ hs).trans ?_
  simp only [QuantumRuntime.evalDist₂_eq_evalDistMap]

/-- The distribution of the value is the average, over the sampled values, of the outcome
distributions of the runs. -/
theorem sampledEvalDist₂_eq_sum [Fintype Ω]
    [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    sampledEvalDist₂ R I x ρ = (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).evalDist₂ I x ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledEvalDist₂_apply _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

/-- When every run is lossless and every initial substate has trace `c`, the distribution of the
value has total mass the trace of `ρ` times `c`. -/
theorem sampledEvalDist₂_apply_univ [Finite Ω] [Nonempty Ω]
    [MeasurableSpace α] {R : Ω → QuantumRuntime spec} {I : L.Interp}
    {x : QuantumComp₂ L spec A B α} (h : ∀ ω, ((R ω).run₂ I x).Lossless) {c : ℝ}
    (hc : ∀ ω, (R ω).init.matrix.trace.re = c) (ρ : SubState A) :
    sampledEvalDist₂ R I x ρ Set.univ = ENNReal.ofReal (ρ.matrix.trace.re * c) := by
  have := Fintype.ofFinite Ω
  rw [sampledEvalDist₂_apply _ _ _ _ MeasurableSet.univ]
  simp only [(R _).evalDist₂_apply_univ_of_lossless I (h _), hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

end sampled

/-! ### Agreement with classical uniform sampling -/

section sampleable

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

end sampleable

/-! ## Guessing a value of a uniform function -/

section guess

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y]

/-- A guess that does not depend on the function is right with probability the total weight
divided by `|Y|`: for weights `w i` on labels `i` that each carry a guess `(x i, y i)`, averaging
over all functions `H` the total weight of the labels with `y i = H (x i)` gives the total weight
divided by `|Y|`. -/
theorem sum_tsum_guess {ι : Type*} (w : ι → ℝ≥0∞) (x : ι → X) (y : ι → Y) :
    ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        ∑' i, w i * Set.indicator {True} 1 (y i = H (x i)) =
      (∑' i, w i) / Fintype.card Y := by
  classical
  have hcount : ∀ i, ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
      (if y i = H (x i) then 1 else 0) = (Fintype.card Y : ℝ≥0∞)⁻¹ := fun i ↦ by
    have hc : (Finset.univ.filter fun H : X → Y ↦ H (x i) = y i).card * Fintype.card Y =
        Fintype.card (X → Y) := by
      have h := Fintype.card_filter_piFinset_eq_of_mem (fun _ : X ↦ (Finset.univ : Finset Y))
        (x i) (Finset.mem_univ (y i))
      simp only [Fintype.piFinset_univ, Finset.card_univ] at h
      rw [h, Finset.prod_erase_mul _ _ (Finset.mem_univ _), Fintype.card_pi]
    have hfilter : (Finset.univ.filter fun H : X → Y ↦ y i = H (x i)) =
        Finset.univ.filter fun H : X → Y ↦ H (x i) = y i :=
      Finset.filter_congr fun _ _ ↦ eq_comm
    have hne : ((Finset.univ.filter fun H : X → Y ↦ H (x i) = y i).card : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun h0 ↦
        (Fintype.card_pos (α := X → Y)).ne' (by rw [← hc, h0, zero_mul])
    rw [← Finset.mul_sum, Finset.sum_boole, hfilter, ← hc, Nat.cast_mul,
      ENNReal.mul_inv (Or.inl hne) (Or.inl (ENNReal.natCast_ne_top _)), mul_right_comm,
      ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _), one_mul]
  have hterm : ∀ i, ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
      (w i * Set.indicator {True} 1 (y i = H (x i))) = w i * (Fintype.card Y : ℝ≥0∞)⁻¹ :=
    fun i ↦ by
      rw [← hcount i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun H _ ↦ ?_
      rw [mul_left_comm]
      congr 2
      by_cases h : y i = H (x i) <;> simp [h]
  simp only [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  simp only [hterm]
  rw [ENNReal.tsum_mul_right, div_eq_mul_inv]

/-- A guess that does not depend on the function is right with probability the total weight
divided by `|Y|`: for a subinstrument `P` on a substate `ρ`, averaging over all functions `H` the
weight with which the output `a` of `P` satisfies `y a = H (x a)` gives the trace of the total
output of `P` on `ρ` divided by `|Y|`. -/
theorem sum_outcomeMeasure_map_guess {M N : Type*} [Fintype M] [Fintype N]
    (P : SubInstrument M N α) (ρ : SubState M) (x : α → X) (y : α → Y) :
    ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        (P.map fun a ↦ y a = H (x a)).outcomeMeasure ρ {True} =
      ENNReal.ofReal (P.total ρ.matrix).trace.re / Fintype.card Y := by
  have hmeas : ∀ H : X → Y, (P.map fun a ↦ y a = H (x a)).outcomeMeasure ρ {True} =
      ∑' a, ENNReal.ofReal (P.branch a ρ.matrix).trace.re *
        Set.indicator {True} 1 (y a = H (x a)) := fun H ↦ by
    rw [DSubInstrument.outcomeMeasure_map, Measure.sum_apply _ (MeasurableSet.singleton True)]
    simp only [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton True),
      smul_eq_mul]
  simp only [hmeas]
  rw [sum_tsum_guess, DSubInstrument.trace_re_total_apply,
    ENNReal.ofReal_tsum_of_nonneg (fun a ↦ P.trace_re_branch_apply_nonneg a ρ.posSemidef)
      (P.isCPTNIFamily.summable_trace_re_apply ρ.posSemidef)]

end guess

/-! ## The quantum random-oracle model -/

section qrom

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The signature of a function oracle `X → Y`: one port, whose input and output register is `X × Y`
(query input, then response), and whose classical result is `Unit`. The response stays in the
quantum register; it is read only if the program measures it. The signature names no function:
`additiveOracleRuntime H` implements it for a fixed `H`, and `qromEvalDist` samples `H`. It is
reducible, so its ports, registers and results unfold when rewriting. -/
@[expose, reducible]
def qromSpec (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    QuantumOracleSpec.{0, 0} where
  Port := Unit
  In _ := QReg.of (X × Y)
  Out _ := QReg.of (X × Y)
  Result _ := Unit

variable [AddCommGroup Y]

/-- The oracle of a fixed function `H : X → Y`: every call applies the unitary
`U_H |x, y⟩ = |x, y + H x⟩` to the query register, that is `ρ ↦ U_H ρ U_H†`, and reports nothing.
The private register is `Unit`. Sampling `H` happens outside, in `qromEvalDist`.

For bitstrings with addition modulo two this is the XOR oracle, which is its own inverse. For a
general finite additive group the inverse is `U_{-H}`, and two calls need not cancel. See
`oracleUnitary_mulVec_single` (action on basis states), `conjTranspose_oracleUnitary` (inverse) and
`lossless_additiveOracleRuntime_step`. -/
@[expose]
noncomputable def additiveOracleRuntime (H : X → Y) : QuantumRuntime (qromSpec X Y) where
  D := QReg.of Unit
  init := SubState.basis ()
  step _ := (oracleQuery H).frame Unit

/-- The step of the oracle runtime is the oracle unitary, framed by the trivial register. -/
theorem additiveOracleRuntime_step (H : X → Y) (i : Unit) :
    (additiveOracleRuntime H).step i = (oracleQuery H).frame Unit :=
  rfl

/-- The private register of the oracle runtime starts in its unique basis state. -/
theorem additiveOracleRuntime_init (H : X → Y) : (additiveOracleRuntime H).init = SubState.basis
  () :=
  rfl

/-- The steps of the oracle runtime are lossless. -/
theorem lossless_additiveOracleRuntime_step (H : X → Y) (i : Unit) : ((additiveOracleRuntime
  H).step i).Lossless :=
  (lossless_oracleQuery H).frame Unit

/-- A lossless program runs against the oracle runtime to a lossless dependent subinstrument. -/
theorem lossless_run_additiveOracleRuntime (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    (hx : x.Lossless I) (H : X → Y) : ((additiveOracleRuntime H).run I x).Lossless :=
  (additiveOracleRuntime H).lossless_run I hx (lossless_additiveOracleRuntime_step H)

/-- A lossless fixed-register program runs against the oracle runtime to a lossless
subinstrument. -/
theorem lossless_run₂_additiveOracleRuntime (I : L.Interp) {x : QuantumComp₂ L (qromSpec X Y) A B α}
    (hx : x.Lossless I) (H : X → Y) : ((additiveOracleRuntime H).run₂ I x).Lossless :=
  (additiveOracleRuntime H).lossless_run₂ I hx (lossless_additiveOracleRuntime_step H)

/-- The initial substate of the oracle runtime has trace one. -/
theorem trace_re_additiveOracleRuntime_init (H : X → Y) : (additiveOracleRuntime
  H).init.matrix.trace.re = 1 :=
  (congrArg Complex.re (SubState.trace_basis (A := Unit) ())).trans Complex.one_re

section sampled

/-- The distribution of an observation of the leaf reached by `x` from `ρ` in the quantum
random-oracle model: `H : X → Y` is drawn uniformly, the program runs under `I` against the oracle
unitary of `H`, and its leaf `p` is reported as `f H p`. -/
@[expose]
noncomputable def qromEvalDistMap
    [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (X → Y) → (Σ u, W u) → β) :
    Measure β :=
  sampledEvalDistMap additiveOracleRuntime I x ρ f

/-- The distribution of the leaf a program reaches in the quantum random-oracle model. With `I`, `x`
and `ρ` fixed, a function `H : X → Y` is sampled uniformly once, and `x` runs against
`additiveOracleRuntime H`: a set `S` of leaves has weight `|Y|^(-|X|) * ∑_H (additiveOracleRuntime
H).evalDist I x ρ S` (`qromEvalDist_eq_sum`).

A leaf records the final register and returned data; the final quantum state is kept by `jointPost`
and `reducedPost`. Use `qromEvalDistMap` for an observation that also sees `H`, and `qromEvalDist₂`
for the returned value of a fixed-final-register program. The distribution is a subprobability
measure; for a lossless program its total mass is `tr ρ`. -/
@[expose]
noncomputable def qromEvalDist
    [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) : Measure (Σ u, W u) :=
  sampledEvalDist additiveOracleRuntime I x ρ

/-- Observing the leaf itself, without looking at the random function, gives the distribution of the
quantum random-oracle model. -/
theorem qromEvalDistMap_id
    [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) :
    qromEvalDistMap I x ρ (fun _ p ↦ p) = qromEvalDist I x ρ :=
  sampledEvalDistMap_id _ I x ρ

/-- The distribution of the quantum random-oracle model is the average, over all `|Y| ^ |X|`
functions, of the outcome distributions of the runs against their oracle unitaries. -/
theorem qromEvalDist_eq_sum
    [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) :
    qromEvalDist I x ρ =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (additiveOracleRuntime H).evalDist I x ρ := by
  rw [qromEvalDist, sampledEvalDist_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- The observed distribution of the quantum random-oracle model is the average, over all `|Y| ^
|X|` functions, of the observed distributions of the runs. -/
theorem qromEvalDistMap_eq_sum
    [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (X → Y) → (Σ u, W u) → β) :
    qromEvalDistMap I x ρ f =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (additiveOracleRuntime H).evalDistMap I x ρ (f H) := by
  rw [qromEvalDistMap, sampledEvalDistMap_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- When the run against every function is lossless, the distribution of the quantum random-oracle
model has total mass the trace of the initial substate. -/
theorem qromEvalDist_apply_univ
    [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (qromSpec X Y) W A} (h : ∀ H, ((additiveOracleRuntime H).run I x).Lossless)
    (ρ : SubState A) : qromEvalDist I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [qromEvalDist, sampledEvalDist_apply_univ h trace_re_additiveOracleRuntime_init, mul_one]

/-- The distribution of a lossless program has total mass the trace of the initial substate. -/
theorem qromEvalDist_apply_univ_of_lossless
    [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.Lossless I) (ρ : SubState A) :
    qromEvalDist I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re :=
  qromEvalDist_apply_univ (lossless_run_additiveOracleRuntime I hx) ρ

/-- When the run against every function is lossless and the initial state is normalized, the
distribution of the quantum random-oracle model is a probability measure. -/
theorem isProbabilityMeasure_qromEvalDist
    [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (qromSpec X Y) W A} (h : ∀ H, ((additiveOracleRuntime H).run I x).Lossless)
    {ρ : SubState A} (hρ : ρ.matrix.trace = 1) : IsProbabilityMeasure (qromEvalDist I x ρ) :=
  ⟨by rw [qromEvalDist_apply_univ h, hρ, Complex.one_re, ENNReal.ofReal_one]⟩

/-! #### Programs on a fixed final register -/

/-- The distribution of the value returned by the fixed-register program `x` in the quantum
random-oracle model, relabelled by a function that sees the random function: the general observed
distribution, reading each leaf through its value (`Quantum.qromEvalDistMap₂_eq_qromEvalDistMap`).
-/
@[expose]
noncomputable def qromEvalDistMap₂
    [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) (f : (X → Y) → α → β) :
    Measure β :=
  sampledEvalDistMap₂ additiveOracleRuntime I x ρ f

/-- The distribution of the value returned by the fixed-register program `x` in the quantum
random-oracle model: the general observed distribution, reading each leaf through its value
(`Quantum.qromEvalDist₂_eq_qromEvalDistMap`). -/
@[expose]
noncomputable def qromEvalDist₂
    [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) : Measure α :=
  sampledEvalDist₂ additiveOracleRuntime I x ρ

/-- The relabelled distribution of a fixed-register program is the general observed distribution,
reading each leaf through its value. -/
theorem qromEvalDistMap₂_eq_qromEvalDistMap
    [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) (f : (X → Y) → α → β) :
    qromEvalDistMap₂ I x ρ f =
      qromEvalDistMap I x ρ fun H p ↦ f H ((QuantumComp₂.leafEquiv B α).symm p) :=
  rfl

/-- The distribution of the value of a fixed-register program is the general observed distribution,
reading each leaf through its value. -/
theorem qromEvalDist₂_eq_qromEvalDistMap
    [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    qromEvalDist₂ I x ρ = qromEvalDistMap I x ρ fun _ p ↦ (QuantumComp₂.leafEquiv B α).symm p :=
  rfl

/-- Relabelling the value without looking at the random function or changing it gives the
distribution of the value. -/
theorem qromEvalDistMap₂_id
    [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    qromEvalDistMap₂ I x ρ (fun _ a ↦ a) = qromEvalDist₂ I x ρ :=
  rfl

/-- The distribution of the value is the average, over all `|Y| ^ |X|` functions, of the outcome
distributions of the runs against their oracle unitaries. -/
theorem qromEvalDist₂_eq_sum
    [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    qromEvalDist₂ I x ρ =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (additiveOracleRuntime H).evalDist₂ I x ρ := by
  rw [qromEvalDist₂, sampledEvalDist₂_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- The relabelled distribution of the value is the average, over all `|Y| ^ |X|` functions, of the
outcome distributions of the relabelled runs. -/
theorem qromEvalDistMap₂_eq_sum
    [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) (f : (X → Y) → α → β) :
    qromEvalDistMap₂ I x ρ f =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (additiveOracleRuntime H).evalDist₂ I (x.map (f H)) ρ := by
  rw [qromEvalDistMap₂, sampledEvalDistMap₂_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- When the run against every function is lossless, the distribution of the value has total mass
the trace of the initial substate. -/
theorem qromEvalDist₂_apply_univ
    [MeasurableSpace α] {I : L.Interp}
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (h : ∀ H, ((additiveOracleRuntime H).run₂ I
      x).Lossless)
    (ρ : SubState A) : qromEvalDist₂ I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [qromEvalDist₂, sampledEvalDist₂_apply_univ h trace_re_additiveOracleRuntime_init, mul_one]

/-- The distribution of the value of a lossless fixed-register program has total mass the trace of
the initial substate. -/
theorem qromEvalDist₂_apply_univ_of_lossless
    [MeasurableSpace α] {I : L.Interp}
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.Lossless I) (ρ : SubState A) :
    qromEvalDist₂ I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re :=
  qromEvalDist₂_apply_univ (lossless_run₂_additiveOracleRuntime I hx) ρ

/-- When the run against every function is lossless and the initial state is normalized, the
distribution of the value is a probability measure. -/
theorem isProbabilityMeasure_qromEvalDist₂
    [MeasurableSpace α] {I : L.Interp}
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (h : ∀ H, ((additiveOracleRuntime H).run₂ I
      x).Lossless)
    {ρ : SubState A} (hρ : ρ.matrix.trace = 1) : IsProbabilityMeasure (qromEvalDist₂ I x ρ) :=
  ⟨by rw [qromEvalDist₂_apply_univ h, hρ, Complex.one_re, ENNReal.ofReal_one]⟩

end sampled

/-! ### No queries -/

/-- **No queries, no dependence on the oracle.** A program with query budget zero runs to the
same dependent subinstrument against every function. -/
theorem run_additiveOracleRuntime_eq_of_isQueryBound_zero (I : L.Interp) {x : QuantumComp L
  (qromSpec X Y) W A}
    (hx : x.IsQueryBound 0) (H H' : X → Y) :
    (additiveOracleRuntime H).run I x = (additiveOracleRuntime H').run I x :=
  QuantumRuntime.run_congr_of_isQueryBound I hx fun _ h ↦ absurd rfl h

/-- **No queries, no dependence on the oracle**, for fixed-register programs: the runs against
every function are the same subinstrument. -/
theorem run₂_additiveOracleRuntime_eq_of_isQueryBound_zero (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.IsQueryBound 0) (H H' : X → Y) :
    (additiveOracleRuntime H).run₂ I x = (additiveOracleRuntime H').run₂ I x :=
  QuantumRuntime.run₂_congr_of_isQueryBound I hx fun _ h ↦ absurd rfl h

/-- A zero-query program guesses a value of the uniform random function with probability
`w / |Y|`, where `w` is the total successful weight of its run from `ρ`:
`Pr[gy(p) = H(gx(p))] = w / |Y|`.

The program, its interpretation and its input are fixed independently of `H`. The run is
independent of `H`, so `w` can be computed against any reference function `H₀` as the sum of
branch traces from `ρ ⊗ |()⟩⟨()|`. Failure and subnormalized input reduce this weight.

The guess functions read the classical leaf `p = ⟨u, a⟩`, including the register label `u`;
they do not receive or measure the quantum state on `u`. For a lossless program with a
normalized input, `qromEvalDistMap_guess_zero_of_trace_eq_one` gives `w = 1`. -/
theorem qromEvalDistMap_guess_zero (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.IsQueryBound 0) (ρ : SubState A)
    (gx : (Σ u, W u) → X) (gy : (Σ u, W u) → Y) (H₀ : X → Y) :
    qromEvalDistMap I x ρ (fun H p ↦ gy p = H (gx p)) {True} =
      ENNReal.ofReal
          (MatrixMap.familyTrace ((additiveOracleRuntime H₀).run I x).branch
            (ρ.prod (SubState.basis ())).matrix).re /
        Fintype.card Y := by
  have hw : ∀ (H : X → Y) (p : Σ u, W u),
      (additiveOracleRuntime H).jointPost I x ρ p = (additiveOracleRuntime H₀).jointPost I x ρ p
        := fun H p ↦ by
    unfold QuantumRuntime.jointPost
    rw [run_additiveOracleRuntime_eq_of_isQueryBound_zero I hx H H₀]
    rfl
  rw [qromEvalDistMap, sampledEvalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True)]
  simp only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True)]
  refine (Finset.sum_congr rfl fun H _ ↦ congrArg _ (tsum_congr fun p ↦ by rw [hw H p]; rfl)).trans
    ((sum_tsum_guess (fun p ↦ ENNReal.ofReal ((additiveOracleRuntime H₀).jointPost I x ρ
      p).matrix.trace.re)
      gx gy).trans ?_)
  exact congrArg (· / (Fintype.card Y : ℝ≥0∞)) ((additiveOracleRuntime H₀).tsum_jointPost_trace I
    x ρ)

/-- A lossless program with query budget zero guesses a value of the random function with
probability the trace of its initial substate divided by `|Y|`. -/
theorem qromEvalDistMap_guess_zero_of_lossless (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (ρ : SubState A) (gx : (Σ u, W u) → X) (gy : (Σ u, W u) → Y) :
    qromEvalDistMap I x ρ (fun H p ↦ gy p = H (gx p)) {True} =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card Y := by
  have h : (ρ.prod (SubState.basis ())).matrix.trace.re = ρ.matrix.trace.re := by
    rw [SubState.trace_re_prod, SubState.trace_basis, Complex.one_re, mul_one]
  rw [qromEvalDistMap_guess_zero I hx ρ gx gy 0,
    lossless_run_additiveOracleRuntime I hl 0 (ρ.prod (SubState.basis ())).matrix]
  exact congrArg (fun r ↦ ENNReal.ofReal r / (Fintype.card Y : ℝ≥0∞)) h

/-- In the quantum random-oracle model, a lossless program with query budget zero that starts
from a normalized state and whose leaf `p` carries a guess `(gx p, gy p)` satisfies
`gy p = H (gx p)` with probability `1 / |Y|`. -/
theorem qromEvalDistMap_guess_zero_of_trace_eq_one (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (gx : (Σ u, W u) → X) (gy : (Σ u, W u) → Y) {ρ : SubState A} (hρ : ρ.matrix.trace = 1) :
    qromEvalDistMap I x ρ (fun H p ↦ gy p = H (gx p)) {True} = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  rw [qromEvalDistMap_guess_zero_of_lossless I hx hl ρ gx gy, hρ]
  simp

/-- **No queries, no knowledge of the oracle**, for the value returned by a fixed-register
program: a guess `(gx a, gy a)` satisfies `gy a = H (gx a)` with probability the total weight of
the run divided by `|Y|`. -/
theorem qromEvalDistMap₂_guess_zero (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.IsQueryBound 0) (ρ : SubState A)
    (gx : α → X) (gy : α → Y) (H₀ : X → Y) :
    qromEvalDistMap₂ I x ρ (fun H a ↦ gy a = H (gx a)) {True} =
      ENNReal.ofReal
          (((additiveOracleRuntime H₀).run₂ I x).total (ρ.prod (SubState.basis
            ())).matrix).trace.re /
        Fintype.card Y := by
  have hrun : ∀ H : X → Y, (additiveOracleRuntime H).evalDist₂ I (x.map fun a ↦ gy a = H (gx a))
    ρ =
      (((additiveOracleRuntime H₀).run₂ I x).map fun a ↦
        gy a = H (gx a)).outcomeMeasure (ρ.prod (SubState.basis ())) := fun H ↦ by
    rw [QuantumRuntime.evalDist₂, QuantumRuntime.run₂_map,
      run₂_additiveOracleRuntime_eq_of_isQueryBound_zero I hx H H₀]
    rfl
  rw [qromEvalDistMap₂, sampledEvalDistMap₂_apply _ _ _ _ _ (MeasurableSet.singleton True)]
  simp only [hrun]
  exact sum_outcomeMeasure_map_guess _ _ gx gy

/-- A lossless fixed-register program with query budget zero guesses a value of the random
function with probability the trace of its initial substate divided by `|Y|`. -/
theorem qromEvalDistMap₂_guess_zero_of_lossless (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (ρ : SubState A) (gx : α → X) (gy : α → Y) :
    qromEvalDistMap₂ I x ρ (fun H a ↦ gy a = H (gx a)) {True} =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card Y := by
  have h : (((additiveOracleRuntime 0).run₂ I x).total (ρ.prod (SubState.basis ())).matrix).trace =
      (ρ.prod (SubState.basis ())).matrix.trace :=
    (DSubInstrument.lossless_iff_isTP_total _).mp
      (lossless_run₂_additiveOracleRuntime I hl 0) _
  rw [qromEvalDistMap₂_guess_zero I hx ρ gx gy 0, h, SubState.trace_re_prod, SubState.trace_basis,
    Complex.one_re, mul_one]

/-- A lossless fixed-register program with query budget zero that starts from a normalized state
and returns a guess `(x, y)` satisfies `y = H x` with probability `1 / |Y|`. -/
theorem qromEvalDistMap₂_guess_zero_of_trace_eq_one (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B (X × Y)} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    {ρ : SubState A} (hρ : ρ.matrix.trace = 1) :
    qromEvalDistMap₂ I x ρ (fun H a ↦ a.2 = H a.1) {True} = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  rw [qromEvalDistMap₂_guess_zero_of_lossless I hx hl ρ Prod.fst Prod.snd, hρ]
  simp

/-! ### The oracle is only seen where it is queried -/

/-- Every call along every branch of the run of `x` under `I` against `H` from `ρ` receives an
operator supported on the query inputs in `S`: before each call, the joint operator of the query
register, the runtime register and the carried remainder vanishes outside query inputs in `S`.
The input `ρ ⊗ |()⟩⟨()|` is positive semidefinite, so branches of weight zero receive the zero
operator and impose nothing. -/
@[expose]
def QueriesWithin (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A) (S : Set X) (H : X → Y)
    (ρ : SubState A) : Prop :=
  (additiveOracleRuntime H).ForallQueries I
    (fun _ E σ ↦ QuerySupportedOn (fun m : ((X × Y) × Unit) × E ↦ m.1.1.1) S σ) x
    (ρ.prod (SubState.basis ())).matrix

variable {S : Set X} {H H' : X → Y}

/-- On an operator supported on the query inputs in `S`, a call of the oracle runtime of `H`,
framed by any remainder, only depends on the restriction of `H` to `S`. -/
theorem additiveOracleRuntime_step_frame_congr (hH : Set.EqOn H H' S) (i : (qromSpec X Y).Port) (E
  : QReg)
    {σ : Matrix (((X × Y) × Unit) × E) (((X × Y) × Unit) × E) ℂ}
    (hσ : QuerySupportedOn (fun m : ((X × Y) × Unit) × E ↦ m.1.1.1) S σ) (r : Unit) :
    (((additiveOracleRuntime H).step i).frame E).branch r σ =
      (((additiveOracleRuntime H').step i).frame E).branch r σ := by
  change (((oracleQuery H).frame Unit).frame E).branch r σ =
    (((oracleQuery H').frame Unit).frame E).branch r σ
  rw [DSubInstrument.branch_frame_apply, DSubInstrument.branch_frame_apply,
    DSubInstrument.branch_frame_apply, DSubInstrument.branch_frame_apply, branch_oracleQuery_apply,
    branch_oracleQuery_apply]
  ext m m'
  rw [MatrixMap.amplify_apply _ σ m m', MatrixMap.amplify_apply _ σ m m',
    amplify_conj_oracleUnitary_congr hH
      (QuerySupportedOn.block (q := fun n : (X × Y) × Unit ↦ n.1.1) hσ m.2 m'.2)]

/-- **The oracle is only seen where it is queried.** If the calls of the run of `x` against `H`
from `ρ` stay within `S` and `H'` agrees with `H` on `S`, the runs against `H` and `H'` from `ρ`
have the same branches, on every leaf. -/
theorem run_branch_additiveOracleRuntime_eq_of_eqOn (I : L.Interp) {x : QuantumComp L (qromSpec X
  Y) W A}
    {ρ : SubState A} (hS : QueriesWithin I x S H ρ) (hH : Set.EqOn H H' S) (p : Σ u, W u) :
    ((additiveOracleRuntime H').run I x).branch p (ρ.prod (SubState.basis ())).matrix =
      ((additiveOracleRuntime H).run I x).branch p (ρ.prod (SubState.basis ())).matrix :=
  (QuantumRuntime.run_branch_apply_eq_of_forallQueries (D := QReg.of Unit)
    (σ₁ := SubState.basis ()) (σ₂ := SubState.basis ()) (s₁ := (additiveOracleRuntime H).step)
    (s₂ := (additiveOracleRuntime H').step) I (fun i E _ hσ r ↦
      additiveOracleRuntime_step_frame_congr hH i E hσ r) hS
    p).symm

/-- **The oracle is only seen where it is queried.** If the calls of the run of `x` against `H`
from `ρ` stay within `S` and `H'` agrees with `H` on `S`, the runs against `H` and `H'` from `ρ`
have the same outcome distribution. -/
theorem evalDist_additiveOracleRuntime_eq_of_eqOn [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {ρ : SubState A} (hS : QueriesWithin I x S H ρ)
    (hH : Set.EqOn H H' S) : (additiveOracleRuntime H').evalDist I x ρ = (additiveOracleRuntime
      H).evalDist I x ρ :=
  (QuantumRuntime.evalDist_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (additiveOracleRuntime H).step) (s₂ := (additiveOracleRuntime H').step) I
    (fun i E _ hσ r ↦ additiveOracleRuntime_step_frame_congr hH i E hσ r) hS).symm

/-- If the calls of the run of `x` against `H` from `ρ` stay within `S` and `H'` agrees with `H`
on `S`, the runs against `H` and `H'` from `ρ` leave the same joint post-states. -/
theorem jointPost_additiveOracleRuntime_eq_of_eqOn (I : L.Interp) {x : QuantumComp L (qromSpec X
  Y) W A}
    {ρ : SubState A} (hS : QueriesWithin I x S H ρ) (hH : Set.EqOn H H' S) (p : Σ u, W u) :
    (additiveOracleRuntime H').jointPost I x ρ p = (additiveOracleRuntime H).jointPost I x ρ p :=
  (QuantumRuntime.jointPost_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (additiveOracleRuntime H).step) (s₂ := (additiveOracleRuntime H').step) I
    (fun i E _ hσ r ↦ additiveOracleRuntime_step_frame_congr hH i E hσ r) hS p).symm

/-- **The oracle is only seen where it is queried**, for the distribution of the value returned by a
fixed-register program. -/
theorem evalDist₂_additiveOracleRuntime_eq_of_eqOn [MeasurableSpace α] (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} {ρ : SubState A} (hS : QueriesWithin I x S H ρ)
    (hH : Set.EqOn H H' S) :
    (additiveOracleRuntime H').evalDist₂ I x ρ = (additiveOracleRuntime H).evalDist₂ I x ρ :=
  (QuantumRuntime.evalDist₂_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (additiveOracleRuntime H).step) (s₂ := (additiveOracleRuntime H').step) I
    (fun i E _ hσ r ↦ additiveOracleRuntime_step_frame_congr hH i E hσ r) hS).symm

/-- Staying within `S` transfers to any function that agrees on `S`. -/
theorem QueriesWithin.of_eqOn {I : L.Interp} {x : QuantumComp L (qromSpec X Y) W A}
    {ρ : SubState A} (hS : QueriesWithin I x S H ρ) (hH : Set.EqOn H H' S) :
    QueriesWithin I x S H' ρ :=
  QuantumRuntime.ForallQueries.of_congr (D := QReg.of Unit) (σ₁ := SubState.basis ())
    (σ₂ := SubState.basis ()) (s₁ := (additiveOracleRuntime H).step) (s₂ := (additiveOracleRuntime
      H').step) I
    (fun i E _ hσ r ↦ additiveOracleRuntime_step_frame_congr hH i E hσ r) hS

end qrom

end Quantum
