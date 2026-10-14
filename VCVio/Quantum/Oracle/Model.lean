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
public import VCVio.Quantum.Oracle.Unitary

/-!
# The quantum random-oracle model

An oracle is realized by a family of runtimes indexed by a sampled value.
`Quantum.sampledLaw R I x ρ` draws the value `ω` uniformly, with VCVio's `$ᵗ`, and observes the
leaf reached by the program `x`, under the interpretation `I` of its local operations, against
the runtime `R ω` from `ρ` (`Quantum.QuantumRuntime.outcomeLaw`). Another realization of the
oracle is another family of runtimes for the same signature, and "same outcome law" is an
equation between two values of `Quantum.sampledLaw`.

Events that mention the sampled value, such as "the program's guess `(x, y)` satisfies
`y = H x`", are measured by `Quantum.sampledLawWith`, which observes the leaf of each run through
a function `f ω` that sees the sampled value. The observed law is a sum of weighted point masses
(`Quantum.QuantumRuntime.outcomeLawWith`), so `f` need not be measurable.

The quantum random-oracle model is the instance for the signature `Quantum.qromSpec X Y`, with
one port acting on `X × Y`, in which the sampled value is a function `H : X → Y` and the runtime
`Quantum.xorRuntime H` answers each call with the oracle unitary of `H`
(`Quantum.qromLaw`). Programs are quantum programs over any primitive signature: adaptive,
with their own registers, and with any number of calls on each path.

Every law here is stated for general programs (`Quantum.QuantumComp`), whose final register may
depend on the outcome: such a program returns a leaf in `Σ u, W u`, and its laws are laws of that
leaf, observed if need be through a function of the leaf. For a program on a fixed final register
(`Quantum.QuantumComp₂`), the law of its returned value is the general law observed through the
value of each leaf (`Quantum.QuantumComp₂.leafEquiv`): `Quantum.sampledLaw₂`,
`Quantum.sampledLawWith₂`, `Quantum.qromLaw₂` and `Quantum.qromLawWith₂` are defined so, and are
the mixtures of the fixed-register outcome laws (`Quantum.sampledLaw₂_eq_bind`,
`Quantum.sampledLawWith₂_eq_bind`).

## Main results

* `Quantum.qromLaw_eq_sum`: the law is the average over all functions of the outcome laws of the
  runs.
* `Quantum.qromLaw_apply_univ`: against every function, a lossless run gives total mass the trace
  of the program's initial substate; `Quantum.isProbabilityMeasure_qromLaw` for a lossless
  program from a normalized state.
* `Quantum.run_xorRuntime_eq_of_isQueryBound_zero`: a program with query budget zero runs to the
  same dependent subinstrument against every function.
* `Quantum.qromLawWith_guess_zero`: with query budget zero, a guess `(gx p, gy p)` read off the
  leaf `p` satisfies `gy p = H (gx p)` with probability the total weight of the run (the trace
  functional of its branches) divided by `|Y|`; `1 / |Y|` for a lossless program from a
  normalized state (`Quantum.qromLawWith_guess_zero_of_trace_eq_one`).
* `Quantum.outcomeLaw_xorRuntime_eq_of_eqOn`: if every call along the run against `H` receives
  an operator supported on the query inputs in `S` (`Quantum.QueriesWithin`), the run against any
  `H'` that agrees with `H` on `S` has the same outcome law, and the same joint post-states.

Each has a fixed-register form with `₂` in its name (`Quantum.qromLaw₂_eq_sum`,
`Quantum.qromLawWith₂_guess_zero`, and so on).
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder

universe u v u₁ v₁ w w₁

namespace Quantum

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w} {A B : QReg}
  {α : Type w} {β : Type w₁}

/-! ## Outcome laws against a sampled runtime -/

section sampled

variable {Ω : Type} [SampleableType Ω]

/-- The law of an observation of the leaf reached by `x`, when `ω` is drawn uniformly and the
oracle is realized by the runtime `R ω`: the mixture over `ω` of the laws of the leaf of `x` under
`I` against `R ω` from `ρ`, observed through `f ω` (`Quantum.QuantumRuntime.outcomeLawWith`). The
observation sees the sampled value and the whole leaf, its final register included, and need not
be measurable. -/
@[expose]
noncomputable def sampledLawWith [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    Measure β :=
  letI : MeasurableSpace Ω := ⊤
  (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).outcomeLawWith I x ρ (f ω)

/-- The law of the leaf reached by `x` when `ω` is drawn uniformly and the oracle is realized by
the runtime `R ω`: the mixture over `ω` of the outcome laws of `x` under `I` against `R ω` from
`ρ`. -/
@[expose]
noncomputable def sampledLaw [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) : Measure (Σ u, W u) :=
  letI : MeasurableSpace Ω := ⊤
  (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).outcomeLaw I x ρ

/-- Observing the leaf itself, without looking at the sampled value, gives the law of the
leaf. -/
theorem sampledLawWith_id [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) :
    sampledLawWith R I x ρ (fun _ p ↦ p) = sampledLaw R I x ρ :=
  rfl

section fintype

variable [Fintype Ω]

/-- The observed law of a measurable set averages, over the sampled values, its measure under
the observed runs. -/
theorem sampledLawWith_apply [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) {s : Set β}
    (hs : MeasurableSet s) :
    sampledLawWith R I x ρ f s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).outcomeLawWith I x ρ (f ω) s := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledLawWith, SampleableType.evalDist_uniformSample, uniformOn_univ_bind_apply _ _ hs]

/-- The observed law is the average, over the sampled values, of the observed laws of the
runs. -/
theorem sampledLawWith_eq_sum [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    sampledLawWith R I x ρ f =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).outcomeLawWith I x ρ (f ω) := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledLawWith_apply _ _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]

/-- The law of a measurable set of leaves averages, over the sampled values, its measure under
the runs. -/
theorem sampledLaw_apply [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) {s : Set (Σ u, W u)}
    (hs : MeasurableSet s) :
    sampledLaw R I x ρ s = ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).outcomeLaw I x ρ s := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledLaw, SampleableType.evalDist_uniformSample, uniformOn_univ_bind_apply _ _ hs]

/-- The law is the average, over the sampled values, of the outcome laws of the runs. -/
theorem sampledLaw_eq_sum [MeasurableSpace (Σ u, W u)] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) :
    sampledLaw R I x ρ = (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).outcomeLaw I x ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledLaw_apply _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

end fintype

/-- When every run is lossless and every initial substate has trace `c`, the law has total mass
the trace of `ρ` times `c`. -/
theorem sampledLaw_apply_univ [MeasurableSpace (Σ u, W u)] {R : Ω → QuantumRuntime spec}
    {I : L.Interp} {x : QuantumComp L spec W A} (h : ∀ ω, ((R ω).run I x).Lossless) {c : ℝ}
    (hc : ∀ ω, (R ω).init.matrix.trace.re = c) (ρ : SubState A) :
    sampledLaw R I x ρ Set.univ = ENNReal.ofReal (ρ.matrix.trace.re * c) := by
  let : Fintype Ω := Fintype.ofFinite Ω
  rw [sampledLaw_apply _ _ _ _ MeasurableSet.univ]
  simp only [(R _).outcomeLaw_apply_univ_of_lossless I (h _), hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-! ### Programs on a fixed final register -/

/-- The law of the value returned by the fixed-register program `x`, relabelled by a function
that sees the sampled value: the general observed law, reading each leaf `p` through its value
`(leafEquiv B α).symm p`. It is the mixture over `ω` of the outcome laws of `x.map (f ω)`
(`Quantum.sampledLawWith₂_eq_bind`). -/
@[expose]
noncomputable def sampledLawWith₂ [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) :
    Measure β :=
  sampledLawWith R I x ρ fun ω p ↦ f ω ((QuantumComp₂.leafEquiv B α).symm p)

/-- The law of the value returned by the fixed-register program `x`: the general observed law,
reading each leaf through its value. It is the mixture over `ω` of the outcome laws of `x`
(`Quantum.sampledLaw₂_eq_bind`). -/
@[expose]
noncomputable def sampledLaw₂ [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) : Measure α :=
  sampledLawWith R I x ρ fun _ p ↦ (QuantumComp₂.leafEquiv B α).symm p

/-- The relabelled law of a fixed-register program is the mixture of the outcome laws of its
relabellings. -/
theorem sampledLawWith₂_eq_bind [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) :
    sampledLawWith₂ R I x ρ f =
      letI : MeasurableSpace Ω := ⊤
      (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).outcomeLaw₂ I (x.map (f ω)) ρ := by
  simp only [QuantumRuntime.outcomeLaw₂_map_eq_outcomeLawWith]
  rfl

/-- The law of the value of a fixed-register program is the mixture of its outcome laws. -/
theorem sampledLaw₂_eq_bind [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    sampledLaw₂ R I x ρ =
      letI : MeasurableSpace Ω := ⊤
      (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).outcomeLaw₂ I x ρ := by
  simp only [QuantumRuntime.outcomeLaw₂_eq_outcomeLawWith]
  rfl

/-- Relabelling the value without looking at the sampled value or changing it gives the law of
the value. -/
theorem sampledLawWith₂_id [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    sampledLawWith₂ R I x ρ (fun _ a ↦ a) = sampledLaw₂ R I x ρ :=
  rfl

section fintype

variable [Fintype Ω]

/-- The relabelled law of a measurable set averages, over the sampled values, its measure under
the relabelled runs. -/
theorem sampledLawWith₂_apply [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) {s : Set β}
    (hs : MeasurableSet s) :
    sampledLawWith₂ R I x ρ f s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).outcomeLaw₂ I (x.map (f ω)) ρ s := by
  refine (sampledLawWith_apply R I x ρ _ hs).trans ?_
  simp only [QuantumRuntime.outcomeLaw₂_map_eq_outcomeLawWith]

/-- The relabelled law is the average, over the sampled values, of the outcome laws of the
relabelled runs. -/
theorem sampledLawWith₂_eq_sum [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (f : Ω → α → β) :
    sampledLawWith₂ R I x ρ f =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).outcomeLaw₂ I (x.map (f ω)) ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledLawWith₂_apply _ _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]

/-- The law of a measurable set of values averages, over the sampled values, its measure under
the runs. -/
theorem sampledLaw₂_apply [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) {s : Set α} (hs : MeasurableSet s) :
    sampledLaw₂ R I x ρ s = ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).outcomeLaw₂ I x ρ s := by
  refine (sampledLawWith_apply R I x ρ _ hs).trans ?_
  simp only [QuantumRuntime.outcomeLaw₂_eq_outcomeLawWith]

/-- The law of the value is the average, over the sampled values, of the outcome laws of the
runs. -/
theorem sampledLaw₂_eq_sum [MeasurableSpace α] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    sampledLaw₂ R I x ρ = (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).outcomeLaw₂ I x ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledLaw₂_apply _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

end fintype

/-- When every run is lossless and every initial substate has trace `c`, the law of the value
has total mass the trace of `ρ` times `c`. -/
theorem sampledLaw₂_apply_univ [MeasurableSpace α] {R : Ω → QuantumRuntime spec} {I : L.Interp}
    {x : QuantumComp₂ L spec A B α} (h : ∀ ω, ((R ω).run₂ I x).Lossless) {c : ℝ}
    (hc : ∀ ω, (R ω).init.matrix.trace.re = c) (ρ : SubState A) :
    sampledLaw₂ R I x ρ Set.univ = ENNReal.ofReal (ρ.matrix.trace.re * c) := by
  let : Fintype Ω := Fintype.ofFinite Ω
  rw [sampledLaw₂_apply _ _ _ _ MeasurableSet.univ]
  simp only [(R _).outcomeLaw₂_apply_univ_of_lossless I (h _), hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

end sampled

/-! ## Guessing a value of a uniform function -/

section guess

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y]

/-- Each value is taken at a given input by the same number of functions: the functions with
`H x = y`, times `|Y|`, are all the functions. -/
theorem card_filter_apply_eq_mul_card [DecidableEq Y] (x : X) (y : Y) :
    (Finset.univ.filter fun H : X → Y ↦ H x = y).card * Fintype.card Y =
      Fintype.card (X → Y) := by
  have hfib : ∀ y' : Y, (Finset.univ.filter fun H : X → Y ↦ H x = y').card =
      (Finset.univ.filter fun H : X → Y ↦ H x = y).card := fun y' ↦
    Finset.card_equiv (Equiv.addRight fun _ ↦ y - y') fun H ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ (congrArg (· + (y - y')) h).trans (add_sub_cancel y' y),
        fun h ↦ add_right_cancel (h.trans (add_sub_cancel y' y).symm)⟩
  have h := Finset.card_eq_sum_card_fiberwise (f := fun H : X → Y ↦ H x) (s := Finset.univ)
    (t := Finset.univ) fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl fun b _ ↦ hfib b, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm]

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
    have hc := card_filter_apply_eq_mul_card (x i) (y i)
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
    rw [SubInstrument.outcomeMeasure_map, Measure.sum_apply _ (MeasurableSet.singleton True)]
    simp only [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton True),
      smul_eq_mul]
  simp only [hmeas]
  rw [sum_tsum_guess, SubInstrument.trace_re_total_apply,
    ENNReal.ofReal_tsum_of_nonneg (fun a ↦ P.trace_re_branch_apply_nonneg a ρ.posSemidef)
      (P.isCPTNIFamily.summable_trace_re_apply ρ.posSemidef)]

end guess

/-! ## The quantum random-oracle model -/

section qrom

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The signature of a random oracle `X → Y`: one port, whose call acts on the query register
`X × Y` and returns no classical result. It is reducible, so that its ports, registers and
results unfold to `Unit` and `X × Y` when rewriting. -/
@[expose, reducible]
def qromSpec (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    QuantumOracleSpec.{0, 0} where
  Port := Unit
  In _ := QReg.of (X × Y)
  Out _ := QReg.of (X × Y)
  Result _ := Unit

variable [AddCommGroup Y]

/-- The runtime of the oracle unitary of `H : X → Y`: a trivial private register, and each call
applies `|x, y⟩ ↦ |x, y + H x⟩` to the query register. -/
@[expose]
noncomputable def xorRuntime (H : X → Y) : QuantumRuntime (qromSpec X Y) where
  D := QReg.of Unit
  init := SubState.basis ()
  step _ := (oracleQuery H).frame Unit

/-- The step of the oracle runtime is the oracle unitary, framed by the trivial register. -/
theorem xorRuntime_step (H : X → Y) (i : Unit) :
    (xorRuntime H).step i = (oracleQuery H).frame Unit :=
  rfl

/-- The private register of the oracle runtime starts in its unique basis state. -/
theorem xorRuntime_init (H : X → Y) : (xorRuntime H).init = SubState.basis () :=
  rfl

/-- The steps of the oracle runtime are lossless. -/
theorem lossless_xorRuntime_step (H : X → Y) (i : Unit) : ((xorRuntime H).step i).Lossless :=
  (lossless_oracleQuery H).frame Unit

/-- A lossless program runs against the oracle runtime to a lossless dependent subinstrument. -/
theorem lossless_run_xorRuntime (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    (hx : x.Lossless I) (H : X → Y) : ((xorRuntime H).run I x).Lossless :=
  (xorRuntime H).lossless_run I hx (lossless_xorRuntime_step H)

/-- A lossless fixed-register program runs against the oracle runtime to a lossless
subinstrument. -/
theorem lossless_run₂_xorRuntime (I : L.Interp) {x : QuantumComp₂ L (qromSpec X Y) A B α}
    (hx : x.Lossless I) (H : X → Y) : ((xorRuntime H).run₂ I x).Lossless :=
  (xorRuntime H).lossless_run₂ I hx (lossless_xorRuntime_step H)

/-- The initial substate of the oracle runtime has trace one. -/
theorem trace_re_xorRuntime_init (H : X → Y) : (xorRuntime H).init.matrix.trace.re = 1 :=
  (congrArg Complex.re (SubState.trace_basis (A := Unit) ())).trans Complex.one_re

section sampled

variable [SampleableType (X → Y)]

/-- The law of an observation of the leaf reached by `x` from `ρ` in the quantum random-oracle
model: `H : X → Y` is drawn uniformly, the program runs under `I` against the oracle unitary of
`H`, and its leaf `p` is reported as `f H p`. -/
@[expose]
noncomputable def qromLawWith [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (X → Y) → (Σ u, W u) → β) :
    Measure β :=
  sampledLawWith xorRuntime I x ρ f

/-- The law of the leaf reached by `x` from `ρ` in the quantum random-oracle model: `H : X → Y`
is drawn uniformly and the program runs under `I` against the oracle unitary of `H`. -/
@[expose]
noncomputable def qromLaw [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) : Measure (Σ u, W u) :=
  sampledLaw xorRuntime I x ρ

/-- Observing the leaf itself, without looking at the random function, gives the law of the
quantum random-oracle model. -/
theorem qromLawWith_id [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) :
    qromLawWith I x ρ (fun _ p ↦ p) = qromLaw I x ρ :=
  sampledLawWith_id _ I x ρ

/-- The law of the quantum random-oracle model is the average, over all `|Y| ^ |X|` functions,
of the outcome laws of the runs against their oracle unitaries. -/
theorem qromLaw_eq_sum [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) :
    qromLaw I x ρ =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (xorRuntime H).outcomeLaw I x ρ := by
  rw [qromLaw, sampledLaw_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- The observed law of the quantum random-oracle model is the average, over all `|Y| ^ |X|`
functions, of the observed laws of the runs. -/
theorem qromLawWith_eq_sum [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (X → Y) → (Σ u, W u) → β) :
    qromLawWith I x ρ f =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (xorRuntime H).outcomeLawWith I x ρ (f H) := by
  rw [qromLawWith, sampledLawWith_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- When the run against every function is lossless, the law of the quantum random-oracle model
has total mass the trace of the initial substate. -/
theorem qromLaw_apply_univ [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (qromSpec X Y) W A} (h : ∀ H, ((xorRuntime H).run I x).Lossless)
    (ρ : SubState A) : qromLaw I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [qromLaw, sampledLaw_apply_univ h trace_re_xorRuntime_init, mul_one]

/-- The law of a lossless program has total mass the trace of the initial substate. -/
theorem qromLaw_apply_univ_of_lossless [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.Lossless I) (ρ : SubState A) :
    qromLaw I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re :=
  qromLaw_apply_univ (lossless_run_xorRuntime I hx) ρ

/-- When the run against every function is lossless and the initial state is normalized, the
law of the quantum random-oracle model is a probability measure. -/
theorem isProbabilityMeasure_qromLaw [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (qromSpec X Y) W A} (h : ∀ H, ((xorRuntime H).run I x).Lossless)
    {ρ : SubState A} (hρ : ρ.matrix.trace = 1) : IsProbabilityMeasure (qromLaw I x ρ) :=
  ⟨by rw [qromLaw_apply_univ h, hρ, Complex.one_re, ENNReal.ofReal_one]⟩

/-! #### Programs on a fixed final register -/

/-- The law of the value returned by the fixed-register program `x` in the quantum random-oracle
model, relabelled by a function that sees the random function: the general observed law, reading
each leaf through its value (`Quantum.qromLawWith₂_eq_qromLawWith`). -/
@[expose]
noncomputable def qromLawWith₂ [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) (f : (X → Y) → α → β) :
    Measure β :=
  sampledLawWith₂ xorRuntime I x ρ f

/-- The law of the value returned by the fixed-register program `x` in the quantum random-oracle
model: the general observed law, reading each leaf through its value
(`Quantum.qromLaw₂_eq_qromLawWith`). -/
@[expose]
noncomputable def qromLaw₂ [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) : Measure α :=
  sampledLaw₂ xorRuntime I x ρ

/-- The relabelled law of a fixed-register program is the general observed law, reading each
leaf through its value. -/
theorem qromLawWith₂_eq_qromLawWith [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) (f : (X → Y) → α → β) :
    qromLawWith₂ I x ρ f =
      qromLawWith I x ρ fun H p ↦ f H ((QuantumComp₂.leafEquiv B α).symm p) :=
  rfl

/-- The law of the value of a fixed-register program is the general observed law, reading each
leaf through its value. -/
theorem qromLaw₂_eq_qromLawWith [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    qromLaw₂ I x ρ = qromLawWith I x ρ fun _ p ↦ (QuantumComp₂.leafEquiv B α).symm p :=
  rfl

/-- Relabelling the value without looking at the random function or changing it gives the law of
the value. -/
theorem qromLawWith₂_id [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    qromLawWith₂ I x ρ (fun _ a ↦ a) = qromLaw₂ I x ρ :=
  rfl

/-- The law of the value is the average, over all `|Y| ^ |X|` functions, of the outcome laws of
the runs against their oracle unitaries. -/
theorem qromLaw₂_eq_sum [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    qromLaw₂ I x ρ =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (xorRuntime H).outcomeLaw₂ I x ρ := by
  rw [qromLaw₂, sampledLaw₂_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- The relabelled law of the value is the average, over all `|Y| ^ |X|` functions, of the
outcome laws of the relabelled runs. -/
theorem qromLawWith₂_eq_sum [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) (f : (X → Y) → α → β) :
    qromLawWith₂ I x ρ f =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (xorRuntime H).outcomeLaw₂ I (x.map (f H)) ρ := by
  rw [qromLawWith₂, sampledLawWith₂_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- When the run against every function is lossless, the law of the value has total mass the
trace of the initial substate. -/
theorem qromLaw₂_apply_univ [MeasurableSpace α] {I : L.Interp}
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (h : ∀ H, ((xorRuntime H).run₂ I x).Lossless)
    (ρ : SubState A) : qromLaw₂ I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [qromLaw₂, sampledLaw₂_apply_univ h trace_re_xorRuntime_init, mul_one]

/-- The law of the value of a lossless fixed-register program has total mass the trace of the
initial substate. -/
theorem qromLaw₂_apply_univ_of_lossless [MeasurableSpace α] {I : L.Interp}
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.Lossless I) (ρ : SubState A) :
    qromLaw₂ I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re :=
  qromLaw₂_apply_univ (lossless_run₂_xorRuntime I hx) ρ

/-- When the run against every function is lossless and the initial state is normalized, the
law of the value is a probability measure. -/
theorem isProbabilityMeasure_qromLaw₂ [MeasurableSpace α] {I : L.Interp}
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (h : ∀ H, ((xorRuntime H).run₂ I x).Lossless)
    {ρ : SubState A} (hρ : ρ.matrix.trace = 1) : IsProbabilityMeasure (qromLaw₂ I x ρ) :=
  ⟨by rw [qromLaw₂_apply_univ h, hρ, Complex.one_re, ENNReal.ofReal_one]⟩

end sampled

/-! ### No queries -/

/-- **No queries, no dependence on the oracle.** A program with query budget zero runs to the
same dependent subinstrument against every function. -/
theorem run_xorRuntime_eq_of_isQueryBound_zero (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    (hx : x.IsQueryBound 0) (H H' : X → Y) :
    (xorRuntime H).run I x = (xorRuntime H').run I x :=
  QuantumRuntime.run_congr_of_isQueryBound I hx fun _ h ↦ absurd rfl h

/-- **No queries, no dependence on the oracle**, for fixed-register programs: the runs against
every function are the same subinstrument. -/
theorem run₂_xorRuntime_eq_of_isQueryBound_zero (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.IsQueryBound 0) (H H' : X → Y) :
    (xorRuntime H).run₂ I x = (xorRuntime H').run₂ I x :=
  QuantumRuntime.run₂_congr_of_isQueryBound I hx fun _ h ↦ absurd rfl h

/-- **No queries, no knowledge of the oracle.** In the quantum random-oracle model, a program with
query budget zero whose leaf `p` carries a guess, an input `gx p` with a value `gy p`, satisfies
`gy p = H (gx p)` with probability the total weight of its run divided by `|Y|`: the trace
functional of the branches of the run from `ρ ⊗ |()⟩⟨()|`. The run does not depend on the
function (`run_xorRuntime_eq_of_isQueryBound_zero`); it is taken against `H₀`. The final register
of the leaf may depend on the outcome, and the guess may read it. -/
theorem qromLawWith_guess_zero [SampleableType (X → Y)] (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.IsQueryBound 0) (ρ : SubState A)
    (gx : (Σ u, W u) → X) (gy : (Σ u, W u) → Y) (H₀ : X → Y) :
    qromLawWith I x ρ (fun H p ↦ gy p = H (gx p)) {True} =
      ENNReal.ofReal
          (MatrixMap.familyTrace ((xorRuntime H₀).run I x).branch
            (ρ.prod (SubState.basis ())).matrix).re /
        Fintype.card Y := by
  have hw : ∀ (H : X → Y) (p : Σ u, W u),
      (xorRuntime H).jointPost I x ρ p = (xorRuntime H₀).jointPost I x ρ p := fun H p ↦ by
    unfold QuantumRuntime.jointPost
    rw [run_xorRuntime_eq_of_isQueryBound_zero I hx H H₀]
    rfl
  rw [qromLawWith, sampledLawWith_apply _ _ _ _ _ (MeasurableSet.singleton True)]
  simp only [QuantumRuntime.outcomeLawWith_apply _ _ _ _ _ (MeasurableSet.singleton True)]
  refine (Finset.sum_congr rfl fun H _ ↦ congrArg _ (tsum_congr fun p ↦ by rw [hw H p]; rfl)).trans
    ((sum_tsum_guess (fun p ↦ ENNReal.ofReal ((xorRuntime H₀).jointPost I x ρ p).matrix.trace.re)
      gx gy).trans ?_)
  exact congrArg (· / (Fintype.card Y : ℝ≥0∞)) ((xorRuntime H₀).tsum_jointPost_trace I x ρ)

/-- A lossless program with query budget zero guesses a value of the random function with
probability the trace of its initial substate divided by `|Y|`. -/
theorem qromLawWith_guess_zero_of_lossless [SampleableType (X → Y)] (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (ρ : SubState A) (gx : (Σ u, W u) → X) (gy : (Σ u, W u) → Y) :
    qromLawWith I x ρ (fun H p ↦ gy p = H (gx p)) {True} =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card Y := by
  have h : (ρ.prod (SubState.basis ())).matrix.trace.re = ρ.matrix.trace.re := by
    rw [SubState.trace_re_prod, SubState.trace_basis, Complex.one_re, mul_one]
  rw [qromLawWith_guess_zero I hx ρ gx gy 0,
    lossless_run_xorRuntime I hl 0 (ρ.prod (SubState.basis ())).matrix]
  exact congrArg (fun r ↦ ENNReal.ofReal r / (Fintype.card Y : ℝ≥0∞)) h

/-- In the quantum random-oracle model, a lossless program with query budget zero that starts
from a normalized state and whose leaf `p` carries a guess `(gx p, gy p)` satisfies
`gy p = H (gx p)` with probability `1 / |Y|`. -/
theorem qromLawWith_guess_zero_of_trace_eq_one [SampleableType (X → Y)] (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (gx : (Σ u, W u) → X) (gy : (Σ u, W u) → Y) {ρ : SubState A} (hρ : ρ.matrix.trace = 1) :
    qromLawWith I x ρ (fun H p ↦ gy p = H (gx p)) {True} = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  rw [qromLawWith_guess_zero_of_lossless I hx hl ρ gx gy, hρ]
  simp

/-- **No queries, no knowledge of the oracle**, for the value returned by a fixed-register
program: a guess `(gx a, gy a)` satisfies `gy a = H (gx a)` with probability the total weight of
the run divided by `|Y|`. -/
theorem qromLawWith₂_guess_zero [SampleableType (X → Y)] (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.IsQueryBound 0) (ρ : SubState A)
    (gx : α → X) (gy : α → Y) (H₀ : X → Y) :
    qromLawWith₂ I x ρ (fun H a ↦ gy a = H (gx a)) {True} =
      ENNReal.ofReal
          (((xorRuntime H₀).run₂ I x).total (ρ.prod (SubState.basis ())).matrix).trace.re /
        Fintype.card Y := by
  have hrun : ∀ H : X → Y, (xorRuntime H).outcomeLaw₂ I (x.map fun a ↦ gy a = H (gx a)) ρ =
      (((xorRuntime H₀).run₂ I x).map fun a ↦ gy a = H (gx a)).outcomeMeasure
        (ρ.prod (SubState.basis ())) := fun H ↦ by
    rw [QuantumRuntime.outcomeLaw₂, QuantumRuntime.run₂_map,
      run₂_xorRuntime_eq_of_isQueryBound_zero I hx H H₀]
    rfl
  rw [qromLawWith₂, sampledLawWith₂_apply _ _ _ _ _ (MeasurableSet.singleton True)]
  simp only [hrun]
  exact sum_outcomeMeasure_map_guess _ _ gx gy

/-- A lossless fixed-register program with query budget zero guesses a value of the random
function with probability the trace of its initial substate divided by `|Y|`. -/
theorem qromLawWith₂_guess_zero_of_lossless [SampleableType (X → Y)] (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (ρ : SubState A) (gx : α → X) (gy : α → Y) :
    qromLawWith₂ I x ρ (fun H a ↦ gy a = H (gx a)) {True} =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card Y := by
  have h : (((xorRuntime 0).run₂ I x).total (ρ.prod (SubState.basis ())).matrix).trace =
      (ρ.prod (SubState.basis ())).matrix.trace :=
    lossless_run₂_xorRuntime I hl 0 (ρ.prod (SubState.basis ())).matrix
  rw [qromLawWith₂_guess_zero I hx ρ gx gy 0, h, SubState.trace_re_prod, SubState.trace_basis,
    Complex.one_re, mul_one]

/-- A lossless fixed-register program with query budget zero that starts from a normalized state
and returns a guess `(x, y)` satisfies `y = H x` with probability `1 / |Y|`. -/
theorem qromLawWith₂_guess_zero_of_trace_eq_one [SampleableType (X → Y)] (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B (X × Y)} (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    {ρ : SubState A} (hρ : ρ.matrix.trace = 1) :
    qromLawWith₂ I x ρ (fun H a ↦ a.2 = H a.1) {True} = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  rw [qromLawWith₂_guess_zero_of_lossless I hx hl ρ Prod.fst Prod.snd, hρ]
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
  (xorRuntime H).ForallQueries I
    (fun _ E σ ↦ QuerySupportedOn (fun m : ((X × Y) × Unit) × E ↦ m.1.1.1) S σ) x
    (ρ.prod (SubState.basis ())).matrix

variable {S : Set X} {H H' : X → Y}

/-- On an operator supported on the query inputs in `S`, a call of the oracle runtime of `H`,
framed by any remainder, only depends on the restriction of `H` to `S`. -/
theorem xorRuntime_step_frame_congr (hH : Set.EqOn H H' S) (i : (qromSpec X Y).Port) (E : QReg)
    {σ : Matrix (((X × Y) × Unit) × E) (((X × Y) × Unit) × E) ℂ}
    (hσ : QuerySupportedOn (fun m : ((X × Y) × Unit) × E ↦ m.1.1.1) S σ) (r : Unit) :
    (((xorRuntime H).step i).frame E).branch r σ =
      (((xorRuntime H').step i).frame E).branch r σ := by
  change (((oracleQuery H).frame Unit).frame E).branch r σ =
    (((oracleQuery H').frame Unit).frame E).branch r σ
  rw [SubInstrument.branch_frame_apply, SubInstrument.branch_frame_apply,
    SubInstrument.branch_frame_apply, SubInstrument.branch_frame_apply, branch_oracleQuery_apply,
    branch_oracleQuery_apply]
  ext m m'
  rw [MatrixMap.amplify_apply _ σ m m', MatrixMap.amplify_apply _ σ m m',
    amplify_conj_oracleUnitary_congr hH
      (QuerySupportedOn.block (q := fun n : (X × Y) × Unit ↦ n.1.1) hσ m.2 m'.2)]

/-- **The oracle is only seen where it is queried.** If the calls of the run of `x` against `H`
from `ρ` stay within `S` and `H'` agrees with `H` on `S`, the runs against `H` and `H'` from `ρ`
have the same branches, on every leaf. -/
theorem run_branch_xorRuntime_eq_of_eqOn (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    {ρ : SubState A} (hS : QueriesWithin I x S H ρ) (hH : Set.EqOn H H' S) (p : Σ u, W u) :
    ((xorRuntime H').run I x).branch p (ρ.prod (SubState.basis ())).matrix =
      ((xorRuntime H).run I x).branch p (ρ.prod (SubState.basis ())).matrix :=
  (QuantumRuntime.run_branch_apply_eq_of_forallQueries (D := QReg.of Unit)
    (σ₁ := SubState.basis ()) (σ₂ := SubState.basis ()) (s₁ := (xorRuntime H).step)
    (s₂ := (xorRuntime H').step) I (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS
    p).symm

/-- **The oracle is only seen where it is queried.** If the calls of the run of `x` against `H`
from `ρ` stay within `S` and `H'` agrees with `H` on `S`, the runs against `H` and `H'` from `ρ`
have the same outcome law. -/
theorem outcomeLaw_xorRuntime_eq_of_eqOn [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {ρ : SubState A} (hS : QueriesWithin I x S H ρ)
    (hH : Set.EqOn H H' S) : (xorRuntime H').outcomeLaw I x ρ = (xorRuntime H).outcomeLaw I x ρ :=
  (QuantumRuntime.outcomeLaw_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (xorRuntime H).step) (s₂ := (xorRuntime H').step) I
    (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS).symm

/-- If the calls of the run of `x` against `H` from `ρ` stay within `S` and `H'` agrees with `H`
on `S`, the runs against `H` and `H'` from `ρ` leave the same joint post-states. -/
theorem jointPost_xorRuntime_eq_of_eqOn (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    {ρ : SubState A} (hS : QueriesWithin I x S H ρ) (hH : Set.EqOn H H' S) (p : Σ u, W u) :
    (xorRuntime H').jointPost I x ρ p = (xorRuntime H).jointPost I x ρ p :=
  (QuantumRuntime.jointPost_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (xorRuntime H).step) (s₂ := (xorRuntime H').step) I
    (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS p).symm

/-- **The oracle is only seen where it is queried**, for the law of the value returned by a
fixed-register program. -/
theorem outcomeLaw₂_xorRuntime_eq_of_eqOn [MeasurableSpace α] (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} {ρ : SubState A} (hS : QueriesWithin I x S H ρ)
    (hH : Set.EqOn H H' S) :
    (xorRuntime H').outcomeLaw₂ I x ρ = (xorRuntime H).outcomeLaw₂ I x ρ :=
  (QuantumRuntime.outcomeLaw₂_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (xorRuntime H).step) (s₂ := (xorRuntime H').step) I
    (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS).symm

/-- Staying within `S` transfers to any function that agrees on `S`. -/
theorem QueriesWithin.of_eqOn {I : L.Interp} {x : QuantumComp L (qromSpec X Y) W A}
    {ρ : SubState A} (hS : QueriesWithin I x S H ρ) (hH : Set.EqOn H H' S) :
    QueriesWithin I x S H' ρ :=
  QuantumRuntime.ForallQueries.of_congr (D := QReg.of Unit) (σ₁ := SubState.basis ())
    (σ₂ := SubState.basis ()) (s₁ := (xorRuntime H).step) (s₂ := (xorRuntime H').step) I
    (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS

end qrom

end Quantum
