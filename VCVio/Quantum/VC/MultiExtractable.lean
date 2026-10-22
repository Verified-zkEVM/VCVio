/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import VCVio.Quantum.VC.Emulated
public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.Quantum.Oracle.Model

/-!
# Post-quantum multi-extractable vector commitments

Def 7.3 of Chiesa, Di, Hu and Zheng (ePrint 2025/2166, §7, pp. 50–51): a family
`(VC_i)_{i ∈ [k]}` of vector commitments is multi-extractable when there are an emulated oracle
`EO` and an admissible multi-extractor (Def 7.1, `Quantum.MultiExtractor.Admissible`) with five
properties:

* **P1, simulation indistinguishability** (p. 50, `Quantum.Simulates`);
* **P2, oracle commutativity** (p. 50, `Quantum.OraclesCommute`, `Quantum.ComBound`);
* **P3, multi-extraction correctness** (p. 51, `Quantum.ExtractionCorrect`);
* **P4, offline extractability** (p. 51, `Quantum.OfflineExtractable`);
* **P5, online indistinguishability** (p. 51, `Quantum.OnlineIndistinguishable`).

## Conventions

* **Adversaries** are general programs `x : QuantumComp LocalSig.instruments spec W A` from a
  general initial substate `ρ`. P1, P2 and P5 include classical read ports beside the coherent
  ordinary port (`Quantum.EmulatedOracle.coherent`, p. 28).
  The paper's start state `|0^ℓ⟩` (p. 50) is
  the case of a pure `ρ`. Adversaries with classically named ports translate to the coherent view
  through `Quantum.QuantumComp.toCoherent`; P3 and P4 have corollaries for them.
* **Universes.** The outcomes of the adversary's local operations (`LocalSig.instruments.{v}`)
  and its leaves (`W : QReg → Type w`) may lie in any universes: every property is universe
  polymorphic, with the universe parameters `v` and `w` first (`Quantum.Simulates.{v, w}`,
  `Quantum.ExtractionCorrect.{v, w}`, …), and the bundle `Quantum.IsMultiExtractable.{v, w}` uses
  one pair for all five properties. The challengers' local operations have outcomes in `Type`;
  the experiment lifts them to the adversary's universe (`Quantum.QuantumComp.liftInstruments`),
  which changes no run (`Quantum.run_experiment`). What remains fixed to `Type`: the carriers of
  registers (`Quantum.QReg`), hence the oracle's `X` and `Y` and the extraction register `Z`; the
  vector-commitment fields `Cm`, `Td`, `Pf`, which `VectorCommitment` keeps in `Type`; and, as a
  choice of this file, the messages `Msg` (which `VectorCommitment` allows in any universe). The
  uniform form of P1 (`Quantum.uniformWeights`, `Quantum.simulates_uniformWeights_iff`) needs
  `Ω : Type`, and `Quantum.EmulatedOracle.branch_run₂_callBasis` has its result in `Type` (its
  present proof goes through a lemma stated for `Unit`). No bridge between the instances of a
  property at different universes is proved, so a property at `v, w` is not known to imply it at
  other universes.
* **"t-query"** (p. 50) is `x.IsTotalQueryBound t` in P1, P2 and P5: every call counts,
  including reads, extraction and recording. P3 and P4 retain their single coherent port budget.
* **Masses** in P3 and P4 are ordinary adversary masses, excluding the challenger. In P5 the
  trusted wrapper is inside the quantified program: `wVC` includes ordinary oracle mass and
  full read-input trace in the unsplit source world. Reads contribute zero to `wME` and `wRec`.
* **Challengers** run on the adversary's final register, after it, as one program
  (`Quantum.experiment`). `Open` uses uniform coins through `OracleComp.toQuantumAt`.
  `Check` uses `runClassicalChecked`: uniform coins and projective reads at classical addresses.
  A missing answer returns rejection without losing mass. The adversary keeps its ordinary
  oracle/extraction syntax and is lifted into the mixed runtime before the challenger.
  Extraction is a classical call of the
  extraction port on `|tic, 0⟩` followed by decoding (`Quantum.extractQuery`); its branches are
  the projectors onto the fibres of `MultiExtract(tic, ·)` (`Quantum.run₂_extractQuery_branch`).

## Departures from the paper

* P1 bounds both differences, where the paper writes one (p. 50). The paper's distribution
  `D(λ)` (p. 50) is a finitely supported distribution with real weights (Mathlib's
  `Convexity.StdSimplex ℝ Ω`) over a family of runtimes on the mixed signature
  (`Quantum.mixedLawWith`). The random-oracle model is the uniform distribution
  (`Quantum.uniformWeights`) over the family of `Quantum.romVCOracle`, for which P1 reads as a
  bound against `Quantum.sampledEvalDistMap` (`Quantum.simulates_uniformWeights_iff`).
* P2's distance `‖Ψ − Ψ′‖²` (p. 50) is `Quantum.comError`, the trace of the defect
  `C = U_ME O_i − O_i U_ME` against the joint post-state of the oracle register and the adversary's
  output, summed over outcomes. On a unitary adversary from a pure state it is `‖C V |ψ⟩|ϕ⟩‖²`
  (`Quantum.comError_of_pure`).
* P5 is stated as the two inequalities `√p₁ ≤ √p₂ + √κ` and `√p₂ ≤ √p₁ + √κ`, which together say
  `(√p₁ − √p₂)² ≤ κ` (p. 51).
* Extraction returns `none` when the read value is no encoding of a tuple of the right length;
  this branch has weight zero, and the challengers report `false` on it.
* The security parameter `λ` and running-time conditions are not modelled; error functions take
  the query bound and the masses. Monotonicity of the errors (p. 51) is the separate hypothesis
  `Quantum.MEErrors.Monotone`.

## Main definitions

* `Quantum.mixedLawWith`, `Quantum.uniformWeights`.
* `Quantum.experiment`, `Quantum.oracleCall`, `Quantum.checkAt`, `Quantum.openAt`,
  `Quantum.extractQuery`, `Quantum.extractChallenger`, `Quantum.offlineChallenger`.
* `Quantum.Simulates`, `Quantum.OraclesCommute`, `Quantum.comDefect`, `Quantum.comError`,
  `Quantum.ComBound`, `Quantum.ExtractionCorrect`, `Quantum.OfflineExtractable`,
  `Quantum.OnlineIndistinguishable`.
* `Quantum.MEErrors`, `Quantum.IsMultiExtractableWith`, `Quantum.IsMultiExtractable`.

## Main results

* `Quantum.mixedLawWith_uniformWeights`: the uniform mixture of runtimes is uniform sampling.
* `Quantum.run_experiment`: an experiment runs the adversary, then the unlifted challenger.
* `Quantum.run₂_extractQuery_branch`: extraction is the measurement `{Π_tdm}` of
  `MultiExtract(tic, ·)` on the private register (the reading of game G0 of Lemma 9.3, p. 59).
* `Quantum.comError_of_pure`: the pure form of P2's distance.
* `Quantum.IsMultiExtractableWith.mono` and the monotonicity of each property.
* `Quantum.Simulates.restrictOrdinary`, `Quantum.ExtractionCorrect.of_classicalPorts`,
  `Quantum.OfflineExtractable.of_classicalPorts`.
-/

public section

open Matrix MeasureTheory OracleSpec Convexity
open scoped ENNReal Kronecker ComplexOrder

universe u v w u₁ v₁

namespace Quantum

open EmulatedOracle (cohSpec)

/-! ## Experiments -/

section experiment

variable {spec : QuantumOracleSpec.{u₁, v₁}} {A : QReg} {W : QReg → Type w}

/-- **Adversary, then challenger, as one program.** Run the adversary `x`; on its leaf `y` with
final register `u`, run the challenger `chal u y` on `u` and report its bit. The adversary's local
operations and leaves may lie in any universes; the challenger's local operations have outcomes in
`Type`, and are lifted to the adversary's (`Quantum.QuantumComp.liftInstruments`), which changes
no run (`Quantum.run_experiment`). -/
@[expose]
noncomputable def experiment (x : QuantumComp LocalSig.instruments.{v} spec W A)
    (chal : ∀ u, W u → QComp.{u₁, v₁, 0} spec u u Bool) :
    QuantumComp LocalSig.instruments.{v} spec (fun _ ↦ Bool) A :=
  x.bind fun u y ↦ ((chal u y).forgetReg.liftInstruments :
    QuantumComp LocalSig.instruments.{max 0 v} spec (fun _ ↦ Bool) u)

/-- **The run of an experiment**: the run of the adversary, then on each leaf the run of the
challenger on its final register. The lift of the challenger's outcomes is invisible. -/
theorem run_experiment (R : QuantumRuntime spec) (x : QuantumComp LocalSig.instruments.{v} spec W A)
    (chal : ∀ u, W u → QComp.{u₁, v₁, 0} spec u u Bool) :
    R.run .instruments (experiment x chal) =
      (R.run .instruments x).bind fun p ↦ R.run .instruments (chal p.1 p.2).forgetReg := by
  rw [experiment, QuantumRuntime.run_bind]
  simp only [QuantumComp.run_liftInstruments]

/-- **Forgetting the register, on any input.** Observing a set `s` of values on the run of a
fixed-register program with its register forgotten, from any joint substate, is observing `s` on
its fixed-register run. -/
theorem QuantumRuntime.outcomeMeasure_run_forgetReg {L : LocalSig.{u, v}}
    {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) (I : L.Interp) {A B : QReg}
    {α : Type w} [MeasurableSpace α] [MeasurableSpace (Σ _ : QReg, α)]
    (x : QuantumComp₂ L spec A B α) (σ : SubState (A × R.D)) {s : Set α} (hs : MeasurableSet s)
    (hs' : MeasurableSet (Sigma.snd ⁻¹' s : Set (Σ _ : QReg, α))) :
    (R.run I x.forgetReg).outcomeMeasure σ (Sigma.snd ⁻¹' s) = (R.run₂ I x).outcomeMeasure σ s := by
  let _ : MeasurableSpace (Σ u, QuantumComp₂.Leaf B α u) := ⊤
  rw [QuantumRuntime.run_forgetReg, DSubInstrument.map_eq_bind_ret,
    DSubInstrument.outcomeMeasure_bind, Measure.sum_apply _ hs',
    DSubInstrument.outcomeMeasure_apply _ _ hs]
  simp only [DSubInstrument.outcomeMeasure_ret, Measure.smul_apply, Measure.dirac_apply' _ hs',
    smul_eq_mul, DSubInstrument.matrix_post]
  refine ((QuantumComp₂.leafEquiv B α).tsum_eq _).symm.trans (tsum_congr fun a ↦ ?_)
  rfl

/-- A challenger experiment is the sum over the actual dependent post-adversary substates. -/
theorem evalDistMap_experiment_true_eq_tsum {spec : QuantumOracleSpec.{u₁, v₁}} {A : QReg}
    {W : QReg → Type w} (R : QuantumRuntime spec)
    (x : QuantumComp LocalSig.instruments.{v} spec W A)
    (chal : ∀ u, W u → QComp.{u₁, v₁, 0} spec u u Bool) (ρ : SubState A) :
    R.evalDistMap .instruments (experiment x chal) ρ Sigma.snd {true} =
      ∑' p : Σ u, W u, (R.run₂ .instruments (chal p.1 p.2)).outcomeMeasure
        (R.jointPost .instruments x ρ p) {true} := by
  let _ : MeasurableSpace (Σ _ : QReg, Bool) := ⊤
  let _ : MeasurableSpace (Σ u, W u) := ⊤
  have hS : MeasurableSet (Sigma.snd ⁻¹' {true} : Set (Σ _ : QReg, Bool)) :=
    MeasurableSpace.measurableSet_top
  have h₁ : R.evalDistMap .instruments (experiment x chal) ρ Sigma.snd {true} =
      (R.run .instruments (experiment x chal)).outcomeMeasure (ρ.prod R.init)
        (Sigma.snd ⁻¹' {true}) := by
    rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true),
      DSubInstrument.outcomeMeasure_apply _ _ hS]
    rfl
  rw [h₁, run_experiment, DSubInstrument.outcomeMeasure_bind, Measure.sum_apply _ hS]
  simp only [QuantumRuntime.outcomeMeasure_run_forgetReg R _ _ _ (measurableSet_singleton true)
    hS]
  rfl

end experiment

namespace QuantumRuntime
variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec} (R : QuantumRuntime spec)
  (I : L.Interp) {A B C : QReg} {α β : Type*}

/-- Recording both outcomes identifies a composite instrument branch with the composition
of its two branches. The input, intermediate, and output registers may differ. -/
theorem run₂_bind_record (f : QuantumComp₂ L spec A B α)
    (g : α → QuantumComp₂ L spec B C β) (a : α) (b : β) :
    (R.run₂ I (f.bind fun a ↦ (g a).map (fun b ↦ (a, b)))).branch (a, b) =
      (R.run₂ I (g a)).branch b ∘ₗ (R.run₂ I f).branch a := by
  classical
  ext ρ : 1
  rw [run₂_bind, DSubInstrument.branch_bind_apply]
  simp only [run₂_map, SubInstrument.map_eq_bind_pure, DSubInstrument.branch_bind_apply]
  rw [tsum_eq_single a]
  · rw [tsum_eq_single b]
    · simp
    · intro b' hb
      rw [SubInstrument.branch_pure_of_ne (by simp [Ne.symm hb]), LinearMap.zero_apply]
  · intro a' ha
    have hz : ∀ b' : β,
        (SubInstrument.pure (a', b') :
          SubInstrument (C × R.D) (C × R.D) (α × β)).branch (a, b) = 0 :=
      fun _ ↦ SubInstrument.branch_pure_of_ne (by simp [Ne.symm ha])
    simp only [hz, LinearMap.zero_apply, tsum_zero]

/-- Forgetting the first recorded outcome recovers ordinary sequencing. -/
theorem bind_record_map_snd (f : QuantumComp₂ L spec A B α)
    (g : α → QuantumComp₂ L spec B C β) :
    (f.bind fun a ↦ (g a).map (fun b ↦ (a, b))).map Prod.snd = f.bind g := by
  simp only [QuantumComp₂.map, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind,
    QuantumComp₂.bind_pure]

end QuantumRuntime

/-! ## P1: simulation indistinguishability -/

section mixture

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w}
  {A : QReg} {Ω : Type*} {β : Type*} [MeasurableSpace β]

/-- **The law against a finite mixture of runtimes.** For a finitely supported distribution `p`
on `Ω` (Mathlib's `Convexity.StdSimplex ℝ Ω`: real weights `p.weights ω ≥ 0` with finite support
summing to `1`) and a family of runtimes `R`, the law of an observation of the leaf reached by
`x` when the oracle is realized by `R ω` with probability `p.weights ω`: the mixture
`∑ ω, p.weights ω • (R ω).evalDistMap I x ρ (f ω)`. The observation sees the sampled value. -/
@[expose]
noncomputable def mixedLawWith (p : StdSimplex ℝ Ω) (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    Measure β :=
  p.weights.sum fun ω r ↦ ENNReal.ofReal r • (R ω).evalDistMap I x ρ (f ω)

/-- The mixed law of a set is the weighted sum of its measures under the runs. -/
theorem mixedLawWith_apply (p : StdSimplex ℝ Ω) (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) (s : Set β) :
    mixedLawWith p R I x ρ f s =
      p.weights.sum fun ω r ↦ ENNReal.ofReal r * (R ω).evalDistMap I x ρ (f ω) s := by
  simp only [mixedLawWith, Finsupp.sum, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]

/-- The uniform distribution on a sampleable type, as a finitely supported distribution: the
barycenter of the standard simplex. -/
@[expose]
noncomputable def uniformWeights (Ω : Type) [SampleableType Ω] : StdSimplex ℝ Ω :=
  letI := Fintype.ofFinite Ω
  StdSimplex.barycenter

/-- Every weight of the uniform distribution is `1 / |Ω|`. -/
theorem uniformWeights_weights_apply (Ω : Type) [SampleableType Ω] (ω : Ω) :
    (uniformWeights Ω).weights ω = (Nat.card Ω : ℝ)⁻¹ := by
  let := Fintype.ofFinite Ω
  rw [uniformWeights, StdSimplex.weights_barycenter_apply, Nat.card_eq_fintype_card]

/-- **The uniform mixture is uniform sampling.** Against the uniform distribution, the mixed law
is `Quantum.sampledEvalDistMap`, the law of `R ω` for `ω` drawn with VCVio's `$ᵗ`. -/
theorem mixedLawWith_uniformWeights {Ω : Type} [SampleableType Ω] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    mixedLawWith (uniformWeights Ω) R I x ρ f = sampledEvalDistMap R I x ρ f := by
  let := Fintype.ofFinite Ω
  rw [sampledEvalDistMap_eq_sum, mixedLawWith, Finsupp.sum_fintype _ _ fun _ ↦ by simp,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [uniformWeights_weights_apply, Nat.card_eq_fintype_card,
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_natCast]

end mixture

section simulation

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **P1, simulation indistinguishability** (ePrint 2025/2166, Def 7.3, p. 50): against
every `t`-query adversary and every observation, the probability of observing `true` against the
mixed emulated oracle and against the reference model differ by at most `κsim t`, in both
directions. The reference model is the paper's `D(λ)` (p. 50): a finitely supported distribution
`p` over a family `Ref` of mixed ordinary/read runtimes (`Quantum.mixedLawWith`). The
random-oracle model is the uniform distribution (`Quantum.uniformWeights`) over the family of
`Quantum.romVCOracle`; see `Quantum.simulates_uniformWeights_iff`. -/
@[expose]
def Simulates {Ω : Type*} (p : StdSimplex ℝ Ω) (Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y))
    (E : VCOracle k X Y) (κsim : ℕ → ℝ≥0∞) : Prop :=
  ∀ (t : ℕ) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (mixedOracleSpec k X Y) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A), x.IsTotalQueryBound t →
    E.mixedRuntime.evalDistMap .instruments x ρ f {true} ≤
        mixedLawWith p Ref .instruments x ρ (fun _ ↦ f) {true} + κsim t ∧
      mixedLawWith p Ref .instruments x ρ (fun _ ↦ f) {true} ≤
        E.mixedRuntime.evalDistMap .instruments x ρ f {true} + κsim t

variable {Ω : Type*} {p : StdSimplex ℝ Ω} {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)}
  {E : VCOracle k X Y}

/-- P1 is monotone in the error. -/
theorem Simulates.mono {κ κ' : ℕ → ℝ≥0∞} (h : Simulates.{v, w} p Ref E κ) (hκ : κ ≤ κ') :
    Simulates.{v, w} p Ref E κ' := fun t _ _ x f ρ hx ↦
  ⟨(h t x f ρ hx).1.trans (add_le_add le_rfl (hκ t)),
    (h t x f ρ hx).2.trans (add_le_add le_rfl (hκ t))⟩

/-- **P1 against a uniformly sampled reference model**, such as the random-oracle model: the
mixture is `Quantum.sampledEvalDistMap`. -/
theorem simulates_uniformWeights_iff {Ω : Type} [SampleableType Ω]
    {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)} {κ : ℕ → ℝ≥0∞} :
    Simulates.{v, w} (uniformWeights Ω) Ref E κ ↔
      ∀ (t : ℕ) {A : QReg} {W : QReg → Type w}
        (x : QuantumComp LocalSig.instruments.{v} (mixedOracleSpec k X Y) W A)
        (f : (Σ u, W u) → Bool) (ρ : SubState A), x.IsTotalQueryBound t →
        E.mixedRuntime.evalDistMap .instruments x ρ f {true} ≤
            sampledEvalDistMap Ref .instruments x ρ (fun _ ↦ f) {true} + κ t ∧
          sampledEvalDistMap Ref .instruments x ρ (fun _ ↦ f) {true} ≤
            E.mixedRuntime.evalDistMap .instruments x ρ f {true} + κ t := by
  simp only [Simulates, mixedLawWith_uniformWeights]

/-- **P1 from its uniform form**: bounds against `Quantum.sampledEvalDistMap` give P1 against the
uniform distribution. -/
theorem Simulates.ofUniform {Ω : Type} [SampleableType Ω]
    {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)} {κ : ℕ → ℝ≥0∞}
    (h : ∀ (t : ℕ) {A : QReg} {W : QReg → Type w}
      (x : QuantumComp LocalSig.instruments.{v} (mixedOracleSpec k X Y) W A)
      (f : (Σ u, W u) → Bool) (ρ : SubState A), x.IsTotalQueryBound t →
      E.mixedRuntime.evalDistMap .instruments x ρ f {true} ≤
          sampledEvalDistMap Ref .instruments x ρ (fun _ ↦ f) {true} + κ t ∧
        sampledEvalDistMap Ref .instruments x ρ (fun _ ↦ f) {true} ≤
          E.mixedRuntime.evalDistMap .instruments x ρ f {true} + κ t) :
    Simulates.{v, w} (uniformWeights Ω) Ref E κ :=
  simulates_uniformWeights_iff.mpr h

/-- Ordinary-only simulation is the restriction obtained by structural left injection. -/
theorem Simulates.restrictOrdinary {F : Ω → VCOracle k X Y} {κ : ℕ → ℝ≥0∞}
    (h : Simulates.{v, w} p (fun ω ↦ (F ω).mixedRuntime) E κ) {A : QReg}
    {W : QReg → Type w} (t : ℕ)
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (oIn k X Y)) W A)
    (f : (Σ B, W B) → Bool) (ρ : SubState A) (hx : x.IsTotalQueryBound t) :
    E.coherent.toRuntime.evalDistMap .instruments x ρ f {true} ≤
        mixedLawWith p (fun ω ↦ (F ω).coherent.toRuntime) .instruments x ρ
          (fun _ ↦ f) {true} + κ t ∧
      mixedLawWith p (fun ω ↦ (F ω).coherent.toRuntime) .instruments x ρ
          (fun _ ↦ f) {true} ≤
        E.coherent.toRuntime.evalDistMap .instruments x ρ f {true} + κ t := by
  have h' := h t x.liftOrdinary f ρ
    ((QuantumComp.isTotalQueryBound_liftOrdinary_iff x t).mpr hx)
  have hr (G : VCOracle k X Y) :
      G.mixedRuntime.run .instruments x.liftOrdinary = G.coherent.toRuntime.run .instruments x :=
    QuantumRuntime.run_liftOrdinary (t := classicalReadSpec (Fin k × X) (Option Y))
      G.coherent.toRuntime .instruments G.classicalRead.step x
  have hl (G : VCOracle k X Y) :
      G.mixedRuntime.evalDistMap .instruments x.liftOrdinary ρ f =
        G.coherent.toRuntime.evalDistMap .instruments x ρ f := by
    simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost, hr]
    rfl
  simpa only [mixedLawWith, hl] using h'

end simulation

/-! ## P2: oracle commutativity -/

section commute

/-- The first factor and the shared register: `(M₁ × M₂) × S ≃ (M₁ × S) × M₂`. -/
@[expose]
def slotFst (M₁ M₂ S : Type*) : (M₁ × M₂) × S ≃ (M₁ × S) × M₂ where
  toFun a := ((a.1.1, a.2), a.1.2)
  invFun b := ((b.1.1, b.2), b.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The second factor and the shared register: `(M₁ × M₂) × S ≃ (M₂ × S) × M₁`. -/
@[expose]
def slotSnd (M₁ M₂ S : Type*) : (M₁ × M₂) × S ≃ (M₂ × S) × M₁ where
  toFun a := ((a.1.2, a.2), a.1.1)
  invFun b := ((b.2, b.1.1), b.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The first factor of the output and the shared register:
`((M₁ × M₂) × N) × S ≃ (M₁ × S) × (M₂ × N)`. -/
@[expose]
def slotFst₃ (M₁ M₂ N S : Type*) : ((M₁ × M₂) × N) × S ≃ (M₁ × S) × (M₂ × N) where
  toFun a := ((a.1.1.1, a.2), (a.1.1.2, a.1.2))
  invFun b := (((b.1.1, b.2.1), b.2.2), b.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The second factor of the output and the shared register:
`((M₁ × M₂) × N) × S ≃ (M₂ × S) × (M₁ × N)`. -/
@[expose]
def slotSnd₃ (M₁ M₂ N S : Type*) : ((M₁ × M₂) × N) × S ≃ (M₂ × S) × (M₁ × N) where
  toFun a := ((a.1.1.2, a.2), (a.1.1.1, a.1.2))
  invFun b := (((b.2.1, b.1.1), b.2.2), b.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}

/-- **First half of P2** (ePrint 2025/2166, Def 7.3, p. 50): the oracle unitaries commute
when applied to two query registers `X₁Y₁` and `X₂Y₂` sharing the private register,
`[(O_i)_{X₂Y₂S}, (O_j)_{X₁Y₁S}] = 0` for all `i, j`, including `i = j`. -/
@[expose]
def OraclesCommute (E : VCOracle k X Y) : Prop :=
  ∀ i j : Fin k, onFactor (slotSnd (X × Y) (X × Y) E.S) (E.U i) *
      onFactor (slotFst (X × Y) (X × Y) E.S) (E.U j) =
    onFactor (slotFst (X × Y) (X × Y) E.S) (E.U j) *
      onFactor (slotSnd (X × Y) (X × Y) E.S) (E.U i)

variable (k X Y Cm Z) in
/-- The output register of a P2 adversary (ePrint 2025/2166, p. 50): an oracle query register
`X₁Y₁ = X × Y`, an extraction register `X₂Y₂ = TpIC × Z`, and the rest `Env`. -/
abbrev ComOut (Env : QReg) : QReg :=
  QReg.of (((X × Y) × (TpIC k Cm × Z)) × Env)

variable (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)

/-- The commutation defect `C = (U_ME)_{X₂Y₂S} (O_i)_{X₁Y₁S} − (O_i)_{X₁Y₁S} (U_ME)_{X₂Y₂S}` on the
output of a P2 adversary and the private register, so that `Ψ − Ψ′ = C φ` (ePrint 2025/2166,
p. 50). -/
@[expose]
noncomputable def comDefect (Env : QReg) (i : Fin k) :
    Matrix (ComOut k X Y Cm Z Env × E.S) (ComOut k X Y Cm Z Env × E.S) ℂ :=
  onFactor (slotSnd₃ (X × Y) (TpIC k Cm × Z) Env E.S) (extractUnitary ME code) *
      onFactor (slotFst₃ (X × Y) (TpIC k Cm × Z) Env E.S) (E.U i) -
    onFactor (slotFst₃ (X × Y) (TpIC k Cm × Z) Env E.S) (E.U i) *
      onFactor (slotSnd₃ (X × Y) (TpIC k Cm × Z) Env E.S) (extractUnitary ME code)

/-- **P2's distance `‖Ψ − Ψ′‖²`** (ePrint 2025/2166, p. 50), for a general program: the sum
over outcomes `a` of `tr(C σ_a C†)`, where `σ_a` is the joint post-state of the adversary's output
and the private register of `EO^(Ext)`. The joint state is used because `C` acts on the private
register. For a pure input and a unitary adversary it is `‖C V |ψ⟩|ϕ⟩‖²`
(`Quantum.comError_of_pure`). -/
@[expose]
noncomputable def comError (i : Fin k) {A Env : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A
      (ComOut k X Y Cm Z Env) α) (ρ : SubState A) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal (comDefect E ME code Env i *
    (show Matrix (ComOut k X Y Cm Z Env × E.S) (ComOut k X Y Cm Z Env × E.S) ℂ from
      ((E.mixedExtractRuntime ME code).jointPost₂ .instruments x ρ a).matrix) *
      (comDefect E ME code Env i)ᴴ).trace.re

/-- The extraction register and arbitrary retained workspace of a read comparison. -/
abbrev ReadComOut (k : ℕ) (Cm Z : Type) [Fintype Cm] [DecidableEq Cm]
    [Fintype Z] [DecidableEq Z] (Env : QReg) : QReg :=
  QReg.of ((TpIC k Cm × Z) × Env)

/-- The difference between reading after extraction and extracting after reading, retaining
one answer branch on the shared private register. -/
@[expose]
noncomputable def readComDefect (Env : QReg) (c : Fin k × X) (a : Option Y) :
    Matrix (ReadComOut k Cm Z Env × E.S) (ReadComOut k Cm Z Env × E.S) ℂ :=
  let U := onFactor (slotFst (TpIC k Cm × Z) Env E.S) (extractUnitary ME code)
  let J := (1 : Matrix (ReadComOut k Cm Z Env) (ReadComOut k Cm Z Env) ℂ) ⊗ₖ
    E.classicalRead.A c a
  J * U - U * J

/-- The squared read/extraction defect, summed over retained classical outcomes and all read
answers. The final classical outcome selects the address, so adaptive addresses are included. -/
@[expose]
noncomputable def readComError {A Env : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A
      (ReadComOut k Cm Z Env) α) (ρ : SubState A) (c : α → Fin k × X) : ℝ≥0∞ :=
  ∑' l, ∑ a, ENNReal.ofReal (readComDefect E ME code Env (c l) a *
    (show Matrix (ReadComOut k Cm Z Env × E.S) (ReadComOut k Cm Z Env × E.S) ℂ from
      ((E.mixedExtractRuntime ME code).jointPost₂ .instruments x ρ l).matrix) *
    (readComDefect E ME code Env (c l) a)ᴴ).trace.re

/-- **Second half of P2** (ePrint 2025/2166, Def 7.3, p. 50): against every `t`-query
mixed prefix querying `EO^(Ext)`, both the ordinary commutation distance and the summed
read commutation distance are at most `κcom t`. All calls count toward the same total budget;
the read address may depend on the retained final classical outcome. -/
@[expose]
def ComBound (κcom : ℕ → ℝ≥0∞) : Prop :=
  (∀ (i : Fin k) (t : ℕ) {A Env : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A
      (ComOut k X Y Cm Z Env) α) (ρ : SubState A),
    x.IsTotalQueryBound t → comError E ME code i x ρ ≤ κcom t) ∧
  (∀ (t : ℕ) {A Env : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A
      (ReadComOut k Cm Z Env) α) (ρ : SubState A) (c : α → Fin k × X),
    x.IsTotalQueryBound t → readComError E ME code x ρ c ≤ κcom t)

variable {E ME code}

/-- The commutation bound is monotone in the error. -/
theorem ComBound.mono {κ κ' : ℕ → ℝ≥0∞} (h : ComBound.{v, w} E ME code κ) (hκ : κ ≤ κ') :
    ComBound.{v, w} E ME code κ' :=
  ⟨fun i t _ _ _ x ρ hx ↦ (h.1 i t x ρ hx).trans (hκ t),
    fun t _ _ _ x ρ c hx ↦ (h.2 t x ρ c hx).trans (hκ t)⟩

/-- Two valid commutation errors can be minimized pointwise. -/
theorem ComBound.min {κ κ' : ℕ → ℝ≥0∞} (h : ComBound.{v, w} E ME code κ)
    (h' : ComBound.{v, w} E ME code κ') :
    ComBound.{v, w} E ME code (fun t ↦ min (κ t) (κ' t)) :=
  ⟨fun i t _ _ _ x ρ hx ↦ le_min (h.1 i t x ρ hx) (h'.1 i t x ρ hx),
    fun t _ _ _ x ρ c hx ↦ le_min (h.2 t x ρ c hx) (h'.2 t x ρ c hx)⟩

/-- The trace of `C |v⟩⟨v| C†` is the squared norm of `C v`. -/
theorem trace_mul_vecMulVec_mul_conjTranspose_re {m n : Type*} [Fintype m] [Fintype n]
    (C : Matrix n m ℂ) (v : m → ℂ) :
    (C * vecMulVec v (star v) * Cᴴ).trace.re = ∑ a, ‖(C *ᵥ v) a‖ ^ 2 := by
  rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, trace_vecMulVec]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.re_sum,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

variable (E ME code)

/-- **P2's distance for a single-outcome adversary**: if the run of `x` against `EO^(Ext)` has the
single outcome `a₀`, with the Kraus map of `V`, and every other branch is zero, then the distance
is `tr(C V (ρ ⊗ ϕ) V† C†)`. -/
theorem comError_eq_of_branch {i : Fin k} {A Env : QReg} {α : Type w}
    {x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A
      (ComOut k X Y Cm Z Env) α} (a₀ : α)
    (V : Matrix (ComOut k X Y Cm Z Env × E.S) (A × E.S) ℂ)
    (hx₀ : ((E.mixedExtractRuntime ME code).run₂ .instruments x).branch a₀ =
      MatrixMap.conj V)
    (hx : ∀ a ≠ a₀, ((E.mixedExtractRuntime ME code).run₂ .instruments x).branch a = 0)
    (ρ : SubState A) :
    comError E ME code i x ρ = ENNReal.ofReal (comDefect E ME code Env i *
      (V * (ρ.matrix ⊗ₖ E.init.matrix) * Vᴴ) * (comDefect E ME code Env i)ᴴ).trace.re := by
  rw [comError, tsum_eq_single a₀ fun a ha ↦ by
    rw [QuantumRuntime.matrix_jointPost₂, hx a ha, LinearMap.zero_apply]
    erw [Matrix.mul_zero, Matrix.zero_mul, trace_zero]
    simp]
  simp only [QuantumRuntime.matrix_jointPost₂, hx₀]
  rfl

/-- **The pure form of P2's distance** (ePrint 2025/2166, p. 50): for a single-outcome
adversary with the Kraus map of `V`, started so that the joint input `ρ ⊗ ϕ` is the pure state
`|v⟩⟨v|`, the distance is `‖C V v‖² = ‖Ψ − Ψ′‖²`. -/
theorem comError_of_pure {i : Fin k} {A Env : QReg} {α : Type w}
    {x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A
      (ComOut k X Y Cm Z Env) α} (a₀ : α)
    (V : Matrix (ComOut k X Y Cm Z Env × E.S) (A × E.S) ℂ)
    (hx₀ : ((E.mixedExtractRuntime ME code).run₂ .instruments x).branch a₀ =
      MatrixMap.conj V)
    (hx : ∀ a ≠ a₀, ((E.mixedExtractRuntime ME code).run₂ .instruments x).branch a = 0)
    {ρ : SubState A} (v : A × E.S → ℂ)
    (hv : ρ.matrix ⊗ₖ E.init.matrix = vecMulVec v (star v)) :
    comError E ME code i x ρ =
      ENNReal.ofReal (∑ b, ‖((comDefect E ME code Env i * V) *ᵥ v) b‖ ^ 2) := by
  rw [comError_eq_of_branch E ME code a₀ V hx₀ hx, hv, ← trace_mul_vecMulVec_mul_conjTranspose_re,
    conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The ordinary commutator is bounded by four times the joint input trace. -/
theorem comDefect_trace_le_four (Env : QReg) (i : Fin k)
    (ρ : SubState (ComOut k X Y Cm Z Env × E.S)) :
    ENNReal.ofReal (comDefect E ME code Env i * ρ.matrix *
      (comDefect E ME code Env i)ᴴ).trace.re ≤ 4 * ENNReal.ofReal ρ.matrix.trace.re := by
  classical
  let U := onFactor (slotSnd₃ (X × Y) (TpIC k Cm × Z) Env E.S) (extractUnitary ME code)
  let V := onFactor (slotFst₃ (X × Y) (TpIC k Cm × Z) Env E.S) (E.U i)
  have hU := onFactor_mem_unitaryGroup (slotSnd₃ (X × Y) (TpIC k Cm × Z) Env E.S)
    (extractUnitary_mem_unitaryGroup ME code)
  have hV := onFactor_mem_unitaryGroup (slotFst₃ (X × Y) (TpIC k Cm × Z) Env E.S)
    (E.unitary i)
  have h := sum_trace_conj_sub_le_four (fun _ : Unit ↦ U * V) (fun _ : Unit ↦ V * U)
    (by simpa only [Fintype.sum_unique, U, V, star_eq_conjTranspose] using
      (mem_unitaryGroup_iff'.mp (mul_mem hU hV)))
    (by simpa only [Fintype.sum_unique, U, V, star_eq_conjTranspose] using
      (mem_unitaryGroup_iff'.mp (mul_mem hV hU))) ρ.posSemidef
  simpa only [Fintype.sum_unique, MatrixMap.conj_apply, U, V, comDefect] using h

/-- Summing every retained answer gives a read commutator cap independent of the answer count. -/
theorem readComDefect_trace_le_four (Env : QReg) (c : Fin k × X)
    (ρ : SubState (ReadComOut k Cm Z Env × E.S)) :
    ∑ a, ENNReal.ofReal (readComDefect E ME code Env c a * ρ.matrix *
      (readComDefect E ME code Env c a)ᴴ).trace.re ≤ 4 * ENNReal.ofReal ρ.matrix.trace.re := by
  classical
  let U := onFactor (slotFst (TpIC k Cm × Z) Env E.S) (extractUnitary ME code)
  let J := fun a ↦ (1 : Matrix (ReadComOut k Cm Z Env) (ReadComOut k Cm Z Env) ℂ) ⊗ₖ
    E.classicalRead.A c a
  have hU : Uᴴ * U = 1 := mem_unitaryGroup_iff'.mp
    (onFactor_mem_unitaryGroup (slotFst (TpIC k Cm × Z) Env E.S)
      (extractUnitary_mem_unitaryGroup ME code))
  have hJ : ∑ a, (J a)ᴴ * J a = 1 := E.read_kraus_complete _ c
  have hF : ∑ a, (J a * U)ᴴ * (J a * U) = 1 := by
    calc
      _ = Uᴴ * (∑ a, (J a)ᴴ * J a) * U := by
        simp only [conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, hU]
  have hG : ∑ a, (U * J a)ᴴ * (U * J a) = 1 := by
    simpa only [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U,
      hU, Matrix.one_mul] using hJ
  exact sum_trace_conj_sub_le_four (fun a ↦ J a * U) (fun a ↦ U * J a) hF hG ρ.posSemidef

/-- Both commutation defects are at most four for every total call budget. -/
theorem comBound_four : ComBound.{v, w} E ME code (fun _ ↦ 4) := by
  constructor
  · intro i t A Env α x ρ _
    exact (ENNReal.tsum_le_tsum fun a ↦ comDefect_trace_le_four E ME code Env i
      ((E.mixedExtractRuntime ME code).jointPost₂ .instruments x ρ a)).trans
      (tsum_weighted_trace_le _
        (QuantumRuntime.tsum_jointPost₂_trace_le_one _ _ x ρ) 4)
  · intro t A Env α x ρ c _
    exact (ENNReal.tsum_le_tsum fun a ↦ readComDefect_trace_le_four E ME code Env (c a)
      ((E.mixedExtractRuntime ME code).jointPost₂ .instruments x ρ a)).trans
      (tsum_weighted_trace_le _
        (QuantumRuntime.tsum_jointPost₂_trace_le_one _ _ x ρ) 4)

end commute

/-! ## Classical calls from the challenger -/

section calls

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] {Dm : Fin k → Type}

/-- The answer register `Y` of a reading of the coherent register of `EO^(Ext)` on an oracle
port. Readings on the extraction port, which a call of an oracle port does not produce, give
`0`. -/
@[expose]
def readY [Zero Y] : (Σ i, extIn k X Y Cm Z i) → Y
  | ⟨.inl _, m⟩ => (m : X × Y).2
  | ⟨.inr _, _⟩ => 0

/-- An ordinary basis call of oracle `j` at `t`: call the coherent port on `|j, t, 0⟩`,
measure the port register, and return the answer `y`. Checkers use `checkedRead` through
`runClassicalChecked` to retain the distinction between missing and present answers. -/
@[expose]
noncomputable def oracleCall [Zero Y] (B : QReg) (j : Fin k) (t : X) :
    QComp (cohSpec (extIn k X Y Cm Z)) B B Y :=
  QComp.callBasis (spec := cohSpec (extIn k X Y Cm Z)) () B
    (⟨.inl j, ((t, 0) : X × Y)⟩ : Σ i, extIn k X Y Cm Z i) fun o _ ↦ readY o

/-- Read a classical address through the dedicated read port. -/
@[expose]
noncomputable def checkedRead (B : QReg) (j : Fin k) (t : X) :
    QComp (mixedExtSpec k X Y Cm Z) B B (Option Y) :=
  QuantumComp₂.bind (QComp.act (B := QReg.of (Unit × B))
    (SubInstrument.relabel (Equiv.uniqueProd B Unit).symm)) fun _ ↦
    QuantumComp₂.bind (QuantumComp₂.query (spec := mixedExtSpec k X Y Cm Z)
      (.inr (j, t)) B (Equiv.refl (Unit × B))) fun a ↦
      QuantumComp₂.bind (QComp.act (SubInstrument.relabel (Equiv.uniqueProd B Unit))) fun _ ↦
        QuantumComp₂.pure a

/-- Coins return present values; a missing oracle answer short-circuits the classical program. -/
@[expose]
noncomputable def checkedOracleImpl (B : QReg) (j : Fin k) :
    QueryImpl (unifSpec + (X →ₒ Y)) (OptionT (QComp (mixedExtSpec k X Y Cm Z) B B)) :=
  (fun n ↦ OptionT.mk (some <$> QComp.coinImpl (mixedExtSpec k X Y Cm Z) B n) :
    QueryImpl unifSpec (OptionT (QComp (mixedExtSpec k X Y Cm Z) B B))) +
    (fun t ↦ OptionT.mk (checkedRead B j t) :
      QueryImpl (X →ₒ Y) (OptionT (QComp (mixedExtSpec k X Y Cm Z) B B)))

/-- Interpret a classical algorithm using uniform coins and checked oracle answers. -/
@[expose]
noncomputable def runClassicalChecked {α : Type} (B : QReg) (j : Fin k)
    (p : OracleComp (unifSpec + (X →ₒ Y)) α) :
    QComp (mixedExtSpec k X Y Cm Z) B B (Option α) :=
  (simulateQ (checkedOracleImpl B j) p).run

/-- The checked interpreter returns present pure values. -/
@[simp]
theorem runClassicalChecked_pure {α : Type} (B : QReg) (j : Fin k) (a : α) :
    runClassicalChecked (X := X) (Y := Y) (Cm := Cm) (Z := Z) B j (pure a) =
      QuantumComp₂.pure (some a) := rfl

/-- A checked query returns its optional answer before deciding whether to continue. -/
theorem runClassicalChecked_query_bind {α : Type} (B : QReg) (j : Fin k)
    (t : (unifSpec + (X →ₒ Y)).Domain)
    (f : (unifSpec + (X →ₒ Y)).Range t → OracleComp (unifSpec + (X →ₒ Y)) α) :
    runClassicalChecked (Cm := Cm) (Z := Z) B j (liftM ((unifSpec + (X →ₒ Y)).query t) >>= f) =
      ((checkedOracleImpl B j t).run).bind (fun a ↦
        match a with
        | none => QuantumComp₂.pure none
        | some y => runClassicalChecked B j (f y)) := by
  rw [runClassicalChecked, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind,
    Option.elimM, QuantumComp₂.bind_eq]
  congr 1
  funext a
  cases a <;> rfl

/-- A checked read is a lossless program, including the missing-answer branch. -/
theorem lossless_checkedRead (B : QReg) (j : Fin k) (t : X) :
    (checkedRead (Y := Y) (Cm := Cm) (Z := Z) B j t).Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_relabel _)) fun _ ↦
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_query _ _ _) fun _ ↦
      QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_relabel _)) fun _ ↦
        QuantumComp₂.lossless_pure _

/-- Missing answers return a value, so the checked fold preserves losslessness. -/
theorem lossless_runClassicalChecked {α : Type} (B : QReg) (j : Fin k)
    (p : OracleComp (unifSpec + (X →ₒ Y)) α) :
    (runClassicalChecked (Cm := Cm) (Z := Z) B j p).Lossless .instruments := by
  induction p using OracleComp.inductionOn with
  | pure a => exact QuantumComp₂.lossless_pure _
  | query_bind t f ih =>
    rw [runClassicalChecked_query_bind]
    apply QuantumComp₂.lossless_bind
    · cases t with
      | inl n =>
        exact QuantumComp₂.lossless_bind (QComp.lossless_coinImpl n) fun _ ↦
          QuantumComp₂.lossless_pure _
      | inr t => exact lossless_checkedRead B j t
    · intro a
      cases a with
      | none => exact QuantumComp₂.lossless_pure _
      | some y => exact ih y

/-- A read restores the trivial public factor around the runtime's read-port step. -/
theorem run₂_checkedRead_eq (R : QuantumRuntime (mixedExtSpec k X Y Cm Z))
    (B : QReg) (j : Fin k) (t : X) :
    R.run₂ .instruments (checkedRead B j t) =
      (R.queryStep (A := QReg.of (Unit × B)) (.inr (j, t)) B (Equiv.refl _)).reindex
        ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl R.D))
        ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl R.D)) := by
  rw [checkedRead, QuantumRuntime.run₂_act_bind, SubInstrument.frame_relabel]
  unfold SubInstrument.reindex
  refine congrArg (fun f : Unit → SubInstrument ((Unit × B) × R.D) (B × R.D) (Option Y) ↦
    (SubInstrument.relabel
      ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl R.D)).symm).bind f) ?_
  funext u
  have hq := R.run₂_query_bind (A := QReg.of (Unit × B)) (B := B)
    .instruments (.inr (j, t)) B
    (Equiv.refl (Unit × B)) (fun a ↦
      QuantumComp₂.bind (QComp.act (SubInstrument.relabel (Equiv.uniqueProd B Unit)))
        fun _ ↦ QuantumComp₂.pure a)
  refine hq.trans ?_
  refine congrArg (fun f : Option Y → SubInstrument ((Unit × B) × R.D) (B × R.D) (Option Y) ↦
    (R.queryStep (A := QReg.of (Unit × B)) (.inr (j, t)) B (Equiv.refl _)).bind f) ?_
  funext a
  rw [QuantumRuntime.run₂_act_bind]
  erw [SubInstrument.frame_relabel]
  exact congrArg (fun f : Unit → SubInstrument (B × R.D) (B × R.D) (Option Y) ↦
    (SubInstrument.relabel
      ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl R.D))).bind f)
    (funext fun _ ↦ R.run₂_pure .instruments a)

variable [AddGroup Z]

/-- The read-port program executes the base oracle's framed projective instrument. -/
theorem run₂_checkedRead (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S)
    (code : TpDCode k Dm Z) (B : QReg) (j : Fin k) (t : X) :
    (E.mixedExtractRuntime ME code).run₂ .instruments (checkedRead B j t) =
      E.toEmulatedOracle.read E.classicalRead (j, t) B := by
  rw [run₂_checkedRead_eq]
  rfl

/-- Every actual checked-read branch is conjugation by its answer projector. -/
theorem branch_run₂_checkedRead (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S)
    (code : TpDCode k Dm Z) (B : QReg) (j : Fin k) (t : X) (a : Option Y) :
    ((E.mixedExtractRuntime ME code).run₂ .instruments (checkedRead B j t)).branch a =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ E.classicalRead.A (j, t) a) := by
  rw [run₂_checkedRead, EmulatedOracle.read_branch]

/-- The real oracle always returns its function value and leaves the joint state unchanged. -/
theorem run₂_checkedRead_rom [AddCommGroup Y] (H : Fin k → X → Y)
    (ME : MultiExtractor k Cm Dm (romVCOracle k X Y H).S) (code : TpDCode k Dm Z)
    (B : QReg) (j : Fin k) (t : X) :
    ((romVCOracle k X Y H).mixedExtractRuntime ME code).run₂ .instruments
      (checkedRead B j t) = SubInstrument.pure (some (H j t)) := by
  apply DSubInstrument.ext
  funext a
  rw [branch_run₂_checkedRead]
  change MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
    (if a = some (H j t) then (1 : Matrix Unit Unit ℂ) else 0)) = _
  by_cases h : a = some (H j t)
  · subst a
    simp only [ite_true, one_kronecker_one, MatrixMap.conj_one]
    erw [SubInstrument.branch_pure_self]
    rfl
  · simp only [ite_eq_right h, kronecker_zero, MatrixMap.conj_zero]
    erw [SubInstrument.branch_pure_of_ne h]
    rfl

/-- Against a real function, the complete joint checked law is the ordinary classical run
with its result wrapped in `some`. Uniform coins and the residual workspace are retained. -/
theorem runClassicalChecked_rom [AddCommGroup Y] {α : Type} (H : Fin k → X → Y)
    (ME : MultiExtractor k Cm Dm (romVCOracle k X Y H).S) (code : TpDCode k Dm Z)
    (B : QReg) (j : Fin k) (p : OracleComp (unifSpec + (X →ₒ Y)) α) :
    let R := (romVCOracle k X Y H).mixedExtractRuntime ME code
    R.run₂ .instruments (runClassicalChecked B j p) =
      (R.run₂ .instruments (p.toQuantumAt
        (QComp.coinImpl (mixedExtSpec k X Y Cm Z) B +
          (fun t ↦ QuantumComp₂.pure (H j t) :
            QueryImpl (X →ₒ Y) (QComp (mixedExtSpec k X Y Cm Z) B B))))).map some := by
  dsimp only
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [runClassicalChecked_query_bind, OracleComp.toQuantumAt_query_bind,
      QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind]
    cases t with
    | inl n =>
      change (((romVCOracle k X Y H).mixedExtractRuntime ME code).run₂ .instruments
        ((QComp.coinImpl (mixedExtSpec k X Y Cm Z) B n).map some)).bind _ = _
      simp only [QuantumRuntime.run₂_map, SubInstrument.map_eq_bind_pure,
        DSubInstrument.bind_assoc, SubInstrument.pure_bind]
      congr 1
      funext y
      exact ih y
    | inr t =>
      change (((romVCOracle k X Y H).mixedExtractRuntime ME code).run₂ .instruments
        (checkedRead B j t)).bind _ = _
      rw [run₂_checkedRead_rom]
      change _ = SubInstrument.map some
        ((((romVCOracle k X Y H).mixedExtractRuntime ME code).run₂ .instruments
          (QuantumComp₂.pure (H j t))).bind _)
      rw [QuantumRuntime.run₂_pure]
      erw [SubInstrument.pure_bind, SubInstrument.pure_bind]
      exact ih (H j t)

/-- The decoded output of a reading of the coherent register of `EO^(Ext)` on the extraction
port, at the length of `tic`. Readings on an oracle port give `none`. -/
@[expose]
noncomputable def readExtract (code : TpDCode k Dm Z) (tic : TpIC k Cm) :
    (Σ i, extIn k X Y Cm Z i) → Option (TpDLen k Dm tic.1)
  | ⟨.inl _, _⟩ => none
  | ⟨.inr _, m⟩ => code.decodeAt tic.1 (m : TpIC k Cm × Z).2

/-- **Extraction from inside an experiment** (`(m_i, td_i)_i ← MultiExtract(tic, S)`,
ePrint 2025/2166, p. 51): call the extraction port on `|tic, 0⟩`, measure the output
register, and decode it. Its branches are the projectors onto the fibres of
`MultiExtract(tic, ·)` on the private register (`Quantum.run₂_extractQuery_branch`). -/
@[expose]
noncomputable def extractQuery (code : TpDCode k Dm Z) (B : QReg) (tic : TpIC k Cm) :
    QComp (cohSpec (extIn k X Y Cm Z)) B B (Option (TpDLen k Dm tic.1)) :=
  QComp.callBasis (spec := cohSpec (extIn k X Y Cm Z)) () B
    (⟨.inr (), ((tic, 0) : TpIC k Cm × Z)⟩ : Σ i, extIn k X Y Cm Z i) fun o _ ↦
      readExtract code tic o

variable [∀ i, DecidableEq (Dm i)] (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S)
  (code : TpDCode k Dm Z) (B : QReg)

/-- **Extraction is the measurement of `MultiExtract(tic, ·)`**: the branch of `extractQuery` at
`some tdm` is the Kraus map of `1_B ⊗ Π_tdm`. This is the reading of extraction used in game G0
of Lemma 9.3 of ePrint 2025/2166 (p. 59). -/
theorem run₂_extractQuery_branch (tic : TpIC k Cm) (tdm : TpDLen k Dm tic.1) :
    ((E.withExtract ME code).coherent.toRuntime.run₂ .instruments
      (extractQuery code B tic)).branch (some tdm) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ extractProj ME tic tdm) := by
  rw [extractQuery, EmulatedOracle.branch_run₂_callBasis]
  rw [Finset.sum_eq_single (⟨.inr (), ((tic, code.enc ⟨tic.1, tdm⟩) : TpIC k Cm × Z)⟩ :
    Σ i, extIn k X Y Cm Z i)]
  · simp only [readExtract, TpDCode.decodeAt_enc, ↓reduceIte]
    congr 2
    ext d d'
    rw [EmulatedOracle.block_apply]
    refine (EmulatedOracle.coherent_U_apply_self _ (Sum.inr ()) _ _ _ _).trans ?_
    refine (extractUnitary_apply ME code _ _ _ _ d d').trans ?_
    unfold extractProj
    by_cases hd : d = d'
    · subst hd
      refine Eq.trans ?_ (diagonal_apply_eq _ d).symm
      by_cases ht : ME.extract tic d = tdm
      · exact (ite_eq_left ⟨rfl, by rw [zero_add, ht], rfl⟩).trans (ite_eq_left ht).symm
      · refine (ite_eq_right fun h ↦ ht ?_).trans (ite_eq_right ht).symm
        exact (code.enc_mk_inj.mp (h.2.1.trans (zero_add _))).symm
    · exact (ite_eq_right fun h ↦ hd h.2.2).trans (diagonal_apply_ne _ hd).symm
  · rintro ⟨_ | _, m⟩ _ hne
    · simp only [readExtract, reduceCtorEq, ↓reduceIte]
    · obtain ⟨tic', z⟩ := m
      split_ifs with h
      · have hz : code.enc ⟨tic.1, tdm⟩ = z := code.decodeAt_eq_some_iff.mp h
        have ht : tic' ≠ tic := fun ht ↦ hne (by subst ht hz; rfl)
        have hb : (E.withExtract ME code).coherent.block ()
            ⟨.inr (), ((tic', z) : TpIC k Cm × Z)⟩
            ⟨.inr (), ((tic, 0) : TpIC k Cm × Z)⟩ = 0 := by
          ext d d'
          rw [EmulatedOracle.block_apply]
          refine (EmulatedOracle.coherent_U_apply_self _ (Sum.inr ()) _ _ _ _).trans ?_
          refine (extractUnitary_apply ME code _ _ _ _ d d').trans ?_
          simp [ht]
        rw [hb, kronecker_zero, MatrixMap.conj_zero]
      · rfl
  · simp

omit [∀ i, DecidableEq (Dm i)] in
/-- Extraction never reports `none`: that branch is zero. -/
theorem run₂_extractQuery_branch_none (tic : TpIC k Cm) :
    ((E.withExtract ME code).coherent.toRuntime.run₂ .instruments
      (extractQuery code B tic)).branch none = 0 := by
  classical
  rw [extractQuery, EmulatedOracle.branch_run₂_callBasis]
  refine Finset.sum_eq_zero fun o _ ↦ ?_
  split_ifs with h
  · have hb : (E.withExtract ME code).coherent.block () o
        ⟨.inr (), ((tic, 0) : TpIC k Cm × Z)⟩ = 0 := by
      ext d d'
      rw [EmulatedOracle.block_apply]
      obtain ⟨_ | _, m⟩ := o
      · exact EmulatedOracle.coherent_U_apply_of_ne _ Sum.inl_ne_inr _ _ _ _
      · obtain ⟨tic', z⟩ := m
        refine (EmulatedOracle.coherent_U_apply_self _ (Sum.inr ()) _ _ _ _).trans ?_
        refine (extractUnitary_apply ME code _ _ _ _ d d').trans ?_
        refine (ite_eq_right ?_).trans rfl
        rintro ⟨rfl, rfl, -⟩
        simp [readExtract] at h
    rw [hb, kronecker_zero, MatrixMap.conj_zero]
  · rfl

end calls

/-! ## The extraction experiments -/

section challengers

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z]
  {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type} (VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i))

/-- `VC_i.Check^{O_j}(cm, Q, ans, pf)` run from inside an experiment, with `Q = dom ans`
(ePrint 2025/2166, p. 51). -/
@[expose]
noncomputable def checkAt (B : QReg) (i j : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg)
    (pf : Pf i) : QComp (mixedExtSpec k X Y Cm Z) B B Bool := do
  let result ← runClassicalChecked B j ((VC i).check cm ans pf)
  pure (result.getD false)

/-- Checks preserve all mass: a missing read is a rejecting Boolean result. -/
theorem lossless_checkAt (B : QReg) (i j : Fin k) (cm : Cm)
    (ans : PartialVec (ℓ i) Msg) (pf : Pf i) :
    (checkAt (Z := Z) VC B i j cm ans pf).Lossless .instruments := by
  unfold checkAt
  exact QuantumComp₂.lossless_bind (lossless_runClassicalChecked B j _) fun _ ↦
    QuantumComp₂.lossless_pure _

/-- The complete joint check instrument is lossless, including all rejection branches. -/
theorem lossless_run₂_checkAt [AddGroup Z] (E : VCOracle k X Y)
    (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S) (code : TpDCode k (DmOf ℓ Msg Td) Z)
    (B : QReg) (i j : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg) (pf : Pf i) :
    ((E.mixedExtractRuntime ME code).run₂ .instruments
      (checkAt VC B i j cm ans pf)).Lossless :=
  QuantumRuntime.lossless_run₂ _ _ (lossless_checkAt VC B i j cm ans pf)
    (E.lossless_mixedExtractRuntime_step ME code)

/-- A malformed prescribed transcript rejects without reading. -/
theorem checkAt_pairs_none (i : Fin k) (io : (VC i).NonadaptiveCheck) (B : QReg)
    (j : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg) (pf : Pf i)
    (h : io.pairs cm ans pf = none) :
    checkAt (Z := Z) VC B i j cm ans pf = QuantumComp₂.pure false := by
  simp [checkAt, io.check_eq, h]

/-- An empty prescribed transcript accepts without reading. -/
theorem checkAt_pairs_nil (i : Fin k) (io : (VC i).NonadaptiveCheck) (B : QReg)
    (j : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg) (pf : Pf i)
    (h : io.pairs cm ans pf = some []) :
    checkAt (Z := Z) VC B i j cm ans pf = QuantumComp₂.pure true := by
  simp [checkAt, io.check_eq, h, checkIO]

/-- `VC_i.Open(Q, td)` run from inside an experiment, its coins answered by uniform coins
(ePrint 2025/2166, p. 51). It makes no oracle call. -/
@[expose]
noncomputable def openAt {spec : QuantumOracleSpec.{u₁, v₁}} (B : QReg) (i : Fin k)
    (Q : Finset (Fin (ℓ i))) (td : Td i) : QComp spec B B (Pf i) :=
  ((VC i).opening Q td).toQuantumAt (QComp.coinImpl spec B)

/-- The classical output of a P3 adversary (ePrint 2025/2166, p. 51): oracle indices,
commitments, and the set `W` of positions to check. -/
structure ExtractClaim (k : ℕ) (Cm : Type) where
  /-- The oracle index `idx_i` of each position. -/
  idx : Fin k → Fin k
  /-- The commitment `cm_i` of each position. -/
  cm : Fin k → Cm
  /-- The positions `W` whose checks are run. -/
  W : Finset (Fin k)

variable [AddGroup Z]

/-- **The P3 challenger** (ePrint 2025/2166, Def 7.3, p. 51), on the adversary's final
register `B`: extract `(m_i, td_i)_i` from the full tuple of the claim, open every position at
`Dom(m_i)`, run `VC_i.Check^{O_{idx_i}}` for `i ∈ W`, and report the event
`b = 0 ∧ |W| ≤ n ∧ (idx_i)_i distinct`. -/
@[expose]
noncomputable def extractChallenger (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (n : ℕ)
    (c : ExtractClaim k Cm) (B : QReg) : QComp (mixedExtSpec k X Y Cm Z) B B Bool :=
  QuantumComp₂.bind (QuantumComp.liftOrdinary
    (extractQuery code B (TpIC.full hk c.idx c.cm))) fun
    | none => QuantumComp₂.pure false
    | some tdm =>
      (QComp.pi fun i : Fin k ↦ openAt VC B i (tdm i).1.dom (tdm i).2).bind fun pf ↦
        (QComp.allIn c.W fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (tdm i).1 (pf i)).bind
          fun b ↦ QuantumComp₂.pure
            (!b && decide (c.W.card ≤ n) && decide (Function.Injective c.idx))

/-- The output of a P4 adversary (ePrint 2025/2166, p. 51): oracle indices and commitments
from the first stage, and from the second stage the answers `ans_i` with `Q_i = dom ans_i`, the
proofs `pf_i`, and the set `W` of positions checked before extraction. The two stages are one
program: nothing runs between them. -/
structure OpeningClaim (k : ℕ) (Cm Msg : Type) (ℓ : Fin k → ℕ) (Pf : Fin k → Type) where
  /-- The oracle index `idx_i` of each position. -/
  idx : Fin k → Fin k
  /-- The commitment `cm_i` of each position. -/
  cm : Fin k → Cm
  /-- The answers `ans_i`, defined on `Q_i`. -/
  ans : ∀ i, PartialVec (ℓ i) Msg
  /-- The proofs `pf_i`. -/
  pf : ∀ i, Pf i
  /-- The positions `W` checked before extraction. -/
  W : Finset (Fin k)

/-- **The P4 challenger** (ePrint 2025/2166, Def 7.3, p. 51), on the adversary's final
register `B`: run the checks on `W`, extract, run the checks on `[k] \ W`, open every position at
`Q_i` with the extracted trapdoor, and report the event `b₁ ∧ b₂ ∧ ∃ i, (m_i[Q_i] ≠ ans_i ∨
pf'_i ≠ pf_i) ∧ ∑ |Q_i| ≤ qs ∧ (idx_i)_i distinct`. The order matters, since checks call the
oracle and move the private register. -/
@[expose]
noncomputable def offlineChallenger [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf)
    (B : QReg) : QComp (mixedExtSpec k X Y Cm Z) B B Bool :=
  (QComp.allIn c.W fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).bind fun b₁ ↦
    QuantumComp₂.bind (QuantumComp.liftOrdinary
    (extractQuery code B (TpIC.full hk c.idx c.cm))) fun otdm ↦
      (QComp.allIn c.Wᶜ fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).bind
        fun b₂ ↦ match otdm with
          | none => QuantumComp₂.pure false
          | some tdm =>
            (QComp.pi fun i : Fin k ↦ openAt VC B i (c.ans i).dom (tdm i).2).bind fun pf' ↦
              QuantumComp₂.pure (b₁ && b₂ &&
                decide (∃ i : Fin k, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) &&
                decide (∑ i, (c.ans i).dom.card ≤ qs) && decide (Function.Injective c.idx))

variable (code : TpDCode k (DmOf ℓ Msg Td) Z)

/-- The check/extract/check prefix of the P4 challenger with all three classical results
retained, including the decoded extraction tuple and both acceptance bits. -/
noncomputable def offlineChecks (hk : 1 ≤ k) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    QComp (mixedExtSpec k X Y Cm Z) B B
      (Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :=
  (QComp.allIn c.W fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).bind fun b₁ ↦
    (QuantumComp₂.bind (QuantumComp.liftOrdinary
    (extractQuery code B (TpIC.full hk c.idx c.cm))) fun tdm ↦
      (QComp.allIn c.Wᶜ fun i ↦
        checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).map
          (fun b₂ ↦ (tdm, b₂))).map (fun r ↦ (b₁, r))

/-- The opening and mismatch decision of the P4 challenger, conditional on the retained
check/extract/check transcript. Randomized openings and both budget checks are preserved. -/
noncomputable def offlineFinish [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :
    QComp (mixedExtSpec k X Y Cm Z) B B Bool :=
  match r.2.1 with
  | none => QuantumComp₂.pure false
  | some tdm => (QComp.pi fun i : Fin k ↦
      openAt VC B i (c.ans i).dom (tdm i).2).bind fun pf' ↦
        QuantumComp₂.pure (r.1 && r.2.2 &&
          decide (∃ i : Fin k, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) &&
          decide (∑ i, (c.ans i).dom.card ≤ qs) && decide (Function.Injective c.idx))

omit [AddGroup Z] in
/-- On an accepted transcript, the finish opens with `tdm` and decides the mismatch event. -/
theorem offlineFinish_accept [DecidableEq Msg] [∀ i, DecidableEq (Pf i)] (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) (tdm : TpDLen k (DmOf ℓ Msg Td) (.full hk)) :
    offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true) =
      (QComp.pi fun i ↦ openAt VC B i (c.ans i).dom (tdm i).2).bind fun pf' ↦ .pure
        (decide (∃ i : Fin k, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) &&
          decide (∑ i, (c.ans i).dom.card ≤ qs) && decide (Function.Injective c.idx)) := by
  simp [offlineFinish]

omit [AddGroup Z] in
/-- The mismatch branch vanishes unless both checks accept and extraction decodes. -/
theorem run₂_offlineFinish_reject [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (R : QuantumRuntime (mixedExtSpec k X Y Cm Z))
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool)
    (hr : ¬ ∃ tdm, r = (true, some tdm, true)) :
    (R.run₂ .instruments (offlineFinish VC (Z := Z) hk qs c B r)).branch true = 0 := by
  rcases r with ⟨a, v, b⟩
  cases v with
  | none =>
    simp only [offlineFinish, QuantumRuntime.run₂_pure,
      SubInstrument.branch_pure_of_ne (by decide : true ≠ false)]
  | some tdm =>
    have hb : a = false ∨ b = false := by cases a <;> cases b <;> simp_all
    ext ρ : 1
    rw [offlineFinish, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
    simp only [LinearMap.zero_apply]
    refine (tsum_congr fun pf ↦ ?_).trans tsum_zero
    rcases hb with rfl | rfl <;>
      simp [QuantumRuntime.run₂_pure]

omit [AddGroup Z] in
/-- The finishing mismatch branch vanishes when the claim exceeds its opening budget. -/
theorem run₂_offlineFinish_over_budget [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (R : QuantumRuntime (mixedExtSpec k X Y Cm Z))
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :
    (R.run₂ .instruments (offlineFinish VC (Z := Z) hk qs c B r)).branch true = 0 := by
  rcases r with ⟨a, v, b⟩
  cases v with
  | none =>
    simp only [offlineFinish, QuantumRuntime.run₂_pure,
      SubInstrument.branch_pure_of_ne (by decide : true ≠ false)]
  | some tdm =>
    ext ρ : 1
    rw [offlineFinish, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
    simp only [LinearMap.zero_apply]
    refine (tsum_congr fun pf ↦ ?_).trans tsum_zero
    simp [hq, QuantumRuntime.run₂_pure]

/-- The actual P4 challenger is the retained prefix followed by its opening/mismatch decision.
This is an equality of programs, including rejected checks and decoding failure. -/
theorem offlineChallenger_eq_bind_offlineChecks [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    offlineChallenger VC code hk qs c B =
      QuantumComp₂.bind (offlineChecks VC code hk c B)
        (offlineFinish VC (Z := Z) hk qs c B) := by
  simp only [offlineChallenger, offlineChecks, QuantumComp₂.map,
    QuantumComp₂.bind_assoc]
  congr 1
  funext b₁
  erw [QuantumComp₂.bind_assoc, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]
  congr 1
  funext tdm
  erw [QuantumComp₂.bind_assoc]
  congr 1
  funext b₂
  erw [QuantumComp₂.pure_bind]
  cases tdm <;> rfl

/-- The actual P4 challenger instrument retaining its check/extraction transcript alongside
the final mismatch-event bit. Forgetting the transcript recovers `offlineChallenger`. -/
noncomputable def offlineInstrument [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    QComp (mixedExtSpec k X Y Cm Z) B B
      ((Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) × Bool) :=
  (offlineChecks VC code hk c B).bind fun r ↦
    (offlineFinish VC (Z := Z) hk qs c B r).map fun b ↦ (r, b)

/-- Forgetting the retained transcript gives exactly the original P4 challenger. -/
theorem offlineInstrument_map_snd [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    (offlineInstrument VC code hk qs c B).map Prod.snd =
      offlineChallenger VC code hk qs c B := by
  rw [offlineInstrument, QuantumRuntime.bind_record_map_snd,
    offlineChallenger_eq_bind_offlineChecks VC code]

/-- Retaining the prefix outcomes identifies each branch with the three executed branches. -/
theorem run₂_offlineChecks (R : QuantumRuntime (mixedExtSpec k X Y Cm Z))
    (hk : 1 ≤ k) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (b₁ b₂ : Bool) (tdm : Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk))) :
    (R.run₂ .instruments (offlineChecks VC code hk c B)).branch (b₁, tdm, b₂) =
      ((R.run₂ .instruments (QComp.allIn c.Wᶜ fun i ↦
        checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i))).branch b₂ ∘ₗ
        (R.run₂ .instruments (QuantumComp.liftOrdinary
          (extractQuery code B (TpIC.full hk c.idx c.cm)))).branch tdm) ∘ₗ
      (R.run₂ .instruments (QComp.allIn c.W fun i ↦
        checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i))).branch b₁ := by
  let checks := fun W ↦ QComp.allIn W fun i ↦
    checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)
  let extract : QComp (mixedExtSpec k X Y Cm Z) B B _ :=
    QuantumComp.liftOrdinary (extractQuery code B (TpIC.full hk c.idx c.cm))
  have h₁ := R.run₂_bind_record .instruments (checks c.W)
    (fun _ ↦ extract.bind fun d ↦ (checks c.Wᶜ).map (fun b ↦ (d, b))) b₁ (tdm, b₂)
  have h₂ := R.run₂_bind_record .instruments extract (fun _ ↦ checks c.Wᶜ) tdm b₂
  exact h₁.trans (congrArg (fun F ↦ F ∘ₗ (R.run₂ .instruments (checks c.W)).branch b₁) h₂)

/-- The retained event branch executes the finishing program on its particular transcript. -/
theorem run₂_offlineInstrument [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (R : QuantumRuntime (mixedExtSpec k X Y Cm Z)) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) (b : Bool) :
    (R.run₂ .instruments (offlineInstrument VC code hk qs c B)).branch (r, b) =
      (R.run₂ .instruments (offlineFinish VC hk qs c B r)).branch b ∘ₗ
        (R.run₂ .instruments (offlineChecks VC code hk c B)).branch r :=
  R.run₂_bind_record .instruments _ _ r b

/-- The mismatch probability retains every accepting check/extract/check outcome and its
own finishing instrument. No projector description of the checked batches is assumed. -/
theorem offlineChallenger_weight_eq_retained [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (R : QuantumRuntime (mixedExtSpec k X Y Cm Z)) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) (ρ : SubState (B × R.D)) :
    (R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true} =
      ∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
        (offlineInstrument VC code hk qs c B)).branch ((true, some tdm, true), true))
          ρ.matrix).trace.re := by
  classical
  rw [offlineChallenger_eq_bind_offlineChecks VC code, QuantumRuntime.run₂_bind]
  erw [DSubInstrument.outcomeMeasure_bind,
    Measure.sum_apply _ (measurableSet_singleton true)]
  simp only [DSubInstrument.outcomeMeasure_apply_singleton]
  let f := fun r ↦ ENNReal.ofReal (((R.run₂ .instruments
    (offlineFinish VC (Z := Z) hk qs c B r)).branch true)
      (((R.run₂ .instruments (offlineChecks VC code hk c B)).branch r) ρ.matrix)).trace.re
  let g := fun tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk) ↦ (true, some tdm, true)
  have hg : Function.Injective g := by
    intro a b h
    exact Option.some.inj (congrArg (fun r ↦ r.2.1) h)
  have hs : Function.support f ⊆ Set.range g := by
    intro r hr
    by_contra hn
    have hz := run₂_offlineFinish_reject VC R hk qs c B r (by
      simpa only [Set.mem_range, g, eq_comm] using hn)
    exact hr (by simp [f, hz])
  change (∑' r, f r) = _
  rw [← hg.tsum_eq hs]
  apply tsum_congr
  intro tdm
  rw [run₂_offlineInstrument]
  rfl

/-- A rejected retained transcript has zero mismatch-event branch. -/
theorem run₂_offlineInstrument_reject [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (R : QuantumRuntime (mixedExtSpec k X Y Cm Z)) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool)
    (hr : ¬ ∃ tdm, r = (true, some tdm, true)) :
    (R.run₂ .instruments (offlineInstrument VC code hk qs c B)).branch (r, true) = 0 := by
  rw [run₂_offlineInstrument, run₂_offlineFinish_reject VC R hk qs c B r hr]
  exact LinearMap.zero_comp _

/-- A retained mismatch branch vanishes when the claim exceeds its opening budget. -/
theorem run₂_offlineInstrument_over_budget [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (R : QuantumRuntime (mixedExtSpec k X Y Cm Z)) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :
    (R.run₂ .instruments (offlineInstrument VC code hk qs c B)).branch (r, true) = 0 := by
  rw [run₂_offlineInstrument, run₂_offlineFinish_over_budget VC R hk qs c B hq r]
  exact LinearMap.zero_comp _

/-- Claims exceeding the opening budget have zero mismatch probability. -/
theorem offlineChallenger_over_budget [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (R : QuantumRuntime (mixedExtSpec k X Y Cm Z)) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) (ρ : SubState (B × R.D))
    (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs) :
    (R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true} = 0 := by
  rw [offlineChallenger_weight_eq_retained VC code R hk qs c B ρ]
  simp only [run₂_offlineInstrument_over_budget VC code R hk qs c B hq,
    LinearMap.zero_apply, trace_zero, Complex.zero_re, ENNReal.ofReal_zero, tsum_zero]

variable (E : VCOracle k X Y) (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S)
  (code : TpDCode k (DmOf ℓ Msg Td) Z)

/-- **P3, multi-extraction correctness** (ePrint 2025/2166, Def 7.3, p. 51): against every
`t`-query adversary querying `EO^(Ext)` whose oracle masses sum to at most `wVC` and whose
extraction mass is at most `wME`, and every `n ≤ k`, the P3 challenger reports its event with
probability at most `κ t wVC wME n`. Here `wVC` is ordinary adversary mass; the checked
challenger's reads are outside the prefix and its mass bounds. -/
@[expose]
def ExtractionCorrect (κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (hk : 1 ≤ k) (t n : ℕ) (wVC wME : ℝ≥0∞) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) W A)
    (claim : ∀ u, W u → ExtractClaim k Cm) (ρ : SubState A),
    n ≤ k → x.IsQueryBound (fun _ ↦ t) →
    ∑ i : Fin k, (E.withExtract ME code).totalMass .instruments x
      (ρ.matrix ⊗ₖ E.init.matrix) (.inl i) ≤ wVC →
    (E.withExtract ME code).totalMass .instruments x (ρ.matrix ⊗ₖ E.init.matrix) (.inr ()) ≤
      wME →
    (E.mixedExtractRuntime ME code).evalDistMap .instruments
      (experiment x.liftOrdinary fun u y ↦ extractChallenger VC code hk n (claim u y) u) ρ Sigma.snd
        {true} ≤ κ t wVC wME n

/-- **P4, offline extractability** (ePrint 2025/2166, Def 7.3, p. 51): against every
`t`-query adversary querying `EO^(Ext)` with the mass bounds of P3, the P4 challenger reports
its event with probability at most `κ t wVC wME qs`. The malicious prefix has only ordinary
oracle/extraction access. Its `wVC` excludes the checked challenger's reads. -/
@[expose]
def OfflineExtractable [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (hk : 1 ≤ k) (t qs : ℕ) (wVC wME : ℝ≥0∞) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) W A)
    (claim : ∀ u, W u → OpeningClaim k Cm Msg ℓ Pf) (ρ : SubState A),
    x.IsQueryBound (fun _ ↦ t) →
    ∑ i : Fin k, (E.withExtract ME code).totalMass .instruments x
      (ρ.matrix ⊗ₖ E.init.matrix) (.inl i) ≤ wVC →
    (E.withExtract ME code).totalMass .instruments x (ρ.matrix ⊗ₖ E.init.matrix) (.inr ()) ≤
      wME →
    (E.mixedExtractRuntime ME code).evalDistMap .instruments
      (experiment x.liftOrdinary fun u y ↦ offlineChallenger VC code hk qs (claim u y) u)
      ρ Sigma.snd
        {true} ≤ κ t wVC wME qs

variable {VC E ME code}

/-- P3 is monotone in the error. -/
theorem ExtractionCorrect.mono {κ κ' : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞}
    (h : ExtractionCorrect.{v, w} VC E ME code κ) (hκ : κ ≤ κ') :
    ExtractionCorrect.{v, w} VC E ME code κ' :=
  fun hk t n wVC wME _ _ x claim ρ hn hx h₁ h₂ ↦
    (h hk t n wVC wME x claim ρ hn hx h₁ h₂).trans (hκ t wVC wME n)

/-- P4 is monotone in the error. -/
theorem OfflineExtractable.mono [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    {κ κ' : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞}
    (h : OfflineExtractable.{v, w} VC E ME code κ) (hκ : κ ≤ κ') :
    OfflineExtractable.{v, w} VC E ME code κ' :=
  fun hk t qs wVC wME _ _ x claim ρ hx h₁ h₂ ↦
    (h hk t qs wVC wME x claim ρ hx h₁ h₂).trans (hκ t wVC wME qs)

/-- **P3 for adversaries with classically named ports.** An adversary that names the port of each
call classically, makes at most `b i` calls of port `i`, and has per-port query masses within
`wVC` and `wME`, makes the P3 challenger report its event with probability at most
`κ (∑ i, b i) wVC wME n`. -/
theorem ExtractionCorrect.of_classicalPorts {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞}
    (h : ExtractionCorrect.{v, w} VC E ME code κ) (hk : 1 ≤ k) {n : ℕ} (hn : n ≤ k) {wVC wME : ℝ≥0∞}
    {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec (Fin k ⊕ Unit) (extIn k X Y Cm Z)) W A)
    (claim : ∀ u, W u → ExtractClaim k Cm) (ρ : SubState A) {b : Fin k ⊕ Unit → ℕ}
    (hx : x.IsQueryBound b)
    (h₁ : ∑ i : Fin k, (E.withExtract ME code).toRuntime.queryMass .instruments x
      (ρ.matrix ⊗ₖ E.init.matrix) (.inl i) ≤ wVC)
    (h₂ : (E.withExtract ME code).toRuntime.queryMass .instruments x
      (ρ.matrix ⊗ₖ E.init.matrix) (.inr ()) ≤ wME) :
    (E.mixedExtractRuntime ME code).evalDistMap .instruments
      (experiment x.toCoherent.liftOrdinary fun u y ↦
        extractChallenger VC code hk n (claim u y) u) ρ
        Sigma.snd {true} ≤ κ (∑ i, b i) wVC wME n := by
  refine h hk _ n wVC wME x.toCoherent claim ρ hn (QuantumComp.isQueryBound_toCoherent hx)
    ?_ ?_
  · simpa only [EmulatedOracle.totalMass_toCoherent] using h₁
  · simpa only [EmulatedOracle.totalMass_toCoherent] using h₂

/-- **P4 for adversaries with classically named ports**, with per-port query masses. -/
theorem OfflineExtractable.of_classicalPorts [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞}
    (h : OfflineExtractable.{v, w} VC E ME code κ) (hk : 1 ≤ k) {qs : ℕ} {wVC wME : ℝ≥0∞}
    {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec (Fin k ⊕ Unit) (extIn k X Y Cm Z)) W A)
    (claim : ∀ u, W u → OpeningClaim k Cm Msg ℓ Pf) (ρ : SubState A) {b : Fin k ⊕ Unit → ℕ}
    (hx : x.IsQueryBound b)
    (h₁ : ∑ i : Fin k, (E.withExtract ME code).toRuntime.queryMass .instruments x
      (ρ.matrix ⊗ₖ E.init.matrix) (.inl i) ≤ wVC)
    (h₂ : (E.withExtract ME code).toRuntime.queryMass .instruments x
      (ρ.matrix ⊗ₖ E.init.matrix) (.inr ()) ≤ wME) :
    (E.mixedExtractRuntime ME code).evalDistMap .instruments
      (experiment x.toCoherent.liftOrdinary fun u y ↦
        offlineChallenger VC code hk qs (claim u y) u) ρ
        Sigma.snd {true} ≤ κ (∑ i, b i) wVC wME qs := by
  refine h hk _ qs wVC wME x.toCoherent claim ρ (QuantumComp.isQueryBound_toCoherent hx) ?_ ?_
  · simpa only [EmulatedOracle.totalMass_toCoherent] using h₁
  · simpa only [EmulatedOracle.totalMass_toCoherent] using h₂

end challengers

/-! ## P5: online indistinguishability -/

section online

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)

/-- **P5, online indistinguishability** (ePrint 2025/2166, Def 7.3, p. 51), in square-root
form: for every unitary `U` on `Yr × Cell` and every `t`-query adversary querying `EO^(Record)`
whose oracle, extraction and record masses in the world `Record(U)` are at most `wVC`, `wME` and
`wRec`, the probabilities `p₁` and `p₂` of observing `true` in the worlds `Record(U)` and
`Record(MultiExtract, U)` satisfy `√p₁ ≤ √p₂ + √κ` and `√p₂ ≤ √p₁ + √κ`, that is,
`(√p₁ − √p₂)² ≤ κ t wVC wME wRec`. Both worlds start with every cell of the recording register
at `bot`. The trusted verifier may read inside this program. Its reads contribute their full
input trace to `wVC`, alongside selected ordinary oracle mass; `wME` and `wRec` count only their
ordinary coherent indices. All three masses are measured in the unsplit `Record(U)` world. -/
@[expose]
def OnlineIndistinguishable (κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∀ (Yr Cell : Type) [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell] (bot : Cell)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    (t : ℕ) (wVC wME wRec : ℝ≥0∞) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (mixedRecSpec k X Y Cm Z Yr) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A),
    x.IsTotalQueryBound t →
    (E.mixedRecordRuntime ME code bot U hU).totalWeight .instruments
      (E.recordVCWeight ME code bot U hU) x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) ≤ wVC →
    (E.mixedRecordRuntime ME code bot U hU).totalWeight .instruments
      (E.recordIndexWeight ME code bot U hU (.inl (.inr ()))) x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) ≤ wME →
    (E.mixedRecordRuntime ME code bot U hU).totalWeight .instruments
      (E.recordIndexWeight ME code bot U hU (.inr ())) x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) ≤ wRec →
    (E.mixedRecordRuntime ME code bot U hU).evalDistMap .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.mixedRecordMERuntime ME code bot U hU).evalDistMap .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) + κ t wVC wME wRec ^ (2⁻¹ : ℝ) ∧
    (E.mixedRecordMERuntime ME code bot U hU).evalDistMap .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.mixedRecordRuntime ME code bot U hU).evalDistMap .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) + κ t wVC wME wRec ^ (2⁻¹ : ℝ)

variable {E ME code}

/-- P5 is monotone in the error. -/
theorem OnlineIndistinguishable.mono {κ κ' : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    (h : OnlineIndistinguishable.{v, w} E ME code κ) (hκ : κ ≤ κ') :
    OnlineIndistinguishable.{v, w} E ME code κ' := by
  intro Yr Cell _ _ _ _ bot U hU t wVC wME wRec A W x f ρ hx h₁ h₂ h₃
  have hle : κ t wVC wME wRec ^ (2⁻¹ : ℝ) ≤ κ' t wVC wME wRec ^ (2⁻¹ : ℝ) :=
    ENNReal.rpow_le_rpow (hκ t wVC wME wRec) (by norm_num)
  obtain ⟨h₄, h₅⟩ := h Yr Cell bot U hU t wVC wME wRec x f ρ hx h₁ h₂ h₃
  exact ⟨h₄.trans (add_le_add le_rfl hle), h₅.trans (add_le_add le_rfl hle)⟩

end online

/-! ## Multi-extractability -/

/-- The error functions of Def 7.3 (ePrint 2025/2166, pp. 50–51). The security parameter is
not modelled, and `σ`, `ℓmax` and `k` are fixed by the family. -/
structure MEErrors where
  /-- `κsim`, a function of the query bound `t`. -/
  sim : ℕ → ℝ≥0∞
  /-- `κcom`, a function of the query bound `t`. -/
  com : ℕ → ℝ≥0∞
  /-- `κextract`, a function of `t`, `wVC`, `wMultiExtract` and `n`. -/
  extract : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞
  /-- `κoffline`, a function of `t`, `wVC`, `wMultiExtract` and `qs`. -/
  offline : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞
  /-- `κonline`, a function of `t`, `wVC`, `wMultiExtract` and `wRecord`. -/
  online : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞

namespace MEErrors

/-- Errors are compared pointwise. -/
instance : LE MEErrors :=
  ⟨fun κ κ' ↦ κ.sim ≤ κ'.sim ∧ κ.com ≤ κ'.com ∧ κ.extract ≤ κ'.extract ∧
    κ.offline ≤ κ'.offline ∧ κ.online ≤ κ'.online⟩

/-- The pointwise order on errors, unfolded. -/
theorem le_def {κ κ' : MEErrors} : κ ≤ κ' ↔ κ.sim ≤ κ'.sim ∧ κ.com ≤ κ'.com ∧
    κ.extract ≤ κ'.extract ∧ κ.offline ≤ κ'.offline ∧ κ.online ≤ κ'.online :=
  Iff.rfl

/-- **Monotonicity of the errors** (ePrint 2025/2166, p. 51): `κsim`, `κcom`, `κoffline` and
`κonline` are monotone in all their arguments. It is a hypothesis to be assumed where needed, not
part of `Quantum.IsMultiExtractableWith`. -/
@[expose]
def Monotone (κ : MEErrors) : Prop :=
  _root_.Monotone κ.sim ∧ _root_.Monotone κ.com ∧
    _root_.Monotone (fun p : ℕ × ℝ≥0∞ × ℝ≥0∞ × ℕ ↦ κ.offline p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
    _root_.Monotone (fun p : ℕ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ ↦ κ.online p.1 p.2.1 p.2.2.1 p.2.2.2)

end MEErrors

section bundle

variable {k : ℕ} {X Y Msg Cm : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Msg] [DecidableEq Msg] [Fintype Cm] [DecidableEq Cm] {ℓ : Fin k → ℕ}
  {Td Pf : Fin k → Type} [∀ i, Fintype (Td i)] [∀ i, DecidableEq (Td i)]
  [∀ i, DecidableEq (Pf i)] (VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i))

/-- **Def 7.3 for a given oracle, extractor and encoding** (ePrint 2025/2166, pp. 50–51): the
extractor is admissible (Def 7.1, repaired as in `Quantum.MultiExtractor.Admissible`) with
`⊥ = (⊥^ℓ_i, tdBot i)`, and P1–P5 hold with the errors `κ`. -/
structure IsMultiExtractableWith {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (E : VCOracle k X Y) (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (tdBot : ∀ i, Td i) {Ω : Type*} (p : StdSimplex ℝ Ω)
    (Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)) (κ : MEErrors) : Prop where
  /-- Def 7.1: the extractor is admissible. -/
  admissible : ME.Admissible fun i ↦ ((fun _ ↦ none), tdBot i)
  /-- P1: the oracle simulates the reference model. -/
  sim : Simulates.{v, w} p Ref E κ.sim
  /-- P2, first half: the oracle unitaries commute. -/
  commute : OraclesCommute E
  /-- P2, second half: the oracles almost commute with the extractor. -/
  com : ComBound.{v, w} E ME code κ.com
  /-- P3: multi-extraction correctness. -/
  extract : ExtractionCorrect.{v, w} VC E ME code κ.extract
  /-- P4: offline extractability. -/
  offline : OfflineExtractable.{v, w} VC E ME code κ.offline
  /-- P5: online indistinguishability. -/
  online : OnlineIndistinguishable.{v, w} E ME code κ.online

/-- **Def 7.3, post-quantum multi-extractable vector commitments** (ePrint 2025/2166,
pp. 50–51): there are an emulated oracle, a multi-extractor and an encoding of decommitment
tuples for which `Quantum.IsMultiExtractableWith` holds. The existential is the paper's
definition. -/
@[expose]
def IsMultiExtractable (tdBot : ∀ i, Td i) {Ω : Type*} (p : StdSimplex ℝ Ω)
    (Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)) (κ : MEErrors) : Prop :=
  ∃ (E : VCOracle k X Y) (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S) (Z : Type)
    (_ : Fintype Z) (_ : DecidableEq Z) (_ : AddGroup Z) (code : TpDCode k (DmOf ℓ Msg Td) Z),
    IsMultiExtractableWith.{v, w} VC E ME code tdBot p Ref κ

variable {VC}

/-- Def 7.3 for a given oracle is monotone in the errors. -/
theorem IsMultiExtractableWith.mono {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    {E : VCOracle k X Y} {ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S}
    {code : TpDCode k (DmOf ℓ Msg Td) Z} {tdBot : ∀ i, Td i} {Ω : Type*} {p : StdSimplex ℝ Ω}
    {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)} {κ κ' : MEErrors}
    (h : IsMultiExtractableWith.{v, w} VC E ME code tdBot p Ref κ) (hκ : κ ≤ κ') :
    IsMultiExtractableWith.{v, w} VC E ME code tdBot p Ref κ' where
  admissible := h.admissible
  sim := h.sim.mono hκ.1
  commute := h.commute
  com := h.com.mono hκ.2.1
  extract := h.extract.mono hκ.2.2.1
  offline := h.offline.mono hκ.2.2.2.1
  online := h.online.mono hκ.2.2.2.2

/-- Def 7.3 is monotone in the errors. -/
theorem IsMultiExtractable.mono {tdBot : ∀ i, Td i} {Ω : Type*} {p : StdSimplex ℝ Ω}
    {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)} {κ κ' : MEErrors}
    (h : IsMultiExtractable.{v, w} VC tdBot p Ref κ) (hκ : κ ≤ κ') :
    IsMultiExtractable.{v, w} VC tdBot p Ref κ' :=
  let ⟨E, ME, Z, i₁, i₂, i₃, code, hE⟩ := h
  ⟨E, ME, Z, i₁, i₂, i₃, code, hE.mono hκ⟩

end bundle

end Quantum
