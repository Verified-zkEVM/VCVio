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
  general initial substate `ρ`, against the coherent single-port view of the oracle
  (`Quantum.EmulatedOracle.coherent`, p. 28). The paper's start state `|0^ℓ⟩` (p. 50) is
  the case of a pure `ρ`. Adversaries with classically named ports translate to the coherent view
  through `Quantum.QuantumComp.toCoherent`, and P1, P3, P4 and P5 have corollaries for them
  (`…_of_classicalPorts`).
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
* **"t-query"** (p. 50) is `x.IsQueryBound fun _ ↦ t` on the coherent port: every call,
  extraction and record calls included.
* **Masses** `TotalMass(A, i, EO')` (p. 51) are
  `Quantum.EmulatedOracle.totalMass` of the adversary alone, never of the challenger.
* **Challengers** run on the adversary's final register, after it, as one program
  (`Quantum.experiment`). `Open` and `Check` of the general `VectorCommitment` run inside the
  experiment through `OracleComp.toQuantumAt`: coins are uniform coins
  (`Quantum.QComp.coinImpl`), and oracle queries of `Check^{O_j}` are classical calls of port
  `j` on the basis input `|t, 0⟩` (`Quantum.oracleCall`). Extraction is a classical call of the
  extraction port on `|tic, 0⟩` followed by decoding (`Quantum.extractQuery`); its branches are
  the projectors onto the fibres of `MultiExtract(tic, ·)` (`Quantum.run₂_extractQuery_branch`).

## Departures from the paper

* P1 bounds both differences, where the paper writes one (p. 50). The paper's distribution
  `D(λ)` (p. 50) is a finitely supported distribution with real weights (Mathlib's
  `Convexity.StdSimplex ℝ Ω`) over a family of runtimes on the coherent signature
  (`Quantum.mixedLawWith`). The random-oracle model is the uniform distribution
  (`Quantum.uniformWeights`) over the family of `Quantum.romVCOracle`, for which P1 reads as a
  bound against `Quantum.sampledLawWith` (`Quantum.simulates_uniformWeights_iff`).
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
* `Quantum.Simulates.of_classicalPorts`, `Quantum.ExtractionCorrect.of_classicalPorts`,
  `Quantum.OfflineExtractable.of_classicalPorts`,
  `Quantum.OnlineIndistinguishable.of_classicalPorts`.
-/

public section

open Matrix MeasureTheory OracleSpec Convexity
open scoped ENNReal Kronecker

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

end experiment

/-! ## P1: simulation indistinguishability -/

section mixture

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w}
  {A : QReg} {Ω : Type*} {β : Type*} [MeasurableSpace β]

/-- **The law against a finite mixture of runtimes.** For a finitely supported distribution `p`
on `Ω` (Mathlib's `Convexity.StdSimplex ℝ Ω`: real weights `p.weights ω ≥ 0` with finite support
summing to `1`) and a family of runtimes `R`, the law of an observation of the leaf reached by
`x` when the oracle is realized by `R ω` with probability `p.weights ω`: the mixture
`∑ ω, p.weights ω • (R ω).outcomeLawWith I x ρ (f ω)`. The observation sees the sampled value. -/
@[expose]
noncomputable def mixedLawWith (p : StdSimplex ℝ Ω) (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    Measure β :=
  p.weights.sum fun ω r ↦ ENNReal.ofReal r • (R ω).outcomeLawWith I x ρ (f ω)

/-- The mixed law of a set is the weighted sum of its measures under the runs. -/
theorem mixedLawWith_apply (p : StdSimplex ℝ Ω) (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) (s : Set β) :
    mixedLawWith p R I x ρ f s =
      p.weights.sum fun ω r ↦ ENNReal.ofReal r * (R ω).outcomeLawWith I x ρ (f ω) s := by
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
is `Quantum.sampledLawWith`, the law of `R ω` for `ω` drawn with VCVio's `$ᵗ`. -/
theorem mixedLawWith_uniformWeights {Ω : Type} [SampleableType Ω] (R : Ω → QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    mixedLawWith (uniformWeights Ω) R I x ρ f = sampledLawWith R I x ρ f := by
  let := Fintype.ofFinite Ω
  rw [sampledLawWith_eq_sum, mixedLawWith, Finsupp.sum_fintype _ _ fun _ ↦ by simp,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [uniformWeights_weights_apply, Nat.card_eq_fintype_card,
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_natCast]

end mixture

section simulation

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **P1, simulation indistinguishability** (ePrint 2025/2166, Def 7.3, p. 50): against
every `t`-query adversary and every observation, the probability of observing `true` against the
coherent emulated oracle and against the reference model differ by at most `κsim t`, in both
directions. The reference model is the paper's `D(λ)` (p. 50): a finitely supported distribution
`p` over a family `Ref` of runtimes on the coherent signature (`Quantum.mixedLawWith`). The
random-oracle model is the uniform distribution (`Quantum.uniformWeights`) over the family of
`Quantum.romVCOracle`; see `Quantum.simulates_uniformWeights_iff`. -/
@[expose]
def Simulates {Ω : Type*} (p : StdSimplex ℝ Ω) (Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y)))
    (E : VCOracle k X Y) (κsim : ℕ → ℝ≥0∞) : Prop :=
  ∀ (t : ℕ) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (oIn k X Y)) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A), x.IsQueryBound (fun _ ↦ t) →
    E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} ≤
        mixedLawWith p Ref .instruments x ρ (fun _ ↦ f) {true} + κsim t ∧
      mixedLawWith p Ref .instruments x ρ (fun _ ↦ f) {true} ≤
        E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} + κsim t

variable {Ω : Type*} {p : StdSimplex ℝ Ω} {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))}
  {E : VCOracle k X Y}

/-- P1 is monotone in the error. -/
theorem Simulates.mono {κ κ' : ℕ → ℝ≥0∞} (h : Simulates.{v, w} p Ref E κ) (hκ : κ ≤ κ') :
    Simulates.{v, w} p Ref E κ' := fun t _ _ x f ρ hx ↦
  ⟨(h t x f ρ hx).1.trans (add_le_add le_rfl (hκ t)),
    (h t x f ρ hx).2.trans (add_le_add le_rfl (hκ t))⟩

/-- **P1 against a uniformly sampled reference model**, such as the random-oracle model: the
mixture is `Quantum.sampledLawWith`. -/
theorem simulates_uniformWeights_iff {Ω : Type} [SampleableType Ω]
    {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))} {κ : ℕ → ℝ≥0∞} :
    Simulates.{v, w} (uniformWeights Ω) Ref E κ ↔
      ∀ (t : ℕ) {A : QReg} {W : QReg → Type w}
        (x : QuantumComp LocalSig.instruments.{v} (cohSpec (oIn k X Y)) W A)
        (f : (Σ u, W u) → Bool) (ρ : SubState A), x.IsQueryBound (fun _ ↦ t) →
        E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} ≤
            sampledLawWith Ref .instruments x ρ (fun _ ↦ f) {true} + κ t ∧
          sampledLawWith Ref .instruments x ρ (fun _ ↦ f) {true} ≤
            E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} + κ t := by
  simp only [Simulates, mixedLawWith_uniformWeights]

/-- **P1 from its uniform form**: bounds against `Quantum.sampledLawWith` give P1 against the
uniform distribution. -/
theorem Simulates.ofUniform {Ω : Type} [SampleableType Ω]
    {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))} {κ : ℕ → ℝ≥0∞}
    (h : ∀ (t : ℕ) {A : QReg} {W : QReg → Type w}
      (x : QuantumComp LocalSig.instruments.{v} (cohSpec (oIn k X Y)) W A)
      (f : (Σ u, W u) → Bool) (ρ : SubState A), x.IsQueryBound (fun _ ↦ t) →
      E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} ≤
          sampledLawWith Ref .instruments x ρ (fun _ ↦ f) {true} + κ t ∧
        sampledLawWith Ref .instruments x ρ (fun _ ↦ f) {true} ≤
          E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} + κ t) :
    Simulates.{v, w} (uniformWeights Ω) Ref E κ :=
  simulates_uniformWeights_iff.mpr h

/-- **P1 for adversaries with classically named ports.** When the reference model is a family of
emulated oracles, an adversary that names the port of each call classically and makes at most
`b i` calls of port `i` sees the oracle and the model within `κsim (∑ i, b i)`. -/
theorem Simulates.of_classicalPorts {F : Ω → VCOracle k X Y} {κ : ℕ → ℝ≥0∞}
    (h : Simulates.{v, w} p (fun ω ↦ (F ω).coherent.toRuntime) E κ) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec (Fin k) (oIn k X Y)) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A) {b : Fin k → ℕ} (hx : x.IsQueryBound b) :
    E.toRuntime.outcomeLawWith .instruments x ρ f {true} ≤
        mixedLawWith p (fun ω ↦ (F ω).toRuntime) .instruments x ρ (fun _ ↦ f) {true} +
          κ (∑ i, b i) ∧
      mixedLawWith p (fun ω ↦ (F ω).toRuntime) .instruments x ρ (fun _ ↦ f) {true} ≤
        E.toRuntime.outcomeLawWith .instruments x ρ f {true} + κ (∑ i, b i) := by
  have h' := h (∑ i, b i) x.toCoherent f ρ (QuantumComp.isQueryBound_toCoherent hx)
  simp only [mixedLawWith, EmulatedOracle.outcomeLawWith_toCoherent] at h'
  simpa only [mixedLawWith] using h'

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
    (x : QuantumComp₂ LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) A
      (ComOut k X Y Cm Z Env) α) (ρ : SubState A) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal (comDefect E ME code Env i *
    (show Matrix (ComOut k X Y Cm Z Env × E.S) (ComOut k X Y Cm Z Env × E.S) ℂ from
      ((E.withExtract ME code).coherent.toRuntime.jointPost₂ .instruments x ρ a).matrix) *
      (comDefect E ME code Env i)ᴴ).trace.re

/-- **Second half of P2** (ePrint 2025/2166, Def 7.3, p. 50): against every `t`-query
adversary querying `EO^(Ext)`, the commutation distance of every oracle `i` with the extractor is
at most `κcom t`. -/
@[expose]
def ComBound (κcom : ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : Fin k) (t : ℕ) {A Env : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) A
      (ComOut k X Y Cm Z Env) α) (ρ : SubState A),
    x.IsQueryBound (fun _ ↦ t) → comError E ME code i x ρ ≤ κcom t

variable {E ME code}

/-- The commutation bound is monotone in the error. -/
theorem ComBound.mono {κ κ' : ℕ → ℝ≥0∞} (h : ComBound.{v, w} E ME code κ) (hκ : κ ≤ κ') :
    ComBound.{v, w} E ME code κ' := fun i t _ _ _ x ρ hx ↦ (h i t x ρ hx).trans (hκ t)

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
    {x : QuantumComp₂ LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) A
      (ComOut k X Y Cm Z Env) α} (a₀ : α)
    (V : Matrix (ComOut k X Y Cm Z Env × E.S) (A × E.S) ℂ)
    (hx₀ : ((E.withExtract ME code).coherent.toRuntime.run₂ .instruments x).branch a₀ =
      MatrixMap.conj V)
    (hx : ∀ a ≠ a₀, ((E.withExtract ME code).coherent.toRuntime.run₂ .instruments x).branch a = 0)
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
    {x : QuantumComp₂ LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) A
      (ComOut k X Y Cm Z Env) α} (a₀ : α)
    (V : Matrix (ComOut k X Y Cm Z Env × E.S) (A × E.S) ℂ)
    (hx₀ : ((E.withExtract ME code).coherent.toRuntime.run₂ .instruments x).branch a₀ =
      MatrixMap.conj V)
    (hx : ∀ a ≠ a₀, ((E.withExtract ME code).coherent.toRuntime.run₂ .instruments x).branch a = 0)
    {ρ : SubState A} (v : A × E.S → ℂ)
    (hv : ρ.matrix ⊗ₖ E.init.matrix = vecMulVec v (star v)) :
    comError E ME code i x ρ =
      ENNReal.ofReal (∑ b, ‖((comDefect E ME code Env i * V) *ᵥ v) b‖ ^ 2) := by
  rw [comError_eq_of_branch E ME code a₀ V hx₀ hx, hv, ← trace_mul_vecMulVec_mul_conjTranspose_re,
    conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end commute

/-! ## Classical calls from the challenger -/

section calls

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}

/-- The answer register `Y` of a reading of the coherent register of `EO^(Ext)` on an oracle
port. Readings on the extraction port, which a call of an oracle port does not produce, give
`0`. -/
@[expose]
def readY [Zero Y] : (Σ i, extIn k X Y Cm Z i) → Y
  | ⟨.inl _, m⟩ => (m : X × Y).2
  | ⟨.inr _, _⟩ => 0

/-- **A classical query of oracle `j`** at `t` from inside an experiment (the queries of
`Check^{O_j}`, ePrint 2025/2166, p. 51): call the coherent port on the basis input
`|j, t, 0⟩`, measure the port register, and return the answer `y`. -/
@[expose]
noncomputable def oracleCall [Zero Y] (B : QReg) (j : Fin k) (t : X) :
    QComp (cohSpec (extIn k X Y Cm Z)) B B Y :=
  QComp.callBasis (spec := cohSpec (extIn k X Y Cm Z)) () B
    (⟨.inl j, ((t, 0) : X × Y)⟩ : Σ i, extIn k X Y Cm Z i) fun o _ ↦ readY o

/-- The queries of a vector commitment's `Check^{O_j}` answered from inside an experiment: coins
by uniform coins, oracle queries by classical queries of oracle `j`. -/
@[expose]
noncomputable def oracleImpl [Zero Y] (B : QReg) (j : Fin k) :
    QueryImpl (unifSpec + (X →ₒ Y)) (QComp (cohSpec (extIn k X Y Cm Z)) B B) :=
  QComp.coinImpl (cohSpec (extIn k X Y Cm Z)) B +
    (fun t ↦ oracleCall B j t : QueryImpl (X →ₒ Y) (QComp (cohSpec (extIn k X Y Cm Z)) B B))

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

/-- The projector onto the private states `s` with `MultiExtract(tic, s) = tdm` (the paper's
`Π_tdm`, p. 59). -/
@[expose]
noncomputable def extractProj {S : Type*} [DecidableEq S] [∀ i, DecidableEq (Dm i)]
    (ME : MultiExtractor k Cm Dm S) (tic : TpIC k Cm) (tdm : TpDLen k Dm tic.1) :
    Matrix S S ℂ :=
  diagonal fun s ↦ if ME.extract tic s = tdm then 1 else 0

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
  [Zero Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type} (VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i))

/-- `VC_i.Check^{O_j}(cm, Q, ans, pf)` run from inside an experiment, with `Q = dom ans`
(ePrint 2025/2166, p. 51). -/
@[expose]
noncomputable def checkAt (B : QReg) (i j : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg)
    (pf : Pf i) : QComp (cohSpec (extIn k X Y Cm Z)) B B Bool :=
  ((VC i).check cm ans pf).toQuantumAt (oracleImpl B j)

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

/-- **The P3 challenger** (ePrint 2025/2166, Def 7.3, p. 51), on the adversary's final
register `B`: extract `(m_i, td_i)_i` from the full tuple of the claim, open every position at
`Dom(m_i)`, run `VC_i.Check^{O_{idx_i}}` for `i ∈ W`, and report the event
`b = 0 ∧ |W| ≤ n ∧ (idx_i)_i distinct`. -/
@[expose]
noncomputable def extractChallenger (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (n : ℕ)
    (c : ExtractClaim k Cm) (B : QReg) : QComp (cohSpec (extIn k X Y Cm Z)) B B Bool :=
  (extractQuery code B (TpIC.full hk c.idx c.cm)).bind fun
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
    (B : QReg) : QComp (cohSpec (extIn k X Y Cm Z)) B B Bool :=
  (QComp.allIn c.W fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).bind fun b₁ ↦
    (extractQuery code B (TpIC.full hk c.idx c.cm)).bind fun otdm ↦
      (QComp.allIn c.Wᶜ fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).bind
        fun b₂ ↦ match otdm with
          | none => QuantumComp₂.pure false
          | some tdm =>
            (QComp.pi fun i : Fin k ↦ openAt VC B i (c.ans i).dom (tdm i).2).bind fun pf' ↦
              QuantumComp₂.pure (b₁ && b₂ &&
                decide (∃ i : Fin k, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) &&
                decide (∑ i, (c.ans i).dom.card ≤ qs) && decide (Function.Injective c.idx))

variable (E : VCOracle k X Y) (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S)
  (code : TpDCode k (DmOf ℓ Msg Td) Z)

/-- **P3, multi-extraction correctness** (ePrint 2025/2166, Def 7.3, p. 51): against every
`t`-query adversary querying `EO^(Ext)` whose oracle masses sum to at most `wVC` and whose
extraction mass is at most `wME`, and every `n ≤ k`, the P3 challenger reports its event with
probability at most `κ t wVC wME n`. -/
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
    (E.withExtract ME code).coherent.toRuntime.outcomeLawWith .instruments
      (experiment x fun u y ↦ extractChallenger VC code hk n (claim u y) u) ρ Sigma.snd
        {true} ≤ κ t wVC wME n

/-- **P4, offline extractability** (ePrint 2025/2166, Def 7.3, p. 51): against every
`t`-query adversary querying `EO^(Ext)` with the mass bounds of P3, the P4 challenger reports
its event with probability at most `κ t wVC wME qs`. -/
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
    (E.withExtract ME code).coherent.toRuntime.outcomeLawWith .instruments
      (experiment x fun u y ↦ offlineChallenger VC code hk qs (claim u y) u) ρ Sigma.snd
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
    (E.withExtract ME code).coherent.toRuntime.outcomeLawWith .instruments
      (experiment x.toCoherent fun u y ↦ extractChallenger VC code hk n (claim u y) u) ρ
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
    (E.withExtract ME code).coherent.toRuntime.outcomeLawWith .instruments
      (experiment x.toCoherent fun u y ↦ offlineChallenger VC code hk qs (claim u y) u) ρ
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
at `bot`. -/
@[expose]
def OnlineIndistinguishable (κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∀ (Yr Cell : Type) [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell] (bot : Cell)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    (t : ℕ) (wVC wME wRec : ℝ≥0∞) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (recIn k X Y Cm Z Yr)) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A),
    x.IsQueryBound (fun _ ↦ t) →
    ∑ i : Fin k, (E.withRecord ME code bot U hU).totalMass .instruments x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) (.inl (.inl i)) ≤ wVC →
    (E.withRecord ME code bot U hU).totalMass .instruments x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) (.inl (.inr ())) ≤ wME →
    (E.withRecord ME code bot U hU).totalMass .instruments x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) (.inr ()) ≤ wRec →
    (E.withRecord ME code bot U hU).coherent.toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.withRecordME ME code bot U hU).coherent.toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) + κ t wVC wME wRec ^ (2⁻¹ : ℝ) ∧
    (E.withRecordME ME code bot U hU).coherent.toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.withRecord ME code bot U hU).coherent.toRuntime.outcomeLawWith .instruments x ρ f
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

/-- **P5 for adversaries with classically named ports**, with per-port query masses in the world
`Record(U)`. -/
theorem OnlineIndistinguishable.of_classicalPorts {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    (h : OnlineIndistinguishable.{v, w} E ME code κ) {Yr Cell : Type} [Fintype Yr] [DecidableEq Yr]
    [Fintype Cell] [DecidableEq Cell] (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) {wVC wME wRec : ℝ≥0∞} {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec ((Fin k ⊕ Unit) ⊕ Unit)
      (recIn k X Y Cm Z Yr)) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A) {b : (Fin k ⊕ Unit) ⊕ Unit → ℕ}
    (hx : x.IsQueryBound b)
    (h₁ : ∑ i : Fin k, (E.withRecord ME code bot U hU).toRuntime.queryMass .instruments x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) (.inl (.inl i)) ≤ wVC)
    (h₂ : (E.withRecord ME code bot U hU).toRuntime.queryMass .instruments x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) (.inl (.inr ())) ≤ wME)
    (h₃ : (E.withRecord ME code bot U hU).toRuntime.queryMass .instruments x
      (ρ.matrix ⊗ₖ (E.withRecord ME code bot U hU).init.matrix) (.inr ()) ≤ wRec) :
    (E.withRecord ME code bot U hU).toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.withRecordME ME code bot U hU).toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) + κ (∑ i, b i) wVC wME wRec ^ (2⁻¹ : ℝ) ∧
    (E.withRecordME ME code bot U hU).toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.withRecord ME code bot U hU).toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) + κ (∑ i, b i) wVC wME wRec ^ (2⁻¹ : ℝ) := by
  have h' := h Yr Cell bot U hU (∑ i, b i) wVC wME wRec x.toCoherent f ρ
    (QuantumComp.isQueryBound_toCoherent hx)
    (by simpa only [EmulatedOracle.totalMass_toCoherent] using h₁)
    (by simpa only [EmulatedOracle.totalMass_toCoherent] using h₂)
    (by simpa only [EmulatedOracle.totalMass_toCoherent] using h₃)
  simpa only [EmulatedOracle.outcomeLawWith_toCoherent] using h'

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
  [Zero Y] [Fintype Msg] [DecidableEq Msg] [Fintype Cm] [DecidableEq Cm] {ℓ : Fin k → ℕ}
  {Td Pf : Fin k → Type} [∀ i, Fintype (Td i)] [∀ i, DecidableEq (Td i)]
  [∀ i, DecidableEq (Pf i)] (VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i))

/-- **Def 7.3 for a given oracle, extractor and encoding** (ePrint 2025/2166, pp. 50–51): the
extractor is admissible (Def 7.1, repaired as in `Quantum.MultiExtractor.Admissible`) with
`⊥ = (⊥^ℓ_i, tdBot i)`, and P1–P5 hold with the errors `κ`. -/
structure IsMultiExtractableWith {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (E : VCOracle k X Y) (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (tdBot : ∀ i, Td i) {Ω : Type*} (p : StdSimplex ℝ Ω)
    (Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))) (κ : MEErrors) : Prop where
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
    (Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))) (κ : MEErrors) : Prop :=
  ∃ (E : VCOracle k X Y) (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S) (Z : Type)
    (_ : Fintype Z) (_ : DecidableEq Z) (_ : AddGroup Z) (code : TpDCode k (DmOf ℓ Msg Td) Z),
    IsMultiExtractableWith.{v, w} VC E ME code tdBot p Ref κ

variable {VC}

/-- Def 7.3 for a given oracle is monotone in the errors. -/
theorem IsMultiExtractableWith.mono {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    {E : VCOracle k X Y} {ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S}
    {code : TpDCode k (DmOf ℓ Msg Td) Z} {tdBot : ∀ i, Td i} {Ω : Type*} {p : StdSimplex ℝ Ω}
    {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))} {κ κ' : MEErrors}
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
    {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))} {κ κ' : MEErrors}
    (h : IsMultiExtractable.{v, w} VC tdBot p Ref κ) (hκ : κ ≤ κ') :
    IsMultiExtractable.{v, w} VC tdBot p Ref κ' :=
  let ⟨E, ME, Z, i₁, i₂, i₃, code, hE⟩ := h
  ⟨E, ME, Z, i₁, i₂, i₃, code, hE.mono hκ⟩

end bundle

end Quantum
