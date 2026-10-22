/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import VCVio.Quantum.VC.MultiExtractable

/-!
# Multi-extractable vector commitments: the public interface

A consumer that begins with `module` and imports `VCVio.Quantum.VC.MultiExtractable` with an
ordinary `import` (no `import all`) can construct and eliminate each security predicate of
Def 7.3 of ePrint 2025/2166 through its definition:

* `Quantum.Simulates`, `Quantum.ComBound`, `Quantum.ExtractionCorrect`,
  `Quantum.OfflineExtractable` and `Quantum.OnlineIndistinguishable` are introduced by
  `fun`/`intro` against their quantifiers and eliminated by application;
* `Quantum.OraclesCommute` is proved from its defining equation;
* `Quantum.MEErrors.Monotone` is built from, and projected to, its four monotonicity facts;
* `Quantum.IsMultiExtractable` is built from, and destructured into, its witness.

The predicates are universe polymorphic in the adversary's local operations and leaves; a
statement that relates a predicate to a separately bound adversary names the universes. The last
section instantiates P3 at an adversary over `LocalSig.instruments.{1}` with outcome
`ULift.{1} Bool`, and runs an experiment through `Quantum.run_experiment`.
-/

open Quantum Matrix OracleSpec
open scoped ENNReal Kronecker

universe v w

namespace VCVioTest.QuantumVCModule

open EmulatedOracle (cohSpec)

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Msg] [DecidableEq Msg] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type} [∀ i, Fintype (Td i)]
  [∀ i, DecidableEq (Td i)] [∀ i, DecidableEq (Pf i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)} {E : VCOracle k X Y}
  {ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S} {code : TpDCode k (DmOf ℓ Msg Td) Z}

/-! ## P1 -/

/-- P1 is introduced against its quantifiers: every model simulates with the error `⊤`. -/
example {Ω : Type*} (p : Convexity.StdSimplex ℝ Ω)
    (Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)) : Simulates.{v, w} p Ref E ⊤ :=
  fun _ _ _ _ _ _ _ ↦ ⟨by simp, by simp⟩

/-- P1 is eliminated by application. -/
example {Ω : Type*} {p : Convexity.StdSimplex ℝ Ω}
    {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)}
    {κ : ℕ → ℝ≥0∞} (h : Simulates.{v, w} p Ref E κ) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (mixedOracleSpec k X Y) W A)
    (f : (Σ u, W u) → Bool)
    (ρ : SubState A) (hx : x.IsTotalQueryBound 0) :
    E.mixedRuntime.evalDistMap .instruments x ρ f {true} ≤
      mixedLawWith p Ref .instruments x ρ (fun _ ↦ f) {true} + κ 0 :=
  (h 0 x f ρ hx).1

/-- P1 against a uniformly sampled model is introduced from bounds against the sampled law. -/
example {Ω : Type} [SampleableType Ω] {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)} :
    Simulates.{v, w} (uniformWeights Ω) Ref E ⊤ :=
  Simulates.ofUniform fun _ _ _ _ _ _ _ ↦ ⟨by simp, by simp⟩

/-- P1 against a uniformly sampled model is eliminated to bounds against the sampled law. -/
example {Ω : Type} [SampleableType Ω] {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)}
    {κ : ℕ → ℝ≥0∞} (h : Simulates.{v, w} (uniformWeights Ω) Ref E κ) {A : QReg}
    {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (mixedOracleSpec k X Y) W A)
    (f : (Σ u, W u) → Bool)
    (ρ : SubState A) (hx : x.IsTotalQueryBound 0) :
    sampledEvalDistMap Ref .instruments x ρ (fun _ ↦ f) {true} ≤
      E.mixedRuntime.evalDistMap .instruments x ρ f {true} + κ 0 :=
  (simulates_uniformWeights_iff.mp h 0 x f ρ hx).2

/-! ## P2 -/

/-- `OraclesCommute` is proved from its defining equation. -/
example (h : ∀ i j : Fin k, onFactor (slotSnd (X × Y) (X × Y) E.S) (E.U i) *
      onFactor (slotFst (X × Y) (X × Y) E.S) (E.U j) =
    onFactor (slotFst (X × Y) (X × Y) E.S) (E.U j) *
      onFactor (slotSnd (X × Y) (X × Y) E.S) (E.U i)) :
    OraclesCommute E :=
  h

/-- `OraclesCommute` is eliminated to its defining equation. -/
example (h : OraclesCommute E) (i j : Fin k) :
    onFactor (slotSnd (X × Y) (X × Y) E.S) (E.U i) *
        onFactor (slotFst (X × Y) (X × Y) E.S) (E.U j) =
      onFactor (slotFst (X × Y) (X × Y) E.S) (E.U j) *
        onFactor (slotSnd (X × Y) (X × Y) E.S) (E.U i) :=
  h i j

/-- `ComBound` is introduced against its quantifiers. -/
example : ComBound.{v, w} E ME code ⊤ :=
  ⟨fun _ _ _ _ _ _ _ _ ↦ le_top, fun _ _ _ _ _ _ _ _ ↦ le_top⟩

/-- `ComBound` is eliminated by application. -/
example {κ : ℕ → ℝ≥0∞} (h : ComBound.{v, w} E ME code κ) (i : Fin k) {A Env : QReg}
    (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A
      (ComOut k X Y Cm Z Env) PUnit.{w + 1}) (ρ : SubState A)
    (hx : x.IsTotalQueryBound 0) : comError E ME code i x ρ ≤ κ 0 :=
  h.1 i 0 x ρ hx

/-- P2 bounds a read address selected from the complete final classical outcome. -/
example {κ : ℕ → ℝ≥0∞} (h : ComBound.{v, w} E ME code κ) {A Env : QReg}
    {α : Type w} (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z)
      A (ReadComOut k Cm Z Env) α) (ρ : SubState A) (c : α → Fin k × X)
    (hx : x.IsTotalQueryBound 3) : readComError E ME code x ρ c ≤ κ 3 :=
  h.2 3 x ρ c hx

/-! ## P3 and P4 -/

/-- P3 is introduced against its quantifiers. -/
example : ExtractionCorrect.{v, w} VC E ME code ⊤ := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact le_top

/-- P3 is eliminated by application. -/
example {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞} (h : ExtractionCorrect.{v, w} VC E ME code κ)
    (hk : 1 ≤ k)
    {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) W A)
    (claim : ∀ u, W u → ExtractClaim k Cm) (ρ : SubState A) (hx : x.IsQueryBound fun _ ↦ 0) :
    (E.mixedExtractRuntime ME code).evalDistMap .instruments
      (experiment x.liftOrdinary fun u y ↦ extractChallenger VC code hk 0 (claim u y) u) ρ Sigma.snd
        {true} ≤ κ 0 ⊤ ⊤ 0 :=
  h hk 0 0 ⊤ ⊤ x claim ρ (Nat.zero_le _) hx le_top le_top

/-- P4 is introduced against its quantifiers. -/
example : OfflineExtractable.{v, w} VC E ME code ⊤ := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  exact le_top

/-- P4 is eliminated by application. -/
example {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞} (h : OfflineExtractable.{v, w} VC E ME code κ)
    (hk : 1 ≤ k)
    {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) W A)
    (claim : ∀ u, W u → OpeningClaim k Cm Msg ℓ Pf) (ρ : SubState A)
    (hx : x.IsQueryBound fun _ ↦ 0) :
    (E.mixedExtractRuntime ME code).evalDistMap .instruments
      (experiment x.liftOrdinary fun u y ↦ offlineChallenger VC code hk 0 (claim u y) u) ρ Sigma.snd
        {true} ≤ κ 0 ⊤ ⊤ 0 :=
  h hk 0 0 ⊤ ⊤ x claim ρ hx le_top le_top

/-! ## P5 -/

/-- P5 is introduced against its quantifiers. -/
example : OnlineIndistinguishable.{v, w} E ME code ⊤ := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp

/-- P5 is eliminated by application. -/
example {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞} (h : OnlineIndistinguishable.{v, w} E ME code κ)
    (U : Matrix (Unit × Unit) (Unit × Unit) ℂ) (hU : U ∈ unitaryGroup (Unit × Unit) ℂ)
    {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (mixedRecSpec k X Y Cm Z Unit) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A) (hx : x.IsTotalQueryBound 0) :
    (E.mixedRecordRuntime ME code () U hU).evalDistMap .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.mixedRecordMERuntime ME code () U hU).evalDistMap .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) + κ 0 ⊤ ⊤ ⊤ ^ (2⁻¹ : ℝ) :=
  (h Unit Unit () U hU 0 ⊤ ⊤ ⊤ x f ρ hx le_top le_top le_top).1

/-- A trusted wrapper with a real read port is in the quantified P5 program class. -/
example {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    (h : OnlineIndistinguishable.{v, 0} E ME code κ) (c : Fin k × X)
    (U : Matrix (Unit × Unit) (Unit × Unit) ℂ) (hU : U ∈ unitaryGroup (Unit × Unit) ℂ)
    (ρ : SubState (QReg.of (Unit × Unit))) :
    let x : QuantumComp LocalSig.instruments.{v} (mixedRecSpec k X Y Cm Z Unit)
        (fun _ ↦ Bool) (QReg.of (Unit × Unit)) :=
      QuantumComp.queryBind (.inr c) (QReg.of Unit) (Equiv.refl _) fun a ↦
        QuantumComp.pure a.isSome
    (E.mixedRecordRuntime ME code () U hU).evalDistMap .instruments x ρ Sigma.snd
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.mixedRecordMERuntime ME code () U hU).evalDistMap .instruments x ρ Sigma.snd
        {true} ^ (2⁻¹ : ℝ) + κ 1 ⊤ ⊤ ⊤ ^ (2⁻¹ : ℝ) := by
  dsimp only
  exact (h Unit Unit () U hU 1 ⊤ ⊤ ⊤
    (A := QReg.of (Unit × Unit)) (W := fun _ ↦ Bool)
    (QuantumComp.queryBind (.inr c) (QReg.of Unit) (Equiv.refl _) fun a ↦
      QuantumComp.pure a.isSome) Sigma.snd ρ
    ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
      ⟨by decide, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩) le_top le_top le_top).1

/-- A read wrapper charges its full incoming trace to the source-world oracle mass. -/
example (c : Fin k × X)
    (U : Matrix (Unit × Unit) (Unit × Unit) ℂ) (hU : U ∈ unitaryGroup (Unit × Unit) ℂ)
    (ρ : Matrix ((Unit × Unit) × (E.withRecord ME code () U hU).S)
      ((Unit × Unit) × (E.withRecord ME code () U hU).S) ℂ) :
    let x : QuantumComp LocalSig.instruments.{v} (mixedRecSpec k X Y Cm Z Unit)
        (fun _ ↦ Bool) (QReg.of (Unit × Unit)) :=
      QuantumComp.queryBind (.inr c) (QReg.of Unit) (Equiv.refl _) fun a ↦
        QuantumComp.pure a.isSome
    (E.mixedRecordRuntime ME code () U hU).totalWeight .instruments
      (E.recordVCWeight ME code () U hU) x ρ = ENNReal.ofReal ρ.trace.re := by
  dsimp only
  erw [QuantumRuntime.totalWeight_queryBind]
  conv_lhs =>
    rhs
    arg 1
    ext r
    erw [QuantumRuntime.totalWeight_pure]
  simp only [tsum_zero, add_zero, VCOracle.recordVCWeight,
    QuantumRuntime.withReadWeight]
  erw [QuantumRuntime.trace_callInput]
  rfl

/-! ## The bundle -/

/-- `MEErrors.Monotone` is built from its four monotonicity facts. -/
example (κ : MEErrors) (h₁ : Monotone κ.sim) (h₂ : Monotone κ.com)
    (h₃ : Monotone fun p : ℕ × ℝ≥0∞ × ℝ≥0∞ × ℕ ↦ κ.offline p.1 p.2.1 p.2.2.1 p.2.2.2)
    (h₄ : Monotone fun p : ℕ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ ↦ κ.online p.1 p.2.1 p.2.2.1 p.2.2.2) :
    κ.Monotone :=
  ⟨h₁, h₂, h₃, h₄⟩

/-- `MEErrors.Monotone` gives the monotonicity of `κsim`. -/
example (κ : MEErrors) (h : κ.Monotone) : Monotone κ.sim :=
  h.1

/-- The order on errors is eliminated to its components. -/
example {κ κ' : MEErrors} (h : κ ≤ κ') : κ.sim ≤ κ'.sim :=
  h.1

/-- `IsMultiExtractable` is built from a witness. -/
example {tdBot : ∀ i, Td i} {Ω : Type*} {p : Convexity.StdSimplex ℝ Ω}
    {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)} {κ : MEErrors}
    (h : IsMultiExtractableWith.{v, w} VC E ME code tdBot p Ref κ) :
    IsMultiExtractable.{v, w} VC tdBot p Ref κ :=
  ⟨E, ME, Z, inferInstance, inferInstance, inferInstance, code, h⟩

/-- `IsMultiExtractable` is destructured into its witness. -/
example {tdBot : ∀ i, Td i} {Ω : Type*} {p : Convexity.StdSimplex ℝ Ω}
    {Ref : Ω → QuantumRuntime (mixedOracleSpec k X Y)} {κ : MEErrors}
    (h : IsMultiExtractable.{v, w} VC tdBot p Ref κ) :
    ∃ E : VCOracle k X Y, OraclesCommute E := by
  obtain ⟨E, _, _, _, _, _, _, hE⟩ := h
  exact ⟨E, hE.commute⟩

/-! ## Universes -/

/-- P3 applies to an adversary whose local operations have outcomes in `Type 1` and whose leaves
are `ULift.{1} Bool`. -/
example {κ : ℕ → ℝ≥0∞ → ℝ≥0∞ → ℕ → ℝ≥0∞} (h : ExtractionCorrect.{1, 1} VC E ME code κ)
    (hk : 1 ≤ k) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{1} (cohSpec (extIn k X Y Cm Z))
      (fun _ ↦ ULift.{1} Bool) A)
    (claim : QReg → ULift.{1} Bool → ExtractClaim k Cm) (ρ : SubState A)
    (hx : x.IsQueryBound fun _ ↦ 0) :
    (E.mixedExtractRuntime ME code).evalDistMap .instruments
      (experiment x.liftOrdinary fun u y ↦ extractChallenger VC code hk 0 (claim u y) u) ρ Sigma.snd
        {true} ≤ κ 0 ⊤ ⊤ 0 :=
  h hk 0 0 ⊤ ⊤ x claim ρ (Nat.zero_le _) hx le_top le_top

/-- The run of an experiment of a large adversary is the run of the adversary followed by the
run of the unlifted challenger. -/
example (hk : 1 ≤ k) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{1} (cohSpec (extIn k X Y Cm Z))
      (fun _ ↦ ULift.{1} Bool) A)
    (claim : QReg → ULift.{1} Bool → ExtractClaim k Cm) :
    (E.mixedExtractRuntime ME code).run .instruments
        (experiment x.liftOrdinary fun u y ↦ extractChallenger VC code hk 0 (claim u y) u) =
      ((E.withExtract ME code).coherent.toRuntime.run .instruments x).bind fun p ↦
        (E.mixedExtractRuntime ME code).run .instruments
          (extractChallenger VC code hk 0 (claim p.1 p.2) p.1).forgetReg :=
  by
    rw [run_experiment]
    erw [QuantumRuntime.run_liftOrdinary]
    rfl

/-! ## Retained offline events -/

example (tic : TpIC k Cm) (B : QReg) :
    MatrixMap.IsCPTNIFamily (fun tdm ↦
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ extractProj ME tic tdm)) :=
  extractProj_isCPTNIFamily ME tic B

variable (R : QuantumRuntime (mixedExtSpec k X Y Cm Z)) (hk : 1 ≤ k) (qs : ℕ)
  (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)

example (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool)
    (hr : ¬ ∃ tdm, r = (true, some tdm, true)) :
    (R.run₂ .instruments (offlineFinish VC (Z := Z) hk qs c B r)).branch true = 0 :=
  run₂_offlineFinish_reject VC R hk qs c B r hr

example (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool)
    (hr : ¬ ∃ tdm, r = (true, some tdm, true)) :
    (R.run₂ .instruments (offlineInstrument VC code hk qs c B)).branch (r, true) = 0 :=
  run₂_offlineInstrument_reject VC code R hk qs c B r hr

example (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :
    (R.run₂ .instruments (offlineFinish VC (Z := Z) hk qs c B r)).branch true = 0 :=
  run₂_offlineFinish_over_budget VC R hk qs c B hq r

example (ρ : SubState (B × R.D)) :
    (R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true} =
      ∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
        (offlineInstrument VC code hk qs c B)).branch ((true, some tdm, true), true))
          ρ.matrix).trace.re :=
  offlineChallenger_weight_eq_retained VC code R hk qs c B ρ

example (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :
    (R.run₂ .instruments (offlineInstrument VC code hk qs c B)).branch (r, true) = 0 :=
  run₂_offlineInstrument_over_budget VC code R hk qs c B hq r

example (ρ : SubState (B × R.D)) (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs) :
    (R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true} = 0 :=
  offlineChallenger_over_budget VC code R hk qs c B ρ hq

/-- The experiment equation preserves dependent registers and arbitrary leaf universes. -/
example {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) W A)
    (chal : ∀ u, W u → QComp (mixedExtSpec k X Y Cm Z) u u Bool) (ρ : SubState A) :
    R.evalDistMap .instruments (experiment x chal) ρ Sigma.snd {true} =
      ∑' p : Σ u, W u, (R.run₂ .instruments (chal p.1 p.2)).outcomeMeasure
        (R.jointPost .instruments x ρ p) {true} :=
  evalDistMap_experiment_true_eq_tsum R x chal ρ

end VCVioTest.QuantumVCModule
