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
  [Zero Y] [Fintype Msg] [DecidableEq Msg] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type} [∀ i, Fintype (Td i)]
  [∀ i, DecidableEq (Td i)] [∀ i, DecidableEq (Pf i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)} {E : VCOracle k X Y}
  {ME : MultiExtractor k Cm (DmOf ℓ Msg Td) E.S} {code : TpDCode k (DmOf ℓ Msg Td) Z}

/-! ## P1 -/

/-- P1 is introduced against its quantifiers: every model simulates with the error `⊤`. -/
example {Ω : Type*} (p : Convexity.StdSimplex ℝ Ω)
    (Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))) : Simulates.{v, w} p Ref E ⊤ :=
  fun _ _ _ _ _ _ _ ↦ ⟨by simp, by simp⟩

/-- P1 is eliminated by application. -/
example {Ω : Type*} {p : Convexity.StdSimplex ℝ Ω} {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))}
    {κ : ℕ → ℝ≥0∞} (h : Simulates.{v, w} p Ref E κ) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (oIn k X Y)) W A)
    (f : (Σ u, W u) → Bool)
    (ρ : SubState A) (hx : x.IsQueryBound fun _ ↦ 0) :
    E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} ≤
      mixedLawWith p Ref .instruments x ρ (fun _ ↦ f) {true} + κ 0 :=
  (h 0 x f ρ hx).1

/-- P1 against a uniformly sampled model is introduced from bounds against the sampled law. -/
example {Ω : Type} [SampleableType Ω] {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))} :
    Simulates.{v, w} (uniformWeights Ω) Ref E ⊤ :=
  Simulates.ofUniform fun _ _ _ _ _ _ _ ↦ ⟨by simp, by simp⟩

/-- P1 against a uniformly sampled model is eliminated to bounds against the sampled law. -/
example {Ω : Type} [SampleableType Ω] {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))}
    {κ : ℕ → ℝ≥0∞} (h : Simulates.{v, w} (uniformWeights Ω) Ref E κ) {A : QReg}
    {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (oIn k X Y)) W A)
    (f : (Σ u, W u) → Bool)
    (ρ : SubState A) (hx : x.IsQueryBound fun _ ↦ 0) :
    sampledLawWith Ref .instruments x ρ (fun _ ↦ f) {true} ≤
      E.coherent.toRuntime.outcomeLawWith .instruments x ρ f {true} + κ 0 :=
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
  fun _ _ _ _ _ _ _ _ ↦ le_top

/-- `ComBound` is eliminated by application. -/
example {κ : ℕ → ℝ≥0∞} (h : ComBound.{v, w} E ME code κ) (i : Fin k) {A Env : QReg}
    (x : QuantumComp₂ LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) A
      (ComOut k X Y Cm Z Env) PUnit.{w + 1}) (ρ : SubState A)
    (hx : x.IsQueryBound fun _ ↦ 0) : comError E ME code i x ρ ≤ κ 0 :=
  h i 0 x ρ hx

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
    (E.withExtract ME code).coherent.toRuntime.outcomeLawWith .instruments
      (experiment x fun u y ↦ extractChallenger VC code hk 0 (claim u y) u) ρ Sigma.snd
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
    (E.withExtract ME code).coherent.toRuntime.outcomeLawWith .instruments
      (experiment x fun u y ↦ offlineChallenger VC code hk 0 (claim u y) u) ρ Sigma.snd
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
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (recIn k X Y Cm Z Unit)) W A)
    (f : (Σ u, W u) → Bool) (ρ : SubState A) (hx : x.IsQueryBound fun _ ↦ 0) :
    (E.withRecord ME code () U hU).coherent.toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) ≤
      (E.withRecordME ME code () U hU).coherent.toRuntime.outcomeLawWith .instruments x ρ f
        {true} ^ (2⁻¹ : ℝ) + κ 0 ⊤ ⊤ ⊤ ^ (2⁻¹ : ℝ) :=
  (h Unit Unit () U hU 0 ⊤ ⊤ ⊤ x f ρ hx le_top le_top le_top).1

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
    {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))} {κ : MEErrors}
    (h : IsMultiExtractableWith.{v, w} VC E ME code tdBot p Ref κ) :
    IsMultiExtractable.{v, w} VC tdBot p Ref κ :=
  ⟨E, ME, Z, inferInstance, inferInstance, inferInstance, code, h⟩

/-- `IsMultiExtractable` is destructured into its witness. -/
example {tdBot : ∀ i, Td i} {Ω : Type*} {p : Convexity.StdSimplex ℝ Ω}
    {Ref : Ω → QuantumRuntime (cohSpec (oIn k X Y))} {κ : MEErrors}
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
    (E.withExtract ME code).coherent.toRuntime.outcomeLawWith .instruments
      (experiment x fun u y ↦ extractChallenger VC code hk 0 (claim u y) u) ρ Sigma.snd
        {true} ≤ κ 0 ⊤ ⊤ 0 :=
  h hk 0 0 ⊤ ⊤ x claim ρ (Nat.zero_le _) hx le_top le_top

/-- The run of an experiment of a large adversary is the run of the adversary followed by the
run of the unlifted challenger. -/
example (hk : 1 ≤ k) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{1} (cohSpec (extIn k X Y Cm Z))
      (fun _ ↦ ULift.{1} Bool) A)
    (claim : QReg → ULift.{1} Bool → ExtractClaim k Cm) :
    (E.withExtract ME code).coherent.toRuntime.run .instruments
        (experiment x fun u y ↦ extractChallenger VC code hk 0 (claim u y) u) =
      ((E.withExtract ME code).coherent.toRuntime.run .instruments x).bind fun p ↦
        (E.withExtract ME code).coherent.toRuntime.run .instruments
          (extractChallenger VC code hk 0 (claim p.1 p.2) p.1).forgetReg :=
  run_experiment _ x _

end VCVioTest.QuantumVCModule
