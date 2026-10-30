/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Unitaries
public import QuantumFoundations.Oracle.Unitary
public import VCVio.Quantum.Oracle.ClassicalRead

/-!
# Emulated oracles for vector commitments

The oracles of the multi-extractability experiments of Chiesa, Di, Hu and Zheng
(ePrint 2025/2166, §7, pp. 50–51), as emulated oracles (`Quantum.EmulatedOracle`):

* `EO = (Init, (O_i)_{i ∈ [k]})` (p. 50): `k` unitary ports on the query register `X × Y`
  (`Quantum.VCOracle`);
* `EO^(Ext) = (Init, ((O_i)_i, U_MultiExtract))` (p. 50): one further port on
  `TpIC × Z`, answered by the purified extractor (`Quantum.VCOracle.withExtract`);
* `EO^(Record)` (p. 51): `EO^(Ext)` with the recording register `R` adjoined in the state
  with every cell at `⊥`, and one further port on `TpIC × Yr`, answered by `Record(U)`
  (`Quantum.VCOracle.withRecord`) or `Record(MultiExtract, U)` (`Quantum.VCOracle.withRecordME`);
* the random-oracle model as an emulated oracle with a trivial private register
  (`Quantum.romVCOracle`, p. 28).

Trusted classical checks use a projective read on the same private register, returning `Option Y`.
The mixed runtimes carry this read alongside ordinary, extraction, and recording ports. The read
certificate concerns the base oracle; it asserts no commutation with extraction or recording.

"Polynomial time" of the emulation (p. 50) is not part of the definitions.

## Main definitions

* `Quantum.oIn`, `Quantum.extIn`, `Quantum.recIn`: the port registers.
* `Quantum.VCOracle`, `Quantum.VCOracle.withExtract`, `Quantum.VCOracle.withRecord`,
  `Quantum.VCOracle.withRecordME`, `Quantum.romVCOracle`.
-/

public section

open Matrix MeasureTheory
open scoped Kronecker ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum

/-- The original joint poststates of an arbitrary runtime have total trace at most one. -/
theorem QuantumRuntime.tsum_jointPost_trace_le_one {spec : QuantumOracleSpec.{u, v}}
    (R : QuantumRuntime spec) {L : LocalSig.{u₁, v₁}} (I : L.Interp)
    {A : QReg} {W : QReg → Type w} (x : QuantumComp L spec W A) (ρ : SubState A) :
    ∑' p, ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re ≤ 1 := by
  exact ((R.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le (ρ.prod R.init).posSemidef).trans
    (ENNReal.ofReal_le_one.mpr (ρ.prod R.init).trace_re_le_one)

/-- Every measurable runtime event has probability at most one. -/
theorem QuantumRuntime.outcomeLawWith_le_one {spec : QuantumOracleSpec.{u, v}}
    (R : QuantumRuntime spec) {L : LocalSig.{u₁, v₁}} (I : L.Interp)
    {A : QReg} {W : QReg → Type w} (x : QuantumComp L spec W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) (s : Set γ) :
    R.evalDistMap I x ρ f s ≤ 1 := by
  apply (measure_mono (Set.subset_univ s)).trans
  rw [R.evalDistMap_apply_univ I x ρ f, ← R.tsum_jointPost_trace I x ρ]
  exact R.tsum_jointPost_trace_le_one I x ρ

/-- A trace-weighted constant has total weight at most that constant. -/
theorem tsum_weighted_trace_le {P : Type*} (m : P → ℝ≥0∞) (hm : ∑' p, m p ≤ 1)
    (c : ℝ≥0∞) : ∑' p, c * m p ≤ c := by
  rw [ENNReal.tsum_mul_left]
  exact (mul_le_mul_right hm c).trans_eq (mul_one c)

/-- The total weight of the outcomes of a run is at most one. -/
theorem QuantumRuntime.tsum_jointPost₂_trace_le_one {spec : QuantumOracleSpec.{u₁, v₁}}
    (R : QuantumRuntime spec) {L : LocalSig.{u, v}} (I : L.Interp) {A B : QReg} {α : Type w}
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    ∑' a, ENNReal.ofReal (R.jointPost₂ I x ρ a).matrix.trace.re ≤ 1 := by
  let _ : MeasurableSpace α := ⊤
  have h := (R.run₂ I x).outcomeMeasure_apply_univ_le_one (ρ.prod R.init)
  rw [DSubInstrument.outcomeMeasure_apply _ _ MeasurableSet.univ] at h
  simp only [Set.indicator_univ, Pi.one_apply, mul_one] at h
  exact h

/-- The difference of two complete Kraus families has squared trace at most four times
input trace, with the outcomes retained inside the sum. -/
theorem sum_trace_conj_sub_le_four {n m ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [Fintype ι] (F G : ι → Matrix m n ℂ)
    (hF : ∑ a, (F a)ᴴ * F a = 1) (hG : ∑ a, (G a)ᴴ * G a = 1)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    ∑ a, ENNReal.ofReal (MatrixMap.conj (F a - G a) ρ).trace.re ≤
      4 * ENNReal.ofReal ρ.trace.re := by
  have hpoint (a : ι) : (MatrixMap.conj (F a - G a) ρ).trace.re ≤
      2 * ((MatrixMap.conj (F a) ρ).trace.re + (MatrixMap.conj (G a) ρ).trace.re) := by
    have hp := (hρ.mul_mul_conjTranspose_same (F a + G a)).trace_re_nonneg
    have he : MatrixMap.conj (F a - G a) ρ + MatrixMap.conj (F a + G a) ρ =
        (MatrixMap.conj (F a) ρ + MatrixMap.conj (G a) ρ) +
        (MatrixMap.conj (F a) ρ + MatrixMap.conj (G a) ρ) := by
      simp only [MatrixMap.conj_apply, conjTranspose_sub, conjTranspose_add]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add]
      abel
    have ht := congrArg (fun M ↦ M.trace.re) he
    simp only [trace_add, Complex.add_re] at ht
    have hp' : 0 ≤ (MatrixMap.conj (F a + G a) ρ).trace.re := hp
    linarith
  have hf := congrArg Complex.re (MatrixMap.isTP_sum_conj hF ρ)
  have hg := congrArg Complex.re (MatrixMap.isTP_sum_conj hG ρ)
  simp only [LinearMap.sum_apply, trace_sum, Complex.re_sum] at hf hg
  have hn (a : ι) : 0 ≤ (MatrixMap.conj (F a - G a) ρ).trace.re :=
    (hρ.mul_mul_conjTranspose_same (F a - G a)).trace_re_nonneg
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ hn a),
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ a, 2 * ((MatrixMap.conj (F a) ρ).trace.re +
        (MatrixMap.conj (G a) ρ).trace.re) := Finset.sum_le_sum fun a _ ↦ hpoint a
    _ = 4 * ρ.trace.re := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hf, hg]; ring

section extractionMeasurement

variable {k : ℕ} {Cm : Type} {Dm : Fin k → Type}

/-- The projector onto the private states `s` with `MultiExtract(tic, s) = tdm` (the paper's
`Π_tdm`, p. 59). -/
@[expose]
noncomputable def extractProj {S : Type*} [DecidableEq S] [∀ i, DecidableEq (Dm i)]
    (ME : MultiExtractor k Cm Dm S) (tic : TpIC k Cm) (tdm : TpDLen k Dm tic.1) :
    Matrix S S ℂ :=
  diagonal fun s ↦ if ME.extract tic s = tdm then 1 else 0

/-- Measured extraction fibres form a completely positive, trace-nonincreasing family,
including when the decommitment outcome type is not finite. -/
theorem extractProj_isCPTNIFamily {S : Type*} [Fintype S] [DecidableEq S]
    [∀ i, DecidableEq (Dm i)] (ME : MultiExtractor k Cm Dm S) (tic : TpIC k Cm) (B : QReg) :
    MatrixMap.IsCPTNIFamily (fun tdm ↦
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ extractProj ME tic tdm)) := by
  classical
  let K := fun tdm ↦ (1 : Matrix B B ℂ) ⊗ₖ extractProj ME tic tdm
  have he (tdm) : K tdm = diagonal (fun b : B × S ↦
      if ME.extract tic b.2 = tdm then (1 : ℂ) else 0) := by
    simp only [K, extractProj, ← diagonal_one, diagonal_kronecker_diagonal, one_mul]
  refine ⟨fun _ ↦ MatrixMap.isCP_conj _, fun fs ρ hρ ↦ ?_⟩
  have hg : ∑ tdm ∈ fs, (K tdm)ᴴ * K tdm =
      diagonal (fun b : B × S ↦ if ME.extract tic b.2 ∈ fs then (1 : ℂ) else 0) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [he, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal]
    · simp [he, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal, hab]
  have ht : (1 - ∑ tdm ∈ fs, (K tdm)ᴴ * K tdm).PosSemidef := by
    rw [hg, ← diagonal_one, diagonal_sub]
    apply PosSemidef.diagonal
    intro b
    by_cases hb : ME.extract tic b.2 ∈ fs <;> simp [hb]
  have hh := ht.trace_mul_re_nonneg hρ
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, ← MatrixMap.trace_conj_apply] at hh
  exact sub_nonneg.mp hh

end extractionMeasurement

variable (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## Port registers -/

/-- The register of each oracle port: the query register `X × Y` (ePrint 2025/2166, p. 50). -/
abbrev oIn : Fin k → QReg :=
  fun _ ↦ QReg.of (X × Y)

/-- `EO = (Init, (O_i)_{i ∈ [k]})` (ePrint 2025/2166, p. 50): an emulated oracle with `k`
ports on the query register `X × Y`. -/
structure VCOracle extends EmulatedOracle (Fin k) (oIn k X Y) where
  /-- The projective classical read on the shared private register. -/
  classicalRead : ProjectiveClassicalAnswers toEmulatedOracle (Fin k × X) (Option Y)

/-- The port registers of `EO^(Ext)`: the oracle ports, then the extraction port on `TpIC × Z`
(ePrint 2025/2166, p. 50). -/
abbrev extIn (Cm Z : Type) [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] :
    Fin k ⊕ Unit → QReg :=
  Sum.elim (oIn k X Y) fun _ ↦ QReg.of (TpIC k Cm × Z)

/-- The port registers of `EO^(Record)`: the ports of `EO^(Ext)`, then the record port on
`TpIC × Yr` (ePrint 2025/2166, p. 51). -/
abbrev recIn (Cm Z Yr : Type) [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z]
    [Fintype Yr] [DecidableEq Yr] : (Fin k ⊕ Unit) ⊕ Unit → QReg :=
  Sum.elim (extIn k X Y Cm Z) fun _ ↦ QReg.of (TpIC k Cm × Yr)

/-- Coherent oracle calls and classical reads on the same database. -/
abbrev mixedOracleSpec :=
  withReadSpec (EmulatedOracle.cohSpec (oIn k X Y)) (Fin k × X) (Option Y)

/-- Coherent oracle/extraction calls together with classical reads. -/
abbrev mixedExtSpec (Cm Z : Type) [Fintype Cm] [DecidableEq Cm]
    [Fintype Z] [DecidableEq Z] :=
  withReadSpec (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) (Fin k × X) (Option Y)

/-- Coherent oracle/extraction/record calls together with classical reads. -/
abbrev mixedRecSpec (Cm Z Yr : Type) [Fintype Cm] [DecidableEq Cm]
    [Fintype Z] [DecidableEq Z] [Fintype Yr] [DecidableEq Yr] :=
  withReadSpec (EmulatedOracle.cohSpec (recIn k X Y Cm Z Yr)) (Fin k × X) (Option Y)

variable {k X Y}

namespace VCOracle

variable {Cm Z : Type} [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {Dm : Fin k → Type} (E : VCOracle k X Y)

/-- The base oracle with its projective classical reads. -/
@[expose, reducible]
noncomputable def mixedRuntime : QuantumRuntime (mixedOracleSpec k X Y) :=
  E.toEmulatedOracle.withClassicalReads E.classicalRead

/-- Reads at any two classical addresses commute on the shared private register. -/
theorem read_read_commute (c d : Fin k × X) (a b : Option Y) :
    E.classicalRead.A c a * E.classicalRead.A d b =
      E.classicalRead.A d b * E.classicalRead.A c a :=
  E.classicalRead.commute_cells c a d b

/-- Every ordinary oracle call commutes with the framed read projector. -/
theorem read_ordinary_commute (i : Fin k) (c : Fin k × X) (a : Option Y) :
    E.U i * (1 ⊗ₖ E.classicalRead.A c a) = (1 ⊗ₖ E.classicalRead.A c a) * E.U i :=
  E.classicalRead.commute_ordinary i c a

/-- Repeating a read preserves its answer branch and annihilates every conflicting answer. -/
theorem read_replay (c : Fin k × X) (a b : Option Y) :
    E.classicalRead.A c a * E.classicalRead.A c b =
      if a = b then E.classicalRead.A c a else 0 :=
  E.classicalRead.orthogonal c a b

/-- Sequential branches of the read instrument retain only consistent repeated answers. -/
theorem read_instrument_replay (c : Fin k × X) (a b : Option Y) :
    (E.classicalRead.instrument c).branch a ∘ₗ (E.classicalRead.instrument c).branch b =
      if a = b then (E.classicalRead.instrument c).branch a else 0 := by
  rw [ProjectiveClassicalAnswers.instrument_branch, ProjectiveClassicalAnswers.instrument_branch,
    ← MatrixMap.conj_mul, E.read_replay]
  split_ifs <;> simp

/-- Framing the read projectors preserves their Kraus completeness. -/
theorem read_kraus_complete (B : QReg) (c : Fin k × X) :
    ∑ a, ((1 : Matrix B B ℂ) ⊗ₖ E.classicalRead.A c a)ᴴ *
      (1 ⊗ₖ E.classicalRead.A c a) = 1 := by
  classical
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, mul_one,
    E.classicalRead.hermitian, E.classicalRead.orthogonal, ite_true]
  change ∑ a, (kroneckerBilinear (R := ℂ) (1 : Matrix B B ℂ)) (E.classicalRead.A c a) = 1
  rw [← map_sum, E.classicalRead.complete]
  exact one_kronecker_one

/-! ## Extraction -/

/-- **`EO^(Ext)`** (ePrint 2025/2166, p. 50): the oracle `E` with one further port on
`TpIC × Z`, answered by the purified extractor `U_MultiExtract` on the private register. -/
@[expose]
noncomputable def withExtract (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z) :
    EmulatedOracle (Fin k ⊕ Unit) (extIn k X Y Cm Z) :=
  E.toEmulatedOracle.extend (fun _ ↦ extractUnitary ME code)
    fun _ ↦ extractUnitary_mem_unitaryGroup ME code

variable (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)

/-- Extraction and reads share the base private register, without a commutation assertion. -/
@[expose, reducible]
noncomputable def mixedExtractRuntime : QuantumRuntime (mixedExtSpec k X Y Cm Z) :=
  (E.withExtract ME code).coherent.toRuntime.extend E.classicalRead.step

/-- Every ordinary, extraction, and read step preserves total probability. -/
theorem lossless_mixedExtractRuntime_step (p : (mixedExtSpec k X Y Cm Z).Port) :
    ((E.mixedExtractRuntime ME code).step p).Lossless := by
  cases p with
  | inl p => exact (E.withExtract ME code).coherent.lossless_toRuntime_step p
  | inr x => exact E.classicalRead.lossless_step x

/-- `EO^(Ext)` keeps the private register. -/
@[simp]
theorem withExtract_S : (E.withExtract ME code).S = E.S :=
  rfl

/-- `EO^(Ext)` keeps the initial state. -/
@[simp]
theorem withExtract_init : (E.withExtract ME code).init = E.init :=
  rfl

/-- The oracle ports of `EO^(Ext)` are those of `E`. -/
@[simp]
theorem withExtract_U_inl (i : Fin k) : (E.withExtract ME code).U (.inl i) = E.U i :=
  rfl

/-- The extraction port of `EO^(Ext)` is `U_MultiExtract`. -/
@[simp]
theorem withExtract_U_inr (u : Unit) :
    (E.withExtract ME code).U (.inr u) = extractUnitary ME code :=
  rfl

/-! ## Recording -/

variable {Yr Cell : Type} [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]

/-- `EO^(Ext)` with the recording register `R` adjoined in the state with every cell at `bot`
(the step from `Init` to `Init′` of ePrint 2025/2166, p. 51). -/
@[expose, reducible]
noncomputable def withRecReg (bot : Cell) : EmulatedOracle (Fin k ⊕ Unit) (extIn k X Y Cm Z) :=
  (E.withExtract ME code).addRegister (QReg.of (RecReg k Cm Dm Cell))
    (SubState.basis (RecReg.const bot))

/-- **`EO^(Record)` in the world `Record(U)`** (ePrint 2025/2166, p. 51): `EO^(Ext)` with
the recording register adjoined, every cell at `bot`, and one further port on `TpIC × Yr`
answered by `Record(U)`. -/
@[expose]
noncomputable def withRecord (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) (recIn k X Y Cm Z Yr) :=
  (E.withRecReg ME code bot).extend (fun _ ↦ recordUnitary U)
    fun _ ↦ recordUnitary_mem_unitaryGroup hU

/-- **`EO^(Record)` in the world `Record(MultiExtract, U)`** (ePrint 2025/2166, p. 51): as
`Quantum.VCOracle.withRecord`, with the record port answered by `Record(MultiExtract, U)`. -/
@[expose]
noncomputable def withRecordME (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) (recIn k X Y Cm Z Yr) :=
  (E.withRecReg ME code bot).extend (fun _ ↦ recordMEUnitary ME U)
    fun _ ↦ recordMEUnitary_mem_unitaryGroup ME hU

/-- A read carries the recording register unchanged. -/
@[expose]
noncomputable def recordingRead (x : Fin k × X) :
    SubInstrument (Unit × (E.S × RecReg k Cm Dm Cell))
      (Unit × (E.S × RecReg k Cm Dm Cell)) (Option Y) :=
  (E.classicalRead.step x).frame (RecReg k Cm Dm Cell) |>.reindex
    (Equiv.prodAssoc Unit E.S (RecReg k Cm Dm Cell))
    (Equiv.prodAssoc Unit E.S (RecReg k Cm Dm Cell))

/-- Reads beside the recording extension use the base oracle instrument. -/
@[expose, reducible]
noncomputable def mixedRecordRuntime (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) : QuantumRuntime (mixedRecSpec k X Y Cm Z Yr) :=
  (E.withRecord ME code bot U hU).coherent.toRuntime.extend E.recordingRead

/-- Reads beside the extractor-controlled recording extension use the same instrument. -/
@[expose, reducible]
noncomputable def mixedRecordMERuntime (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) : QuantumRuntime (mixedRecSpec k X Y Cm Z Yr) :=
  (E.withRecordME ME code bot U hU).coherent.toRuntime.extend E.recordingRead

/-- Ordinary oracle mass plus full read-input trace in the unsplit recording world. -/
@[expose]
noncomputable def recordVCWeight (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    ∀ p, Matrix ((mixedRecSpec k X Y Cm Z Yr).In p × (E.withRecord ME code bot U hU).S)
      ((mixedRecSpec k X Y Cm Z Yr).In p × (E.withRecord ME code bot U hU).S) ℂ → ℝ≥0∞ :=
  QuantumRuntime.withReadWeight fun _ σ ↦ ∑ i : Fin k,
    ENNReal.ofReal (MatrixMap.conj
      ((E.withRecord ME code bot U hU).indexProj (.inl (.inl i))) σ).trace.re

/-- Extraction or recording index mass. Read ports contribute zero to these masses. -/
@[expose]
noncomputable def recordIndexWeight (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) (i : (Fin k ⊕ Unit) ⊕ Unit) :
    ∀ p, Matrix ((mixedRecSpec k X Y Cm Z Yr).In p × (E.withRecord ME code bot U hU).S)
      ((mixedRecSpec k X Y Cm Z Yr).In p × (E.withRecord ME code bot U hU).S) ℂ → ℝ≥0∞
  | .inl _, σ => ENNReal.ofReal
      (MatrixMap.conj ((E.withRecord ME code bot U hU).indexProj i) σ).trace.re
  | .inr _, _ => 0

variable (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
  (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)

/-- The two record worlds share their ports other than the record port. -/
theorem withRecord_U_inl (i : Fin k ⊕ Unit) :
    (E.withRecord ME code bot U hU).U (.inl i) = (E.withRecordME ME code bot U hU).U (.inl i) :=
  rfl

/-- The record port of `Record(U)`. -/
@[simp]
theorem withRecord_U_inr (u : Unit) :
    (E.withRecord ME code bot U hU).U (.inr u) = recordUnitary U :=
  rfl

/-- The record port of `Record(MultiExtract, U)`. -/
@[simp]
theorem withRecordME_U_inr (u : Unit) :
    (E.withRecordME ME code bot U hU).U (.inr u) = recordMEUnitary ME U :=
  rfl

/-- The two record worlds start in the same state. -/
theorem withRecord_init :
    (E.withRecord ME code bot U hU).init = (E.withRecordME ME code bot U hU).init :=
  rfl

end VCOracle

/-! ## The random-oracle model -/

/-- **The random-oracle model as an emulated oracle** (ePrint 2025/2166, p. 28): a trivial
private register, with port `i` answered by `|x, y⟩ ↦ |x, y + H i x⟩`. -/
@[expose]
noncomputable def romVCOracle (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (H : Fin k → X → Y) : VCOracle k X Y where
  S := QReg.of Unit
  init := SubState.basis ()
  U i := oracleUnitary (H i) ⊗ₖ (1 : Matrix Unit Unit ℂ)
  unitary i := kronecker_mem_unitary (oracleUnitary_mem_unitaryGroup (H i)) (one_mem _)
  classicalRead := {
    A := fun x a ↦ if a = some (H x.1 x.2) then 1 else 0
    hermitian := by intros; split_ifs <;> simp
    orthogonal := by
      intro x a b
      by_cases ha : a = some (H x.1 x.2) <;>
        by_cases hb : b = some (H x.1 x.2) <;> simp_all [eq_comm]
    complete := by intro x; simp
    commute_cells := by intros; split_ifs <;> simp
    commute_ordinary := by intros; split_ifs <;> simp }

end Quantum
