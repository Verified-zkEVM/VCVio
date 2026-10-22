/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Merkle.Offline

public import VCVio.Quantum.VC.Proof.GoodEvent

/-!
# Collision certificates and good-event bounds

Numerical calibrations cover a singleton flip among 64 answers, a three-coefficient
instance with nonzero restriction error, and a two-call collision certificate with
ordinary mass one and bound `19/128`.

The public-import tests cover zero queries, substates, coherent ports, and the generic
good-event facade. The collision estimate and the instability estimate use the same
post-adversary bad-event projector.
-/

public section

open Quantum Matrix
open scoped ComplexOrder ENNReal Kronecker

namespace VCVioTest.QuantumVCOffline

/-- The identity-register equality accepts its original fully explicit argument order. -/
example : familyCollisionMatrix (k := 1) (X := Unit) (Y := Bool) (R := Unit) =
    familyCollisionProjector (k := 1) (X := Unit) (Y := Bool) ⊗ₖ (1 : Matrix Unit Unit ℂ) :=
  @Quantum.familyCollisionMatrix_eq_kronecker 1 Unit Bool inferInstance inferInstance
    Unit inferInstance

/-- Extraction commutation accepts its original fully explicit argument order. -/
example {k : ℕ} {X Y Cm Z : Type} [Fintype X] {Dm : Fin k → Type}
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Cm] [DecidableEq Cm]
    [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)
    (f : (Fin k → Database X Y) → ℂ) :
    ((1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ diagonal f) *
        extractUnitary ME code =
      extractUnitary ME code * ((1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
        diagonal f) :=
  @Quantum.extractUnitary_commute_diagonal k X Y Cm Z inferInstance Dm inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance ME code f

/-- A singleton answer flip among 64 answers satisfies the cell bound with coefficients
`3` and `15/2`. -/
example (χ : AddChar (ZMod 64) ℂ) :
    ((1 / 64 : ℝ) • cellDiag 3 (15 / 2) -
      (flipCell {0} * phaseCell (ZMod 64) χ - phaseCell (ZMod 64) χ * flipCell {0})ᴴ *
        (flipCell {0} * phaseCell (ZMod 64) χ -
          phaseCell (ZMod 64) χ * flipCell {0})).PosSemidef := by
  apply posSemidef_smul_cellDiag_sub_flip χ {0} (by norm_num) (by norm_num) (by norm_num)
  norm_num [LeakBound, ZMod.card]

/-- The three-coefficient calibration uses rate `5/96`, with coefficients `1, 2, 3`. -/
example : PhaseLeakBound (5 / 96) 1 2 1 (1 / 64) := by norm_num [PhaseLeakBound]

/-- The positive phase coefficient gives a nonzero, explicitly checked restriction error. -/
example (χ : AddChar (ZMod 64) ℂ) :
    ((5 / 48 : ℝ) • (cellDiag 1 2 +
        (phaseCell (ZMod 64) χ)ᴴ * cellEmpty * phaseCell (ZMod 64) χ) +
      (5 / 3072 : ℝ) • 1 -
      (flipCell {0} * phaseCell (ZMod 64) χ - phaseCell (ZMod 64) χ * flipCell {0})ᴴ *
        (flipCell {0} * phaseCell (ZMod 64) χ -
          phaseCell (ZMod 64) χ * flipCell {0})).PosSemidef := by
  have h := posSemidef_cellDrop_sub_flip χ ({0} : Finset (ZMod 64))
    (lam := 5 / 96) (a₀ := 1) (a₁ := 2) (d := 1) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [PhaseLeakBound, ZMod.card])
  norm_num [ZMod.card] at h ⊢
  exact h

/-- The quadratic schedule is nontrivial halfway through six calls. -/
example : collisionPotential 6 3 3 = 3 := by norm_num [collisionPotential]

/-- Two calls and original mass one give the finite bound `19/128`, for 64 answers. -/
example : (∑ n ∈ Finset.range 2, collisionRate 2 n 64) *
    ((2 : ℝ) / 2 * min 1 2) = 19 / 128 := by
  have h := sum_collisionRate_mul_charge (by decide : 0 < 2) 64 1
  norm_num at h ⊢
  exact h

section Runtime

variable {spec : QuantumOracleSpec} {L : LocalSig} (I : L.Interp)
  {X : QReg → Type*} {A D : QReg} {Z : Type*} [Fintype Z]
  {s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  {Q : Matrix D D ℂ}

/-- The public runtime certificate elaborates at the nontrivial bound `19/128` without
restricting the program's local instruments or intermediate register dimensions. -/
example (hU : ∀ i r, (s i).branch r = MatrixMap.conj (U i r))
    (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (σ₀ : SubState D)
    (x : QuantumComp L spec X A) {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (ports : Finset spec.Port) (hports : ∀ i ∉ ports, b i = 0)
    (hcount : ∑ i ∈ ports, b i ≤ 2) (K : ℕ → Matrix Z D ℂ)
    (δ : ℕ → ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞)
    (mass : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞)
    (hdrop : ∀ n < 2, ∀ i σ, σ.PosSemidef →
      δ n i σ + ∑' r, QuantumRuntime.potential (K (n + 1)) ((s i).branch r σ) ≤
        QuantumRuntime.potential (K n) σ + mass i σ)
    (hleak : ∀ n < 2, ∀ i σ, σ.PosSemidef →
      ∑' r, ENNReal.ofReal (MatrixMap.conj ((1 ⊗ₖ Q) * U i r -
        U i r * (1 ⊗ₖ Q)) σ).trace.re ≤ ENNReal.ofReal (collisionRate 2 n 64) * δ n i σ)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef)
    (hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ = 0)
    (hinit : QuantumRuntime.potential (K 0) ρ = 0)
    (hmass : ∑ n ∈ Finset.range 2,
      (QuantumRuntime.mk D σ₀ s).queryWeight I mass x ρ n ≤ 1) :
    (QuantumRuntime.mk D σ₀ s).eventWeight I Q x ρ ≤ 19 / 128 := by
  have h := QuantumRuntime.eventWeight_le_of_collisionCertificate I hU hQ hQQ σ₀ x hx
    ports hports (by decide : 0 < 2) hcount 64 (by norm_num) K δ mass
    (by simpa using hdrop) hleak hρ hρQ hinit 1 (by simpa using hmass)
  norm_num [ENNReal.ofReal_div_of_pos] at h
  exact h

end Runtime


section Concrete

open Quantum.EmulatedOracle

variable (ME : MultiExtractor 1 Unit (fun _ ↦ Unit) (Fin 1 → Database Bool (ZMod 64)))
  (code : TpDCode 1 (fun _ ↦ Unit) (ZMod 2))
  (V : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hV : V ∈ unitaryGroup _ ℂ)
  {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}

/-- The unconditional theorem gives `19/128` for a two-call, mass-one program on 64 answers. -/
example (x : QuantumComp L (cohSpec (recIn 1 Bool (ZMod 64) Unit (ZMod 2) Bool)) W A)
    (hx : x.IsQueryBound (fun _ ↦ 2)) (ρ : SubState A)
    (hmass : ∑ i : Fin 1,
      ((compressedVCOracle 1 Bool (ZMod 64)).withRecord ME code false V hV).totalMass I x
        (ρ.matrix ⊗ₖ
          ((compressedVCOracle 1 Bool (ZMod 64)).withRecord ME code false V hV).init.matrix)
        (.inl (.inl i)) = 1) :
    let E := (compressedVCOracle 1 Bool (ZMod 64)).withRecord ME code false V hV
    E.coherent.toRuntime.eventWeight I
      (familyCollisionMatrix (k := 1) (X := Bool) (Y := ZMod 64)
        (R := RecReg 1 Unit (fun _ ↦ Unit) Bool)) x (ρ.matrix ⊗ₖ E.init.matrix) ≤ 19 / 128 := by
  have h := collisionEvent_compressedVCOracle_le ME code false V hV I x hx ρ
  dsimp only at h
  rw [hmass] at h
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

/-- No oracle queries gives exactly zero collision weight, without a positivity premise on t. -/
example (x : QuantumComp L (cohSpec (recIn 1 Bool (ZMod 64) Unit (ZMod 2) Bool)) W A)
    (hx : x.IsQueryBound (fun _ ↦ 0)) (ρ : SubState A) :
    let E := (compressedVCOracle 1 Bool (ZMod 64)).withRecord ME code false V hV
    E.coherent.toRuntime.eventWeight I
      (familyCollisionMatrix (k := 1) (X := Bool) (Y := ZMod 64)
        (R := RecReg 1 Unit (fun _ ↦ Unit) Bool)) x (ρ.matrix ⊗ₖ E.init.matrix) = 0 := by
  apply le_antisymm ?_ zero_le
  have h := collisionEvent_compressedVCOracle_le ME code false V hV I x hx ρ
  simpa only [Nat.cast_zero, mul_zero, zero_div, ENNReal.ofReal_zero, zero_mul] using h

end Concrete


section GoodEvent

open Quantum.EmulatedOracle OracleSpec

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm]
  [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)
  {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}

/-- The generic event bound elaborates through ordinary imports with arbitrary codes,
substates, and coherent ordinary/extraction programs. -/
example [UniformAnswerMeasure (X →ₒ Y)] (Pgood : Set (Database X Y))
    [DecidablePred (· ∈ Pgood)] (hgood : Database.empty ∈ Pgood)
    (x : QuantumComp L (cohSpec (extIn k X Y Cm Z)) W A)
    {t : ℕ} (hx : x.IsQueryBound (fun _ ↦ t)) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    let σ := ρ.matrix ⊗ₖ E.init.matrix
    E.coherent.toRuntime.eventWeight I (familyBadProjector (k := k) Pgood) x σ ≤
      24 * t * min (∑ i : Fin k, E.totalMass I x σ (.inl i)) t *
        Database.instability (offlineLabel Pgood) t :=
  badEvent_compressedWithExtract_le ME code Pgood hgood I x hx ρ

/-- The sharp collision bound supplies the same bad-event input as the generic facade. -/
example [DecidablePred (fun D : Database X Y ↦ D.CollisionFree)]
    (x : QuantumComp L (cohSpec (extIn k X Y Cm Z)) W A)
    {t : ℕ} (hx : x.IsQueryBound (fun _ ↦ t)) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    let σ := ρ.matrix ⊗ₖ E.init.matrix
    E.coherent.toRuntime.eventWeight I
        (familyBadProjector (k := k) {D : Database X Y | D.CollisionFree}) x σ ≤
      ENNReal.ofReal ((7 * t + 5) * t / (4 * (Fintype.card Y : ℝ))) *
        min (∑ i : Fin k, E.totalMass I x σ (.inl i)) t := by
  dsimp only
  rw [familyBadProjector_collisionFree]
  exact collisionEvent_compressedWithExtract_le ME code I x hx ρ

/-- A zero-call substate has no bad weight for any good set containing the empty database. -/
example [UniformAnswerMeasure (X →ₒ Y)] (Pgood : Set (Database X Y))
    [DecidablePred (· ∈ Pgood)] (hgood : Database.empty ∈ Pgood)
    (x : QuantumComp L (cohSpec (extIn k X Y Cm Z)) W A)
    (hx : x.IsQueryBound (fun _ ↦ 0)) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    E.coherent.toRuntime.eventWeight I (familyBadProjector (k := k) Pgood) x
      (ρ.matrix ⊗ₖ E.init.matrix) = 0 := by
  apply le_antisymm ?_ zero_le
  have h := badEvent_compressedWithExtract_le ME code Pgood hgood I x hx ρ
  simpa only [Nat.cast_zero, mul_zero, zero_mul] using h

end GoodEvent

/-! ## A finite ordinary/extraction execution -/

namespace FinitePrefix

open Quantum.EmulatedOracle

local notation "Bit" => Fin 2
local notation "DB" => Fin 1 → Database Unit Bit
local notation "Z" => ZMod (Fintype.card (TpD 1 (fun _ ↦ Unit)) + 1)
local notation "Sig" => uSpec (Fin 1 ⊕ Unit) (extIn 1 Unit Bit Unit Z)
local notation "O" => QuantumOracleSpec.In Sig (Sum.inl 0)
local notation "EReg" => QuantumOracleSpec.In Sig (Sum.inr ())
local notation "A" => QReg.of (O × EReg)

noncomputable def extractor : MultiExtractor 1 Unit (fun _ ↦ Unit) DB :=
  ⟨fun _ _ _ ↦ ()⟩

noncomputable def encoding : TpDCode 1 (fun _ ↦ Unit) Z := .ofFintype

@[expose, reducible]
noncomputable def oracle := (compressedVCOracle 1 Unit Bit).withExtract extractor encoding

/-- One extraction call, with the ordinary register retained as a spectator. -/
noncomputable def extractCall : QuantumComp LocalSig.instruments Sig (fun _ ↦ Unit) A :=
  .queryBind (.inr ()) O (Equiv.prodComm _ _) (fun _ ↦ .pure ())

/-- An ordinary call followed by an extraction call. -/
noncomputable def twoCalls : QuantumComp LocalSig.instruments Sig (fun _ ↦ Unit) A :=
  .queryBind (.inl 0) EReg (Equiv.refl _) (fun _ ↦ extractCall)

/-- The two syntactic calls each spend their own port budget. -/
theorem prefix_budget : twoCalls.IsQueryBound (fun _ ↦ 1) := by
  classical
  rw [twoCalls, QuantumComp.isQueryBound_queryBind_iff]
  refine ⟨by decide, fun _ ↦ ?_⟩
  rw [extractCall, QuantumComp.isQueryBound_queryBind_iff]
  exact ⟨by simp, fun _ ↦ QuantumComp.isQueryBound_pure _ _⟩

/-- On the singleton coherent port, extraction is included in the total budget of two. -/
theorem coherent_budget : twoCalls.toCoherent.IsQueryBound (fun _ ↦ 2) := by
  simpa using QuantumComp.isQueryBound_toCoherent prefix_budget

/-- A zero budget cannot hide the extraction call. -/
example : ¬ extractCall.IsQueryBound (fun _ ↦ 0) := by
  classical
  rw [extractCall, QuantumComp.isQueryBound_queryBind_iff]
  simp

/-- Extraction charges no ordinary mass, even on a nonzero private input. -/
theorem extraction_ordinary_mass (σ : Matrix (A × oracle.S) (A × oracle.S) ℂ) :
    oracle.totalMass .instruments extractCall.toCoherent σ (.inl 0) = 0 := by
  rw [EmulatedOracle.totalMass_toCoherent, extractCall,
    QuantumRuntime.queryMass_queryBind_of_ne _ _ (by decide)]
  simp

/-- The ordinary mass of the twoCalls is exactly its input trace. -/
theorem prefix_ordinary_mass (σ : Matrix (A × oracle.S) (A × oracle.S) ℂ) :
    oracle.totalMass .instruments twoCalls.toCoherent σ (.inl 0) =
      ENNReal.ofReal σ.trace.re := by
  rw [EmulatedOracle.totalMass_toCoherent, twoCalls,
    QuantumRuntime.queryMass_queryBind_self]
  simp only [← EmulatedOracle.totalMass_toCoherent, extraction_ordinary_mass,
    tsum_zero, add_zero]

/-- Extraction itself spends one call on its full incoming trace. -/
theorem extraction_mass (σ : Matrix (A × oracle.S) (A × oracle.S) ℂ) :
    oracle.totalMass .instruments extractCall.toCoherent σ (.inr ()) =
      ENNReal.ofReal σ.trace.re := by
  rw [EmulatedOracle.totalMass_toCoherent, extractCall,
    QuantumRuntime.queryMass_queryBind_self]
  simp

noncomputable def seed : A :=
  (((), 0), (TpIC.full (by decide) (fun _ ↦ 0) (fun _ ↦ ()), 0))

/-- A proper substate of trace one half starts with empty oracle databases. -/
noncomputable def initial : SubState A where
  matrix := (1 / 2 : ℝ) • (SubState.basis seed).matrix
  posSemidef := (SubState.basis seed).posSemidef.smul (by norm_num)
  trace_re_le_one := by rw [Matrix.trace_smul, SubState.trace_basis]; norm_num

noncomputable def joint : Matrix (A × oracle.S) (A × oracle.S) ℂ :=
  initial.matrix ⊗ₖ oracle.init.matrix

theorem joint_trace : joint.trace.re = 1 / 2 := by
  have hi : oracle.init.matrix.trace = 1 := SubState.trace_basis _
  rw [joint, Matrix.trace_kronecker, hi, mul_one]
  change (((1 / 2 : ℝ) • (SubState.basis seed).matrix).trace).re = _
  rw [Matrix.trace_smul, SubState.trace_basis]
  norm_num

/-- The independently computed ordinary mass is one half. -/
example : oracle.totalMass .instruments twoCalls.toCoherent joint (.inl 0) = 1 / 2 := by
  rw [prefix_ordinary_mass, joint_trace]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- The extraction call has the same positive mass, in addition to the ordinary call. -/
theorem prefix_extraction_mass :
    oracle.totalMass .instruments twoCalls.toCoherent joint (.inr ()) = 1 / 2 := by
  rw [EmulatedOracle.totalMass_toCoherent, twoCalls,
    QuantumRuntime.queryMass_queryBind_of_ne _ _ (by decide)]
  simp only [← EmulatedOracle.totalMass_toCoherent, extraction_mass, tsum_fintype,
    Fintype.sum_unique]
  have ht := (oracle.toRuntime.lossless_queryStep (oracle.lossless_toRuntime_step (.inl 0))
    EReg (Equiv.refl _)).tsum_trace_eq joint
  simp only [tsum_fintype, Fintype.sum_unique] at ht
  rw [ht, joint_trace]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- Extraction preserves the weight of the nonempty-database event on every incoming state. -/
theorem extraction_preserves_event
    (σ : Matrix ((TpIC 1 Unit × Z) × DB) ((TpIC 1 Unit × Z) × DB) ℂ) :
    let Q := (1 : Matrix (TpIC 1 Unit × Z) (TpIC 1 Unit × Z) ℂ) ⊗ₖ
      familyBadProjector (k := 1) ({Database.empty} : Set (Database Unit Bit))
    (MatrixMap.conj Q (MatrixMap.conj (extractUnitary extractor encoding) σ)).trace =
      (MatrixMap.conj Q σ).trace := by
  classical
  dsimp only
  unfold familyBadProjector labelProjector
  have hc := extractUnitary_commute_diagonal extractor encoding
    (fun d ↦ if decide (∀ i, d i ∈ ({Database.empty} : Set (Database Unit Bit))) = false
      then (1 : ℂ) else 0)
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, hc, MatrixMap.conj_mul,
    LinearMap.comp_apply]
  exact MatrixMap.isTP_conj
    (mem_unitaryGroup_iff'.mp (extractUnitary_mem_unitaryGroup extractor encoding)) _

/-- A single ordinary query from the empty cell has a nonzero amplitude on a populated cell. -/
theorem populated_amplitude :
    compressedOracle Unit Bit (((), 0), fun _ ↦ some 0) (((), 0), Database.empty) =
      (1 / 2 : ℂ) * cellAmp Bit := by
  have h := congrFun (compressedOracle_mulVec_single_of_eq_none
    (X := Unit) (0 : Bit) (Database.empty_apply (Y := Bit) ()))
    (((), (0 : Bit)), fun _ ↦ some (0 : Bit))
  rw [Matrix.mulVec_single_one] at h
  norm_num [Fin.sum_univ_two, Pi.single_apply, funext_iff] at h ⊢
  exact h

noncomputable def ordinary : Matrix ((Unit × Bit) × DB) ((Unit × Bit) × DB) ℂ :=
  (compressedVCOracle 1 Unit Bit).U 0

/-- The bad projection retains the populated output amplitude of the ordinary port. -/
theorem populated_bad_amplitude :
    (((1 : Matrix (Unit × Bit) (Unit × Bit) ℂ) ⊗ₖ
      familyBadProjector (k := 1) ({Database.empty} : Set (Database Unit Bit))) *
      ordinary)
        (((), 0), fun _ _ ↦ some 0) (((), 0), fun _ ↦ Database.empty) =
          (1 / 2 : ℂ) * cellAmp Bit := by
  classical
  have hs : (fun j : {j : Fin 1 // j ≠ 0} ↦ (fun _ : Unit ↦ some (0 : Bit))) =
      (fun _ ↦ (Database.empty : Database Unit Bit)) := by
    funext j
    exact False.elim (j.2 (Subsingleton.elim _ _))
  have hn : (fun _ : Unit ↦ some (0 : Bit)) ≠ Database.empty := by
    intro he
    have := congrFun he ()
    contradiction
  simp only [familyBadProjector, labelProjector, ← diagonal_one,
    diagonal_kronecker_diagonal, diagonal_mul, one_mul]
  simp only [ordinary, compressedVCOracle, onFactor_apply, splitAt_apply]
  simp [hn, hs, populated_amplitude]

/-- On a half-trace empty input, the bad event after the ordinary call has a positive
populated diagonal entry of one sixteenth. -/
theorem populated_bad_diagonal :
    let Q := (1 : Matrix (Unit × Bit) (Unit × Bit) ℂ) ⊗ₖ
      familyBadProjector (k := 1) ({Database.empty} : Set (Database Unit Bit))
    let σ := Matrix.single (((), (0 : Bit)), (fun _ : Fin 1 ↦ Database.empty))
      (((), (0 : Bit)), (fun _ : Fin 1 ↦ Database.empty)) (1 / 2 : ℂ)
    (MatrixMap.conj Q (MatrixMap.conj ordinary σ)
      (((), 0), fun _ _ ↦ some 0) (((), 0), fun _ _ ↦ some 0)).re = 1 / 16 := by
  classical
  dsimp only
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul]
  let K : Matrix ((Unit × Bit) × DB) ((Unit × Bit) × DB) ℂ :=
    (1 ⊗ₖ familyBadProjector (k := 1) ({Database.empty} : Set (Database Unit Bit))) * ordinary
  let s : (Unit × Bit) × DB := (((), 0), fun _ ↦ Database.empty)
  let a : (Unit × Bit) × DB := (((), 0), fun _ _ ↦ some 0)
  change (MatrixMap.conj K (Matrix.single s s (1 / 2)) a a).re = _
  have hk : K a s = (1 / 2 : ℂ) * cellAmp Bit := populated_bad_amplitude
  simp only [MatrixMap.conj_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single s (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp),
    Finset.sum_eq_single s (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
  simp only [and_self, ite_true, hk]
  norm_num [cellAmp, Complex.mul_re, Complex.mul_im]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The ordinary step of the fixture creates strictly positive bad-event weight from
its half-trace empty input. -/
theorem ordinary_bad_weight_pos :
    let Q := (1 : Matrix (Unit × Bit) (Unit × Bit) ℂ) ⊗ₖ
      familyBadProjector (k := 1) ({Database.empty} : Set (Database Unit Bit))
    let σ := Matrix.single (((), (0 : Bit)), (fun _ : Fin 1 ↦ Database.empty))
      (((), (0 : Bit)), (fun _ : Fin 1 ↦ Database.empty)) (1 / 2 : ℂ)
    0 < ENNReal.ofReal (MatrixMap.conj Q (MatrixMap.conj ordinary σ)).trace.re := by
  classical
  dsimp only
  let s : (Unit × Bit) × DB := (((), 0), fun _ ↦ Database.empty)
  let σ := Matrix.single s s (1 / 2 : ℂ)
  let Q := (1 : Matrix (Unit × Bit) (Unit × Bit) ℂ) ⊗ₖ
    familyBadProjector (k := 1) ({Database.empty} : Set (Database Unit Bit))
  let τ := MatrixMap.conj Q (MatrixMap.conj ordinary σ)
  have hs : σ.PosSemidef := by
    simpa [σ, SubState.matrix_basis, Matrix.smul_single] using
      (SubState.basis s).posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have ht : τ.PosSemidef :=
    (MatrixMap.isCP_conj Q).posSemidef ((MatrixMap.isCP_conj ordinary).posSemidef hs)
  apply ENNReal.ofReal_pos.mpr
  change 0 < τ.trace.re
  have hdiag : (τ (((), 0), fun _ _ ↦ some 0) (((), 0), fun _ _ ↦ some 0)).re = 1 / 16 :=
    populated_bad_diagonal
  have hle : (τ (((), 0), fun _ _ ↦ some 0) (((), 0), fun _ _ ↦ some 0)).re ≤
      τ.trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    exact Finset.single_le_sum (f := fun a ↦ (τ a a).re)
      (fun a _ ↦ (Complex.nonneg_iff.mp (ht.diag_nonneg (i := a))).1)
      (Finset.mem_univ (((), 0), fun _ _ ↦ some 0))
  rw [hdiag] at hle
  linarith

end FinitePrefix

end VCVioTest.QuantumVCOffline

namespace VCVioTest.QuantumVCOffline

open Quantum Matrix OracleComp
open scoped Kronecker

section CheckedChallenger

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm]
  [Fintype Z] [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
  (VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i))
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
  (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)

open scoped Classical in
/-- Fresh extraction through an arbitrary code measures its actual extraction fibre. -/
example (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
    (((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run₂ .instruments
      (extractQuery code B (TpIC.full hk c.idx c.cm))).branch (some tdm) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ extractProj ME (TpIC.full hk c.idx c.cm) tdm) := by
  classical
  exact run₂_extractQuery_branch (compressedVCOracle k X Y) ME code B
    (TpIC.full hk c.idx c.cm) tdm

open scoped Classical in
/-- Rejecting the first checked batch annihilates the retained mismatch branch. -/
example (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
      (offlineInstrument VC code hk qs c B)).branch ((false, some tdm, true), true) = 0 := by
  apply run₂_offlineInstrument_reject
  simp

open scoped Classical in
/-- Exceeding the opening budget annihilates the actual challenger's event. -/
example (ρ : SubState (B × (Fin k → Database X Y)))
    (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
      (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true} = 0 :=
  offlineChallenger_over_budget VC code
    ((compressedVCOracle k X Y).mixedExtractRuntime ME code) hk qs c B ρ hq

open scoped Classical in
/-- Every supported randomized opening is retained in the good-database zero identity. -/
example (io : ∀ i, (VC i).NonadaptiveCheck) (tdBot : ∀ i, Td i)
    (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]
    (hC : Conditions VC io ME tdBot Pgood)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    let K := checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf *
      extractProj ME (TpIC.full hk c.idx c.cm) tdm *
      checkPassProjector io c.W c.idx c.cm c.ans c.pf *
      diagonal (fun D : Fin k → Database X Y ↦ if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (R.run₂ .instruments (offlineFinish VC (Z := Z) hk qs c B
      (true, some tdm, true))).branch true ∘ₗ
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ K) = 0 := by
  classical
  exact run₂_offlineFinish_partial_good_zero io ME tdBot Pgood hC code hk qs c B tdm

open scoped Classical in
/-- The generic offline endpoint is available through ordinary public imports. -/
example [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (io : ∀ i, (VC i).NonadaptiveCheck) (tdBot : ∀ i, Td i)
    (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]
    (hC : Conditions VC io ME tdBot Pgood) :
    OfflineExtractable VC (compressedVCOracle k X Y) ME code
      (fun t wVC _ qs ↦ offlineError io Pgood t wVC qs) :=
  offlineExtractable_compressedVCOracle io ME tdBot Pgood hC code

end CheckedChallenger
end VCVioTest.QuantumVCOffline

/-- Accepted labels remain a subinstrument with an infinite outcome space. -/
example : MatrixMap.IsCPTNIFamily (fun i : ℕ ↦ MatrixMap.conj
    (Matrix.diagonal fun _ : Fin 2 ↦ if True ∧ (0 : ℕ) = i then (1 : ℂ) else 0)) :=
  MatrixMap.accepted_label_isCPTNIFamily (fun _ ↦ True) (fun _ ↦ 0)

namespace VCVioTest.OfflineFixture

open Quantum Matrix OracleComp
open scoped ENNReal Kronecker

local notation "Dm" => DmOf (k := 1) (fun _ ↦ 1) Unit (fun _ ↦ Bool)
local notation "DB" => Fin 1 → Database Unit (Fin 2)

/-- A uniform binary opening; the submitted proof is the zero outcome. -/
def vc : VectorCommitment Unit (Fin 2) Unit Unit Bool (Fin 2) 1 where
  commit _ := pure ((), false)
  opening _ _ := query (spec := unifSpec) 1
  check _ _ pf := pure (pf == 0)

def claim : OpeningClaim 1 Unit Unit (fun _ ↦ 1) (fun _ ↦ Fin 2) where
  idx := id
  cm := fun _ ↦ ()
  ans := fun _ _ ↦ some ()
  pf := fun _ ↦ 0
  W := Finset.univ

def tuple (b : Bool) : TpDLen 1 Dm (.full (by decide)) :=
  fun _ ↦ (fun _ ↦ some (), b)

/-- Extraction records whether the selected cell contains a value. -/
noncomputable def extractor : MultiExtractor 1 Unit Dm DB :=
  ⟨fun tic D i ↦ (fun _ ↦ some (), (D ((tic.2 i).1) ()).isSome)⟩

def db (b : Bool) : DB := fun _ _ ↦ if b then some 0 else none

example (pf : Fin 2) : pf ∈ support (vc.opening Finset.univ false) := by
  simp [vc]

example : ∑ i, ((claim.ans i).dom.card) = 1 := by decide

variable {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (code : TpDCode 1 Dm Z)

/-- The two measured fibres select opposite basis states. -/
private theorem fibre_entry (b out : Bool) :
    (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
      extractProj extractor (TpIC.full (show 1 ≤ 1 by decide) claim.idx claim.cm) (tuple out))
      (Matrix.single ((), db b) ((), db b) 1)) ((), db b) ((), db b) =
        if b = out then 1 else 0 := by
  classical
  rw [MatrixMap.conj_apply]
  simp only [extractProj, ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
    one_mul, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.single_apply_same]
  have he : extractor.extract (TpIC.full (show 1 ≤ 1 by decide) claim.idx claim.cm)
      (db b) = tuple b := by cases b <;> rfl
  have hi : Function.Injective tuple := by
    intro a b h
    exact congrArg (fun f ↦ (f (0 : Fin 1)).2) h
  simp only [Pi.star_apply]
  erw [he]
  by_cases h : b = out
  · subst out
    erw [ite_eq_left (rfl : tuple b = tuple b)]
    norm_num
  · have hn : tuple b ≠ tuple out := fun hh ↦ h (hi hh)
    erw [ite_eq_right hn]
    norm_num [h]

/-- Fresh extraction distinguishes empty and occupied states for every tuple code. -/
example (b out : Bool) :
    let R := ((compressedVCOracle 1 Unit (Fin 2)).withExtract extractor code).coherent.toRuntime
    ((R.run₂ .instruments (extractQuery code (QReg.of Unit)
      (TpIC.full (by decide) claim.idx claim.cm))).branch (some (tuple out))
        (SubState.basis ((), db b)).matrix) ((), db b) ((), db b) =
      if b = out then 1 else 0 := by
  classical
  dsimp only
  erw [run₂_extractQuery_branch]
  convert fibre_entry b out using 1
  rfl

omit [AddGroup Z] in
/-- Every opening branch has weight one half and leaves the state untouched. -/
theorem opening_branch (R : QuantumRuntime (mixedExtSpec 1 Unit (Fin 2) Unit Z))
    (B : QReg) (pf : Fin 2) :
    (R.run₂ .instruments (openAt (fun _ : Fin 1 ↦ vc) B 0 Finset.univ false)).branch pf =
      (1 / 2 : ℂ) • LinearMap.id := by
  rw [openAt]
  change (R.run₂ .instruments ((query (spec := unifSpec) 1 : ProbComp (Fin 2)).toQuantumAt
    (QComp.coinImpl _ B))).branch pf = _
  change (R.run₂ .instruments (((query (spec := unifSpec) 1 >>= pure) :
    ProbComp (Fin 2)).toQuantumAt (QComp.coinImpl _ B))).branch pf = _
  erw [toQuantumAt_query_bind]
  simp only [toQuantumAt_pure, QuantumComp₂.bind_pure]
  rw [QComp.coinImpl, QuantumRuntime.run₂_act, SubInstrument.bind_pure,
    DSubInstrument.branch_frame_apply]
  ext ρ x y
  simp [SubInstrument.branch_uniform_apply]

omit [AddGroup Z] in
/-- On the accepted transcript, the fresh binary opening alone decides the mismatch. -/
theorem finish_eq (B : QReg) :
    offlineFinish (fun _ : Fin 1 ↦ vc) (Z := Z) (by decide) 1 claim B
      (true, some (tuple false), true) =
      (openAt (fun _ : Fin 1 ↦ vc) B 0 Finset.univ false).bind
        (fun pf ↦ .pure (decide (pf ≠ 0))) := by
  rw [offlineFinish_accept]
  simp [QComp.pi, claim, tuple, PartialVec.Agrees, Fin.exists_fin_succ,
    openAt, vc, PartialVec.dom, QuantumComp₂.bind_assoc, Function.injective_id]

omit [AddGroup Z] in
/-- The actual accepted finish assigns exactly half the incoming state to mismatch. -/
theorem mismatch_branch (R : QuantumRuntime (mixedExtSpec 1 Unit (Fin 2) Unit Z))
    (B : QReg) :
    (R.run₂ .instruments (offlineFinish (fun _ : Fin 1 ↦ vc) (Z := Z)
      (by decide) 1 claim B (true, some (tuple false), true))).branch true =
        (1 / 2 : ℂ) • LinearMap.id := by
  rw [finish_eq, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply_univ]
  ext ρ x y
  simp only [QuantumRuntime.run₂_pure, Fin.sum_univ_two]
  erw [opening_branch, opening_branch]
  simp

/-- A normalized basis input therefore has mismatch weight exactly one half. -/
example (R : QuantumRuntime (mixedExtSpec 1 Unit (Fin 2) Unit Z)) (s : R.D) :
    ENNReal.ofReal (((R.run₂ .instruments
      (offlineFinish (fun _ : Fin 1 ↦ vc) (Z := Z) (by decide) 1 claim (QReg.of Unit)
        (true, some (tuple false), true))).branch true
          (SubState.basis ((), s)).matrix).trace.re) = 1 / 2 := by
  rw [mismatch_branch]
  simp

/-- The same submitted proof is rejected when it is changed to the nonzero outcome. -/
example : vc.check () (claim.ans 0) 1 = pure false := rfl

/-- A rejected first batch has zero mismatch channel on this concrete claim. -/
example (R : QuantumRuntime (mixedExtSpec 1 Unit (Fin 2) Unit Z)) :
    (R.run₂ .instruments (offlineFinish (fun _ : Fin 1 ↦ vc) (Z := Z)
      (by decide) 1 { claim with pf := fun _ ↦ 1 } (QReg.of Unit)
      (false, some (tuple false), true))).branch true = 0 := by
  apply run₂_offlineFinish_reject
  simp

/-- The claim opens one position, so a zero budget rejects even an accepted transcript. -/
example (R : QuantumRuntime (mixedExtSpec 1 Unit (Fin 2) Unit Z)) :
    (R.run₂ .instruments (offlineFinish (fun _ : Fin 1 ↦ vc) (Z := Z)
      (by decide) 0 claim (QReg.of Unit) (true, some (tuple false), true))).branch true = 0 := by
  apply run₂_offlineFinish_over_budget
  decide

end VCVioTest.OfflineFixture
