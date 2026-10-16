/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Proof.Offline

/-!
# Local potential and charged-certificate tests

Numerical calibrations of bounds-note (NOTE) equations (77), (89), and (107) in NOTE's
refinement of ePrint 2025/2166 §9.3's collision-event argument (Lemma 9.6,
p. 61; event bound, pp. 64–65):
a singleton flip in an answer space of size 64, a three-coefficient instance with nonzero
restriction error, and a two-call certificate with original mass one and bound `19/128`.
The tests cover the abstract certificate and the concrete old-oracle collision theorem,
with no local trace hypotheses in the concrete applications. They include the zero-query
case and unrestricted programs using ordinary, extraction, and recording ports.
-/

public section

open Quantum Matrix
open scoped ComplexOrder ENNReal Kronecker

namespace VCVioTest.QuantumVCOffline

/-- Equation (77), with `α = 3`, `β = 15/2`, and one changing answer among 64. -/
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

end VCVioTest.QuantumVCOffline
