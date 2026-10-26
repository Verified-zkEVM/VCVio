/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Consistency
public import VCVio.Quantum.VC.Proof.Commutativity
public import VCVio.Quantum.VC.Proof.Extraction

/-!
# Tests for the consistency projectors and the proofs of Lemmas 9.2 and 9.3

Checks of the public interface of `VCVio.Quantum.Oracle.Compressed.Consistency`, sharpening
Lemma 9.5 of ePrint 2025/2166:

* the exact discrepancy `‖P̂ - P‖² = 1 - (1 - 1/N)^2` for one prescribed cell, with `N = 3`;
* an inconsistent prescription has both projectors zero;
* the empty prescription has `P = P̂ = 1`.

and elaboration of Lemma 9.2 (`Quantum.comBound_compressedVCOracle`, constant `24`, and the
paper's `80`) and Lemma 9.3 (`Quantum.extractionCorrect_compressedVCOracle`, exact error, and the
paper's `8 n q2 / N`) for two compressed oracles on databases `Bool → Option (ZMod 3)`.
-/

public section

open Quantum Matrix OracleSpec
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace VCVioTest.QuantumVCProof

/-! ## Consistency projectors -/

/-- One prescribed cell, `true ↦ 1`, for databases `Bool → Option (ZMod 3)`. -/
abbrev log₁ : QueryLog (Bool →ₒ ZMod 3) := [⟨true, 1⟩]

/-- With one prescribed cell and `N = 3`, the discrepancy is exactly `1 - (2/3)² = 5/9`. -/
example : ‖compressedCheckProjector log₁ - checkProjector (ZMod 3) log₁‖ ^ 2 = 5 / 9 := by
  have h : log₁.Consistent := QueryLog.consistent_singleton _
  have hcard : (loggedCells log₁).card = 1 := rfl
  rw [l2_opNorm_compressedCheckProjector_sub_sq h, hcard, ZMod.card]
  norm_num

/-- Two different outputs at the same input. -/
abbrev logBad : QueryLog (Bool →ₒ ZMod 3) := [⟨true, 0⟩, ⟨true, 1⟩]

/-- The prescription `logBad` is inconsistent. -/
theorem not_consistent_logBad : ¬ logBad.Consistent := fun h ↦
  absurd (QueryLog.consistent_iff.mp h ⟨true, 0⟩ (by simp) ⟨true, 1⟩ (by simp) rfl)
    (by decide)

/-- An inconsistent prescription has zero projector. -/
example : checkProjector (ZMod 3) logBad = 0 :=
  checkProjector_eq_zero_of_not_consistent not_consistent_logBad

/-- An inconsistent prescription has zero compressed projector. -/
example : compressedCheckProjector logBad = 0 :=
  compressedCheckProjector_eq_zero_of_not_consistent not_consistent_logBad

/-- The empty prescription: both projectors are the identity. -/
example : compressedCheckProjector ([] : QueryLog (Bool →ₒ ZMod 3)) -
    checkProjector (ZMod 3) ([] : QueryLog (Bool →ₒ ZMod 3)) = 0 := by
  simp

/-! ## Lemmas 9.2 and 9.3 on a small instance -/

noncomputable local instance : UniformAnswerMeasure (Bool →ₒ ZMod 3) :=
  UniformAnswerMeasure.ofFiniteNonempty _

section lemma92

variable {Dm : Fin 2 → Type} (ME : MultiExtractor 2 Bool Dm (Fin 2 → Database Bool (ZMod 3)))
  (code : TpDCode 2 Dm (ZMod 2))

/-- Lemma 9.2 with the constant `24` for two compressed oracles. -/
example : ComBound.{0, 0} (compressedVCOracle 2 Bool (ZMod 3)) ME code (comBoundError ME) :=
  comBound_compressedVCOracle ME code

/-- Lemma 9.2 with the paper's constant `80`. -/
example : ComBound.{0, 0} (compressedVCOracle 2 Bool (ZMod 3)) ME code fun t ↦
    80 * ⨆ (j' : Fin 2) (tic : TpIC 2 Bool) (Dfix : Fin 2 → Database Bool (ZMod 3)),
      Database.instability (onlineLabel ME ![tic] Dfix j') (t + 1) :=
  comBound_compressedVCOracle_eighty ME code

/-- An extraction followed by a checked read is a two-call mixed prefix. -/
noncomputable def extractionReadPrefix (Env : QReg) (tic : TpIC 2 Bool) :
    QComp (mixedExtSpec 2 Bool (ZMod 3) Bool (ZMod 2))
      (ReadComOut 2 Bool (ZMod 2) Env) (ReadComOut 2 Bool (ZMod 2) Env) (Option (ZMod 3)) :=
  QuantumComp₂.bind
    (QuantumComp.liftOrdinary (extractQuery code (ReadComOut 2 Bool (ZMod 2) Env) tic))
    fun _ ↦ checkedRead (ReadComOut 2 Bool (ZMod 2) Env) 0 true

/-- Both calls count, and the retained answer can choose the final read address. -/
example (Env : QReg) (tic : TpIC 2 Bool) (ρ : SubState (ReadComOut 2 Bool (ZMod 2) Env)) :
    readComError (compressedVCOracle 2 Bool (ZMod 3)) ME code
      (extractionReadPrefix code Env tic) ρ (fun a ↦ (1, a.isSome)) ≤ comBoundError ME 2 := by
  apply (comBound_compressedVCOracle ME code).2
  unfold extractionReadPrefix QuantumComp₂.bind
  apply QuantumComp.IsTotalQueryBound.bind (n := 1) (m := 1)
  · apply (QuantumComp.isTotalQueryBound_liftOrdinary_iff _ _).mpr
    simp only [extractQuery, QComp.callBasis, QComp.act_bind, QuantumComp₂.primBind]
    apply (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr
    intro _
    unfold QuantumComp₂.bind
    apply QuantumComp.IsTotalQueryBound.bind (n := 1) (m := 0)
    · unfold QuantumComp₂.query QuantumComp.query
      exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩
    · rintro _ ⟨h, r⟩
      subst h
      apply (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr
      exact fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _
  · rintro _ ⟨h, a⟩
    subst h
    simp only [checkedRead, QComp.act_bind, QuantumComp₂.primBind]
    apply (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr
    intro _
    unfold QuantumComp₂.bind
    apply QuantumComp.IsTotalQueryBound.bind (n := 1) (m := 0)
    · unfold QuantumComp₂.query QuantumComp.query
      exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩
    · rintro _ ⟨h, r⟩
      subst h
      apply (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr
      exact fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _

end lemma92

section missingRead

local notation "Q" => compressedReadProjector 2 Bool (ZMod 2)
local notation "Cell" => Fin 2 × Bool
local notation "DB" => Fin 2 → Database Bool (ZMod 2)

/-- The missing-answer branch is a nonzero channel on the full private space. -/
example (c : Cell) : MatrixMap.conj (Q c none) ≠ 0 := by
  have hn : Q c none ≠ 0 := by
    intro hz
    let C := compressDatabases 2 Bool (ZMod 2)
    have he : C * Q c none * C =
        diagonal (fun D : DB ↦ if D c.1 c.2 = none then (1 : ℂ) else 0) := by
      change C * (C * _ * C) * C = _
      calc
        _ = (C * C) * (diagonal fun D : DB ↦
              if D c.1 c.2 = none then (1 : ℂ) else 0) * (C * C) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by simp [C, compressDatabases_mul_self]
    rw [hz, Matrix.mul_zero, Matrix.zero_mul] at he
    have hh := congrArg (fun M ↦ M (fun _ ↦ Database.empty) (fun _ ↦ Database.empty)) he
    simp [Database.empty] at hh
  intro hz
  have hh := LinearMap.congr_fun hz (1 : Matrix DB DB ℂ)
  simp only [MatrixMap.conj_apply, Matrix.mul_one, compressedReadProjector_hermitian,
    compressedReadProjector_orthogonal, ite_true, LinearMap.zero_apply] at hh
  exact hn hh

end missingRead

section lemma93

variable {Msg : Type} {ℓ : Fin 2 → ℕ} {Td Pf : Fin 2 → Type}
  {VC : ∀ i, VectorCommitment Bool (ZMod 3) Msg Bool (Td i) (Pf i) (ℓ i)}
  (chk : ∀ i, (VC i).NonadaptiveCheck)
  (ME : MultiExtractor 2 Bool (DmOf ℓ Msg Td) (compressedVCOracle 2 Bool (ZMod 3)).S)
  (code : TpDCode 2 (DmOf ℓ Msg Td) (ZMod 2)) {tdBot : ∀ i, Td i}
  {Pgood : Set (Database Bool (ZMod 3))}

/-- Lemma 9.3 with the exact error `1 - (1 - 1/3)^{2 n q2}` for two compressed oracles. -/
example (hC : Conditions VC chk ME tdBot Pgood) :
    ExtractionCorrect.{0, 0} VC (compressedVCOracle 2 Bool (ZMod 3)) ME code
      fun _ _ _ n ↦ ENNReal.ofReal (1 - (1 - (3 : ℝ)⁻¹) ^ (2 * n * q2 chk)) :=
  extractionCorrect_compressedVCOracle chk ME code hC

/-- The opening-specific budget gives the same exact acceptance error. -/
example (h : ℕ) (hh : OpeningQueryBound chk h) (hC : Conditions VC chk ME tdBot Pgood) :
    ExtractionCorrect.{0, 0} VC (compressedVCOracle 2 Bool (ZMod 3)) ME code
      fun _ _ _ n ↦ ENNReal.ofReal (1 - (1 - (3 : ℝ)⁻¹) ^ (2 * n * h)) :=
  extractionCorrect_compressedVCOracle_of_openingQueryBound chk ME code h hh hC

/-- Lemma 9.3 with the leading-order error `2 n q2 / 3`. -/
example (hC : Conditions VC chk ME tdBot Pgood) :
    ExtractionCorrect.{0, 0} VC (compressedVCOracle 2 Bool (ZMod 3)) ME code
      fun _ _ _ n ↦ (2 * n * q2 chk : ℝ≥0∞) / 3 :=
  extractionCorrect_compressedVCOracle_two_mul chk ME code hC

/-- Lemma 9.3 with the paper's error `8 n q2 / 3`. -/
example (hC : Conditions VC chk ME tdBot Pgood) :
    ExtractionCorrect.{0, 0} VC (compressedVCOracle 2 Bool (ZMod 3)) ME code
      fun _ _ _ n ↦ (8 * n * q2 chk : ℝ≥0∞) / 3 :=
  extractionCorrect_compressedVCOracle_eight_mul chk ME code hC

end lemma93

end VCVioTest.QuantumVCProof
