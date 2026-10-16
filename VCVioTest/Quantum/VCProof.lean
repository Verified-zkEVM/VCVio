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

Checks of the public interface of `VCVio.Quantum.Oracle.Compressed.Consistency` (eq. (26) of the
notes on ePrint 2025/2166, sharpening Lemma 9.5):

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
abbrev io₁ : List (Bool × ZMod 3) := [(true, 1)]

/-- With one prescribed cell and `N = 3`, the discrepancy is exactly `1 - (2/3)² = 5/9`. -/
example : ‖compressedCheckProjector io₁ - checkProjector (ZMod 3) io₁‖ ^ 2 = 5 / 9 := by
  have h : ConsistentIO io₁ := consistentIO_singleton _
  have hcard : (ioCells io₁).card = 1 := rfl
  rw [l2_opNorm_compressedCheckProjector_sub_sq h, hcard, ZMod.card]
  norm_num

/-- Two different outputs at the same input. -/
abbrev ioBad : List (Bool × ZMod 3) := [(true, 0), (true, 1)]

/-- The prescription `ioBad` is inconsistent. -/
theorem not_consistentIO_ioBad : ¬ ConsistentIO ioBad := fun h ↦
  absurd (h (true, 0) (by simp) (true, 1) (by simp) rfl) (by decide)

/-- An inconsistent prescription has zero projector. -/
example : checkProjector (ZMod 3) ioBad = 0 :=
  checkProjector_eq_zero_of_not_consistentIO not_consistentIO_ioBad

/-- An inconsistent prescription has zero compressed projector. -/
example : compressedCheckProjector ioBad = 0 :=
  compressedCheckProjector_eq_zero_of_not_consistentIO not_consistentIO_ioBad

/-- The empty prescription: both projectors are the identity. -/
example : compressedCheckProjector ([] : List (Bool × ZMod 3)) -
    checkProjector (ZMod 3) ([] : List (Bool × ZMod 3)) = 0 := by
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

end lemma92

section lemma93

variable {Msg : Type} {ℓ : Fin 2 → ℕ} {Td Pf : Fin 2 → Type}
  {VC : ∀ i, VectorCommitment Bool (ZMod 3) Msg Bool (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)
  (ME : MultiExtractor 2 Bool (DmOf ℓ Msg Td) (compressedVCOracle 2 Bool (ZMod 3)).S)
  (code : TpDCode 2 (DmOf ℓ Msg Td) (ZMod 2)) {tdBot : ∀ i, Td i}
  {Pgood : Set (Database Bool (ZMod 3))}

/-- Lemma 9.3 with the exact error `1 - (1 - 1/3)^{2 n q2}` for two compressed oracles. -/
example (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{0, 0} VC (compressedVCOracle 2 Bool (ZMod 3)) ME code
      fun _ _ _ n ↦ ENNReal.ofReal (1 - (1 - (3 : ℝ)⁻¹) ^ (2 * n * q2 io)) :=
  extractionCorrect_compressedVCOracle io ME code hC

/-- Lemma 9.3 with the leading-order error `2 n q2 / 3`. -/
example (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{0, 0} VC (compressedVCOracle 2 Bool (ZMod 3)) ME code
      fun _ _ _ n ↦ (2 * n * q2 io : ℝ≥0∞) / 3 :=
  extractionCorrect_compressedVCOracle_two_mul io ME code hC

/-- Lemma 9.3 with the paper's error `8 n q2 / 3`. -/
example (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{0, 0} VC (compressedVCOracle 2 Bool (ZMod 3)) ME code
      fun _ _ _ n ↦ (8 * n * q2 io : ℝ≥0∞) / 3 :=
  extractionCorrect_compressedVCOracle_eight_mul io ME code hC

end lemma93

end VCVioTest.QuantumVCProof
