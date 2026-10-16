/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Instability
public import VCVio.Quantum.VC.Proof.Commutativity

/-!
# Concrete P2 for salted Merkle extraction

The compressed oracle commutation error is bounded by
`min (4, 24 * min (1, (2s + 1) / |Y|))`. The constant `24` comes from the concrete
online instability bound; `4` is the squared norm bound for a difference of two unitaries.

## References

Chiesa–Di–Hu–Zheng, ePrint 2025/2166: oracle commutativity (Definition 7.3, property 2,
p. 50) and its instability reduction (Lemma 9.2, p. 58), together with Merkle instability
(Lemma 8.8, p. 56). The constant-24/cap-four P2 bound is a strengthened bound proved here;
its formula is not the estimate stated in the paper's Theorem 8.3 (p. 53).
-/

public section

open Quantum Matrix OracleSpec
open scoped ENNReal Matrix.Norms.L2Operator

universe v w

namespace Quantum

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)

/-- The operator norm structure on the joint P2 register with an explicit finite basis. -/
noncomputable local instance comRegisterNormedAddCommGroup (Env : QReg) :
    NormedAddCommGroup (Matrix (ComOut k X Y Cm Z Env × E.S) (ComOut k X Y Cm Z Env × E.S) ℂ) := by
  letI : Fintype (ComOut k X Y Cm Z Env × E.S) := inferInstance
  exact Matrix.instL2OpNormedAddCommGroup

/-- The commutation defect of any two unitary ports has squared operator norm at most four. -/
theorem norm_comDefect_sq_le_four (Env : QReg) (i : Fin k) :
    ‖comDefect E ME code Env i‖ ^ 2 ≤ 4 := by
  classical
  let U := onFactor (slotSnd₃ (X × Y) (TpIC k Cm × Z) Env E.S) (extractUnitary ME code)
  let V := onFactor (slotFst₃ (X × Y) (TpIC k Cm × Z) Env E.S) (E.U i)
  have hU := onFactor_mem_unitaryGroup (slotSnd₃ (X × Y) (TpIC k Cm × Z) Env E.S)
    (extractUnitary_mem_unitaryGroup ME code)
  have hV := onFactor_mem_unitaryGroup (slotFst₃ (X × Y) (TpIC k Cm × Z) Env E.S)
    (E.unitary i)
  have hUV : ‖U * V‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self (mem_unitaryGroup_iff'.mp (mul_mem hU hV))
  have hVU : ‖V * U‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self (mem_unitaryGroup_iff'.mp (mul_mem hV hU))
  have h : ‖U * V - V * U‖ ≤ 2 := (norm_sub_le (U * V) (V * U)).trans (by linarith)
  change ‖U * V - V * U‖ ^ 2 ≤ 4
  nlinarith [norm_nonneg (U * V - V * U)]

/-- The universal P2 cap, valid for mixed states and arbitrary adversarial query bounds. -/
theorem comBound_four : ComBound.{v, w} E ME code (fun _ ↦ 4) := by
  classical
  intro i t A Env α x ρ _
  let σ : α → SubState (ComOut k X Y Cm Z Env × E.S) := fun a ↦
    (E.withExtract ME code).coherent.toRuntime.jointPost₂ .instruments x ρ a
  have hleaf (a : α) :
      ENNReal.ofReal (comDefect E ME code Env i * (σ a).matrix *
        (comDefect E ME code Env i)ᴴ).trace.re ≤
      4 * ENNReal.ofReal (σ a).matrix.trace.re := by
    have h := (MatrixMap.re_trace_conj_le (comDefect E ME code Env i)
      (σ a).posSemidef).trans (mul_le_mul_of_nonneg_right
        (norm_comDefect_sq_le_four E ME code Env i) (σ a).trace_re_nonneg)
    simpa only [MatrixMap.conj_apply, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal h
  calc comError E ME code i x ρ
      ≤ ∑' a, 4 * ENNReal.ofReal (σ a).matrix.trace.re := ENNReal.tsum_le_tsum hleaf
    _ = 4 * ∑' a, ENNReal.ofReal (σ a).matrix.trace.re := ENNReal.tsum_mul_left
    _ ≤ 4 * 1 := by
      gcongr
      exact QuantumRuntime.tsum_jointPost₂_trace_le_one _ _ x ρ
    _ = 4 := mul_one _

end Quantum

namespace SaltedMerkle

variable {Y : Type} [Fintype Y]

/-- The concrete commutation error `C(s)` for salted Merkle extraction. -/
@[expose]
noncomputable def comErrorBound (s : ℕ) : ℝ≥0∞ :=
  min 4 (24 * min 1 ((2 * s + 1 : ℝ≥0∞) / Fintype.card Y))

variable {X Msg Salt Z : Type} [DecidableEq X] [LinearOrder Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
  (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg fun i ↦ Td Y Salt (d i)) Z)

/-- The instability contribution to P2 is at most `24 min (1, (2s + 1) / |Y|)`. -/
theorem comBoundError_le [Finite X] [UniformAnswerMeasure (X →ₒ Y)] (s : ℕ) :
    comBoundError (multiExtract enc d) s ≤
      24 * min 1 ((2 * s + 1 : ℝ≥0∞) / Fintype.card Y) := by
  unfold comBoundError
  gcongr
  exact iSup_le fun j ↦ iSup_le fun tic ↦ iSup_le fun Ds ↦
    instability_onlineLabel_le enc d tic Ds j s

variable [Fintype X] [AddCommGroup Y]

/-- Concrete P2 for the old compressed oracle, with the sharp universal cap four. -/
theorem comBound [UniformAnswerMeasure (X →ₒ Y)] :
    ComBound.{v, w} (compressedVCOracle k X Y) (multiExtract enc d) code
      (comErrorBound (Y := Y)) := by
  have h := (comBound_compressedVCOracle (multiExtract enc d) code).mono
    (comBoundError_le enc d)
  intro i s A Env α x ρ hx
  exact le_min (comBound_four _ _ code i s x ρ hx) (h i s x ρ hx)

/-- Both clauses of P2: the old oracle ports commute, and extraction commutes up to `C(s)`. -/
theorem oraclesCommute_and_comBound [UniformAnswerMeasure (X →ₒ Y)] :
    OraclesCommute (compressedVCOracle k X Y) ∧
      ComBound.{v, w} (compressedVCOracle k X Y) (multiExtract enc d) code
        (comErrorBound (Y := Y)) :=
  ⟨oraclesCommute_compressedVCOracle, comBound enc d code⟩

end SaltedMerkle
