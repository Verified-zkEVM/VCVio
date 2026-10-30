/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Merkle.Online

/-!
# Public-import checks for recording grades and online constants

The declarations are consumed through an ordinary import. The numerical examples check the
zero errors at budgets zero and one, the odd-weight sum, the coefficient 24, and the cap.
The main P5 theorems are checked through the same public import.
-/

public section

open Quantum
open scoped ENNReal

#check RecReg.swapEquiv
#check RecReg.occupied_swap
#check RecReg.swap_eq_of_extract_eq_on_occupied
#check VCOracle.withRecord_jointPost_grade
#check VCOracle.withRecordME_jointPost_grade
#check compressedVCOracle_U_totalSize_le
#check SaltedMerkle.instability_onlineLabel_list_le
#check SaltedMerkle.instability_onlineLabel_empty
#check online_weighted_sum_sq_le

#check RecReg.swap_rest_eq_iff
#check cellControlled_apply
#check QuerySupportedOn.callInput
#check QuantumRuntime.queryWeight_mono_of_grade
#check EmulatedOracle.ofReal_trace_coherentBlocks_conj_le_selectedMass
#check SaltedMerkle.instability_onlineLabel_list_le_jointBudget
#check SaltedMerkle.l2_opNorm_online_commutator_sq_le
#check online_weighted_rpow_sum_le
#check sum_onlineRate

example : (Finset.range 6).sum onlineStepWeight = 25 := by
  norm_num [sum_onlineStepWeight]

example : merkleOnlineError 1024 3 2 = (3 / 16 : ℝ≥0∞) := by
  norm_num [merkleOnlineError]
  rw [min_eq_right ((ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num))]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

example : merkleOnlineError 16 3 2 = 1 := by
  norm_num [merkleOnlineError]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
  norm_num

example : merkleOnlineError 1024 0 ⊤ = 0 ∧ merkleOnlineError 1024 1 ⊤ = 0 := by
  simp

example : (24 / (1024 : ℝ)) *
    (∑ j ∈ Finset.range 3, Real.sqrt ((onlineStepWeight j : ℝ) * onlineStepWeight j)) ^ 2 =
      3 / 8 := by
  norm_num [Finset.sum_range_succ, onlineStepWeight, Real.sqrt_mul_self]

example (ME : MultiExtractor 0 Unit (fun _ ↦ Unit) Unit)
    (R : RecReg 0 Unit (fun _ ↦ Unit) Bool) : RecReg.swap ME () R = R := by
  apply Prod.ext
  · funext q
    have hp := q.1.len_pos
    have hl := q.1.len_le
    omega
  · funext qt
    have hp := qt.1.1.len_pos
    have hl := qt.1.1.len_le
    omega

example : ∑ j ∈ Finset.range 3, ENNReal.ofReal (24 * (onlineStepWeight j : ℝ) / (1024 : ℕ)) =
    (3 / 32 : ℝ≥0∞) := by
  rw [sum_onlineRate (N := 1024) (by norm_num)]
  norm_num
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

end

#check Quantum.recordUnitary_swap_apply
#check Quantum.RecReg.swapUnitary_mem_unitaryGroup
#check Quantum.RecReg.swapUnitary_initial
#check Quantum.recordUnitary_swap_conjugacy
#check Quantum.extractUnitary_swap_conjugacy

#check Quantum.l2_opNorm_recordingDefect_le
#check Quantum.l2_opNorm_familyDefect_source_le
#check Quantum.l2_opNorm_compressed_recordingDefect_source_sq_le
#check Quantum.posSemidef_rotated_port_difference_of_source_bound
#check SaltedMerkle.instability_online_keys_le

#check Quantum.VCOracle.outcomeLawWith_recording_rpow_bounds
#check Quantum.VCOracle.onlineIndistinguishable_of_recording_source_bounds
#check Quantum.compressed_online_of_instability
#check SaltedMerkle.merkle_online
#print axioms SaltedMerkle.merkle_online

public section

open Quantum
open scoped ENNReal

namespace ReadRecordingCounterexample

open Matrix
open scoped Kronecker

private def swapBits (b : Bool) : Equiv.Perm (Bool × Bool × Bool) where
  toFun r := if b then (r.2.2, r.2.1, r.1) else (r.2.1, r.1, r.2.2)
  invFun r := if b then (r.2.2, r.2.1, r.1) else (r.2.1, r.1, r.2.2)
  left_inv r := by cases b <;> rfl
  right_inv r := by cases b <;> rfl

private def split (d : Option Bool) : Equiv.Perm (Bool × Bool × Bool) :=
  swapBits (d == some false)

/-- The empty-read branch has a nonzero commutator with the controlled record swap. -/
example : readPermutationDefect split
    (fun _ : Unit ↦ checkedReadEmptyCell (Y := Bool))
      ((some false, (false, false, true)), ()) (some true, (true, false, false)) =
        (1 / 2 : ℂ) := by
  norm_num [readPermutationDefect, split, swapBits, checkedReadEmptyCell_apply,
    cellUniform_some, cellAmp_mul_self]

end ReadRecordingCounterexample

section ReadMass

open Matrix

private abbrev readSpec := classicalReadSpec Unit Bool
private noncomputable abbrev workReg := QReg.of (Unit × Unit)

private noncomputable def readOnce :
    QuantumComp LocalSig.instruments readSpec (fun _ ↦ Unit) workReg :=
  .queryBind () (QReg.of Unit) (Equiv.refl _) (fun _ ↦ .pure ())

example : readOnce.IsTotalQueryBound 1 := by
  simp [readOnce, QuantumComp.isTotalQueryBound_queryBind_iff]

/-- A read-only wrapper charges its input trace once, independently of its outcome law. -/
example (R : QuantumRuntime readSpec)
    (σ : Matrix (workReg × R.D) (workReg × R.D) ℂ) :
    R.totalWeight .instruments (fun _ τ ↦ ENNReal.ofReal τ.trace.re) readOnce σ =
      ENNReal.ofReal σ.trace.re := by
  simp [readOnce, QuantumRuntime.totalWeight_queryBind, QuantumRuntime.trace_callInput]

/-- A program without calls has zero mass in either runtime. -/
example (R T : QuantumRuntime readSpec)
    (σ : Matrix (workReg × R.D) (workReg × R.D) ℂ)
    (τ : Matrix (workReg × T.D) (workReg × T.D) ℂ) :
    R.totalWeight .instruments (fun _ ω ↦ ENNReal.ofReal ω.trace.re)
        (QuantumComp.pure (A := workReg) (X := fun _ ↦ Unit) ()) σ =
      T.totalWeight .instruments (fun _ ω ↦ ENNReal.ofReal ω.trace.re)
        (QuantumComp.pure (A := workReg) (X := fun _ ↦ Unit) ()) τ := by
  simp

private noncomputable abbrev constantRead (b : Bool) : QuantumRuntime readSpec where
  D := QReg.of Unit
  init := SubState.basis ()
  step _ := SubInstrument.pure b

private noncomputable def conditionalRead : QuantumComp LocalSig.instruments readSpec
    (fun _ ↦ Unit) workReg :=
  .queryBind () (QReg.of Unit) (Equiv.refl _)
    (fun b ↦ if b then readOnce else .pure ())

/-- Adaptive read mass belongs to its execution world, even with identical initialization. -/
example (b : Bool) (σ : Matrix (workReg × Unit) (workReg × Unit) ℂ) :
    (constantRead b).totalWeight .instruments (fun _ τ ↦ ENNReal.ofReal τ.trace.re)
      conditionalRead σ = (if b then 2 else 1) * ENNReal.ofReal σ.trace.re := by
  dsimp only [constantRead, workReg, readSpec, classicalReadSpec]
  simp only [conditionalRead, QuantumRuntime.totalWeight_queryBind,
    tsum_fintype, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_false, ite_true, QuantumRuntime.totalWeight_pure,
    add_zero, readOnce, QuantumRuntime.totalWeight_queryBind,
    QuantumRuntime.totalWeight_pure, tsum_zero]
  rw [QuantumRuntime.queryStep_branch_apply]
  cases b <;> simp [SubInstrument.relabel_branch_apply, QuantumRuntime.trace_callInput,
    QuantumRuntime.queryEquivIn, QuantumRuntime.queryEquivOut, Function.comp_def, two_mul]
  rfl

end ReadMass

/-- Empty records give zero read defect without observing the record-key register. -/
theorem VCOnlineTest.readPermutationDefect_empty_record
    {k : ℕ} {Cm S Cell A : Type} {Dm : Fin k → Type}
    [Fintype Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
    [DecidableEq Cell]
    (ME : MultiExtractor k Cm Dm S) (M : A → Matrix S S ℂ) (bot : Cell)
    (s s' : S) (r : RecReg k Cm Dm Cell) (a : A) :
    readPermutationDefect (RecReg.swapEquiv ME) M ((s, r), a) (s', RecReg.const bot) = 0 := by
  simp [readPermutationDefect, RecReg.swapEquiv, RecReg.swap_const]

example (N t : ℕ) : merkleOnlineError N t ⊤ = merkleOnlineError N t t := by
  simp [merkleOnlineError]

/-- The mixed recording weight charges the entire read input once. -/
example (E : VCOracle 1 Unit (ZMod 2))
    (ME : MultiExtractor 1 Unit (fun _ ↦ Unit) E.S)
    (code : TpDCode 1 (fun _ ↦ Unit) (ZMod 2))
    (σ : Matrix (Unit × (E.S × RecReg 1 Unit (fun _ ↦ Unit) Bool))
      (Unit × (E.S × RecReg 1 Unit (fun _ ↦ Unit) Bool)) ℂ) :
    E.recordVCWeight ME code false (1 : Matrix (Unit × Bool) (Unit × Bool) ℂ)
      (one_mem _) (.inr (0, ())) σ = ENNReal.ofReal σ.trace.re := rfl
