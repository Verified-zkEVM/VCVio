/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import VCVio.Quantum.VC.Merkle.Online

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
#check EmulatedOracle.queryWeight_conj_le_selectedMass_of_grade
#check EmulatedOracle.tsum_rpow_queryWeight_conj_le_of_grade
#check EmulatedOracle.outcomeLawWith_rpow_bounds_of_graded_ports
#check EmulatedOracle.tsum_rpow_queryWeight_conj_le_online
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
