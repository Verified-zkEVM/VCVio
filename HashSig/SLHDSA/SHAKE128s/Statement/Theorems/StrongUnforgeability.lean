/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.SmallBudget
public import HashSig.SLHDSA.Security.WeakKeyBound
import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Security
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Observation

/-!
# Actual-work security of deterministic SHAKE-128s

The attacker and the verifier use the same 30-byte SHAKE oracle as the signer. The probability-one
budget counts each signing attempt, each direct attacker hash and the actual hashes used by final
verification. The lifetime condition permits at most `2 ^ 64` signing attempts.
`slhDsa_sufCma_le` bounds forgery at every budget. Below 569, the separate
`slhDsa_sufCma_eq_zero_of_lt_569` needs only the budget.
-/

public section

open OracleComp
open scoped ENNReal

namespace SLHDSA.SHAKE128s

open Bridge.SharedExperiment.Physical

/-- The verifier floor, paid native charge and unit probability bound in their respective ranges. -/
@[expose] noncomputable def jointWorkBound (q : Nat) : ℝ≥0∞ :=
  if q < 569 then 0 else if q < 2 ^ 127 then
    ((32 * q - 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
      34 * (SLHDSA.Security.honestAdrsCount FIPS205.params : ℝ≥0∞) / (2 ^ 256)
  else 1

/-- An accepting verifier cannot fit below its minimum work. -/
@[simp] theorem jointWorkBound_of_lt_569 {q : Nat} (low : q < 569) : jointWorkBound q = 0 := by
  unfold jointWorkBound
  exact ite_eq_left low

/-- In the nontrivial range, the paid charge leaves a fixed reserve after the weak-key correction.
The numerator in the correction counts the honest addresses of SHAKE-128s. -/
@[simp] theorem jointWorkBound_of_middle {q : Nat} (low : 569 ≤ q) (high : q < 2 ^ 127) :
    jointWorkBound q =
      ((32 * q - 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
        34 * (1591788895347057694892543 : ℝ≥0∞) / (2 ^ 256) := by
  simp only [jointWorkBound, ite_eq_right (Nat.not_lt.mpr low), ite_eq_left high,
    Bridge.SharedExperiment.honestAdrsCount_fips205, Nat.cast_ofNat]

/-- At the trivial probability threshold the work bound saturates at one. -/
@[simp] theorem jointWorkBound_of_ge_two_pow {q : Nat} (high : 2 ^ 127 ≤ q) :
    jointWorkBound q = 1 := by
  have low : ¬q < 569 := by omega
  unfold jointWorkBound
  rw [ite_eq_right low, ite_eq_right (Nat.not_lt.mpr high)]

/-- Under the signing lifetime and an almost-sure joint cap, the forgery probability is
bounded by the verifier floor, the paid hash fraction or one, according to the budget. -/
theorem slhDsa_sufCma_le (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (q : Nat) (life : Game.WithinSigningLimit FIPS205.scheme adv)
    (cap : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q) :
    (Game.securityGame FIPS205.scheme).advantage () adv ≤ jointWorkBound q := by
  by_cases low : q < 569
  · rw [jointWorkBound_of_lt_569 low]
    exact (slhDsa_sufCma_eq_zero_of_lt_569 adv q low cap).le
  by_cases high : q < 2 ^ 127
  · rw [jointWorkBound_of_middle (Nat.le_of_not_gt low) high]
    simpa only [weakMass, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc] using
      actual_joint_work_le_reserve adv q (by omega) life cap
  · rw [jointWorkBound_of_ge_two_pow (Nat.le_of_not_gt high)]
    exact prEvent_le_one _

/-- The paid cache reserve makes the nontrivial range strictly smaller than the 127-bit bound. -/
theorem jointWorkBound_lt_of_middle {q : Nat} (low : 569 ≤ q) (high : q < 2 ^ 127) :
    jointWorkBound q < (q : ℝ≥0∞) / (2 ^ 127) := by
  rw [jointWorkBound_of_middle low high]
  simpa only [weakMass, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc] using
    retained_reserve_lt_headline q (by omega)

/-- The piecewise work bound preserves the original coefficient at every natural budget. -/
theorem jointWorkBound_le (q : Nat) : jointWorkBound q ≤ (q : ℝ≥0∞) / (2 ^ 127) := by
  by_cases low : q < 569
  · rw [jointWorkBound_of_lt_569 low]
    exact zero_le
  by_cases high : q < 2 ^ 127
  · exact (jointWorkBound_lt_of_middle (Nat.le_of_not_gt low) high).le
  have large : 2 ^ 127 ≤ q := Nat.le_of_not_gt high
  have h : (2 ^ 127 : ℝ≥0∞) ≤ q := by exact_mod_cast large
  rw [jointWorkBound_of_ge_two_pow large]
  calc
    1 = (2 ^ 127 : ℝ≥0∞) / (2 ^ 127) :=
      (ENNReal.div_self (by positivity) (by finiteness)).symm
    _ ≤ (q : ℝ≥0∞) / (2 ^ 127) := by gcongr

/-- Deterministic FIPS 205 SHAKE-128s has 127 bits of strong unforgeability under the joint
budget for signing attempts, direct attacker queries and verification. -/
theorem slhDsa_sufCma_127 : Game.HasSecurityBits FIPS205.scheme Game.adversaryWork 127 :=
  fips_joint_127

end SLHDSA.SHAKE128s
