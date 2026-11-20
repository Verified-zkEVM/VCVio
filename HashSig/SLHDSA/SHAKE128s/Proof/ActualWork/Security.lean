/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.ForgeryBound
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Probability
public import HashSig.SLHDSA.SHAKE128s.Bridge.Scheme
public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.SmallBudget

/-!
# Strong unforgeability with an almost-sure joint work cap
-/

public section
open OracleComp OracleSpec SignatureAlg
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- An adversary with zero probability-one joint work allowance has no winning execution. -/
theorem original_zero_work_win_eq_zero
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv 0) :
    Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] = 0 :=
  slhDsa_sufCma_eq_zero_of_lt_569 adv 0 (by decide) hbound

end SLHDSA.SHAKE128s.Bridge.SharedExperiment

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical

/-- Below the trivial range, the native charge retains the unused fraction of one
hash-budget unit after both weak-key payments. -/
theorem actual_joint_work_le_reserve
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (q : Nat) (small : 2 * q < 2 ^ 128)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q) :
    (Game.securityGame FIPS205.scheme).advantage () adv ≤
      ((32 * q - 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) + 34 * weakMass := by
  classical
  let fallback (s : Seed) : LabFallback := fun
    | .inl (.inl (.inl native)) => Guarded.deriveFallback s (.inl (.inl native))
    | .inl (.inl (.inr (.inl _))) => ()
    | .inl (.inl (.inr (.inr _))) => Vector.replicate _ 0
    | .inl (.inr raw) => Guarded.deriveFallback s (.inl (.inr raw))
    | .inr ev => Guarded.deriveFallback s (.inr ev)
  apply strict_bound_of_residual_covered adv q small hlimit hbound fallback
  intro seed
  exact GuardedFill.uncharged_probability_le_actualCoverage q small seed adv (fallback seed)

/-- On the actual FIPS 205 scheme, the signing lifetime and almost-sure joint cap suffice at
every budget. The transcript and cache classification happens inside the proof. -/
theorem actual_joint_work_le (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (q : Nat)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q) :
    (Game.securityGame FIPS205.scheme).advantage () adv ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  by_cases minimal : q < 569
  · rw [slhDsa_sufCma_eq_zero_of_lt_569 adv q minimal hbound]
    exact zero_le
  by_cases small : 2 * q < 2 ^ 128
  · exact (actual_joint_work_le_reserve adv q small hlimit hbound).trans
      (retained_reserve_lt_headline q (by omega)).le
  · have high : 2 ^ 127 ≤ q := by omega
    apply (prEvent_le_one _).trans
    have one : (((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞)) = 1 :=
      ENNReal.div_self (by positivity) (by finiteness)
    rw [← one, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_left (Nat.cast_le.mpr high) _

/-- The original actual-work security-bit statement on the 30-byte external game. -/
theorem fips_joint_127 : Game.HasSecurityBits FIPS205.scheme Game.adversaryWork 127 :=
  fun q _ adv life joint => actual_joint_work_le adv q life joint

/-- The identical bit claim on the original 240-bit transcription follows by representation
transport for every adversary. -/
theorem model_joint_127 : Game.HasSecurityBits Bridge.model Game.adversaryWork 127 :=
  (Bridge.hasSecurityBits_fips205_iff Game.adversaryWork 127).mp fips_joint_127

/-- The security statement on the original signing-and-forgery interface. -/
theorem paper_joint_127 : SLHDSA.SHAKE128s.Security.HasSecurityBits
    SLHDSA.SHAKE128s.Security.adversaryWork 127 :=
  (Bridge.hasSecurityBits_model_iff _ _).mpr model_joint_127

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
