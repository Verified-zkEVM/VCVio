/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.ForgeryBound
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Probability
public import HashSig.SLHDSA.SHAKE128s.Bridge.Scheme
public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability

/-!
# Strong unforgeability with an almost-sure joint work cap

The joint-work certificate gives 127-bit strong unforgeability on the FIPS byte game.
Representation equivalences carry the result to the bit-vector model and the paper’s signing
interface.
-/

public section
open OracleComp OracleSpec SignatureAlg
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- If joint work is zero with probability one, the probability of winning is zero. -/
theorem original_zero_work_win_eq_zero
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv 0) :
    Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] = 0 :=
  slhDsa_sufCma_eq_zero_of_lt_569 adv 0 (by decide) hbound

end SLHDSA.SHAKE128s.Bridge.SharedExperiment

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical

/-- The FIPS external game with 30-byte oracle answers has 127 bits of joint-work security. -/
theorem fips_joint_127 : Game.HasSecurityBits FIPS205.scheme Game.adversaryWork 127 :=
  slhDsa_sufCma_127

/-- The model with 240-bit oracle answers has 127 bits of joint-work security. -/
theorem model_joint_127 : Game.HasSecurityBits Bridge.model Game.adversaryWork 127 :=
  (Bridge.hasSecurityBits_fips205_iff Game.adversaryWork 127).mp fips_joint_127

/-- The paper’s signing-and-forgery game has 127 bits of joint-work security. -/
theorem paper_joint_127 : SLHDSA.SHAKE128s.Security.HasSecurityBits
    SLHDSA.SHAKE128s.Security.adversaryWork 127 :=
  (Bridge.hasSecurityBits_model_iff _ _).mpr model_joint_127

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
