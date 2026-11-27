/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module

import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Security
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget

/-!
# SHAKE-128s strong forgery under an actual joint work cap

Erasing the hash counter recovers the signing experiment. The cost of an accepting verification
gives zero success below 569 units of work. Transport from the FIPS byte game supplies the
127-bit joint-work certificate.
-/
public section
open OracleComp OracleSpec
namespace SLHDSA.SHAKE128s.WorkFinal
open SLHDSA.SHAKE128s.Security

/-- Erasing the total hash counter recovers the original experiment. -/
theorem map_fst_runAll (adversary : Adversary) : Prod.fst <$> runAll adversary = run adversary := by
  have commute (f : Outcome × Nat → Outcome) (p : OracleComp OracleWorld (Outcome × Nat)) :
      RandomOracleModel.run (f <$> p) = f <$> RandomOracleModel.run p := by
    unfold RandomOracleModel.run
    rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
      Functor.map_map]
  rw [runAll, run, ← commute]
  exact congrArg RandomOracleModel.run (Game.fst_map_countAllHashes _)

/-- Verification alone exceeds any joint cap below 569 on an accepting forgery. -/
theorem advantage_eq_zero (adversary : Adversary) (q : Nat) (hq : q < 569)
    (hbound : securityGame.HasQueryBound () adversaryWork adversary q) :
    securityGame.advantage () adversary = 0 :=
  VerificationBudget.advantage_eq_zero adversary q hq hbound

/-- Strong forgery has 127 bits of security under the adversary-work counting convention. -/
theorem hasSecurityBits_work : HasSecurityBits adversaryWork 127 :=
  Bridge.SharedExperiment.Physical.paper_joint_127

end SLHDSA.SHAKE128s.WorkFinal
