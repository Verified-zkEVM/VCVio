/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget
import HashSig.SLHDSA.SHAKE128s.Bridge.Scheme

/-! # Zero forgery advantage below the SHAKE-128s verification floor -/
public section
open OracleComp OracleSpec
namespace SLHDSA.SHAKE128s

/-- Deterministic pure-mode SHAKE-128s has zero forgery advantage below 569 actual joint calls,
including verification of the forgery against the cache left by the adversary. -/
theorem slhDsa_sufCma_eq_zero_of_lt_569
    (adv : Game.Adversary FIPS205.Answer (SLHDSA.PublicKeyCore FIPS205.core)) (q : Nat)
    (hq : q < 569) (cap : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork
      adv q) : (Game.securityGame FIPS205.scheme).advantage () adv = 0 := by
  have law := Bridge.experiment_evalDistEq Bridge.schemeBridge
    Bridge.map_answerEquiv_uniformSample adv
  exact (law.prEvent_eq _).trans (VerificationBudget.advantage_eq_zero
    (Bridge.adapt Bridge.schemeBridge adv) q hq ((law.prEvent_eq _).symm.trans cap))

end SLHDSA.SHAKE128s
