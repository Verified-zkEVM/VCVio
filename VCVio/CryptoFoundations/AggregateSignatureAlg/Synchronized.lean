/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.AggregateSignatureAlg

/-! # Synchronized aggregate signatures in the certified-key model

Messages carry a period. An adversary receives one honest public key and supplies the secret
keys and messages of its co-signers. Success requires a fresh honest message, aggregate
verification, and at most one signing request per period in the entire signing log. The latter
is a winning condition, not an adversary restriction. This is the certified-key experiment of
Ahn, Green and Hohenberger, *Synchronized aggregate signatures* (CCS 2010).

Public-key derivation is an argument of the experiment, so the aggregate-signature interface
also supports schemes whose key generation does not expose deterministic key derivation.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace AggregateSignatureAlg.Synchronized

/-- The target period/message, certified co-signers and their messages, and aggregate. -/
abbrev Forgery (Period M SK S : Type) := (Period × M) × List (SK × M) × S

/-- No two signing occurrences use the same period, including identical repeated requests. -/
@[expose] def OnePerPeriod {Period M : Type} (signed : List (Period × M)) : Prop :=
  signed.Pairwise fun a b => a.1 ≠ b.1

/-- Period equality decides whether the complete signing log respects synchronization. -/
instance {Period M : Type} [DecidableEq Period] (signed : List (Period × M)) :
    Decidable (OnePerPeriod signed) := inferInstanceAs (Decidable (signed.Pairwise _))

/-- A certified-key adversary with ambient oracle access and an honest signing oracle. -/
structure Adversary {ι : Type} {spec : OracleSpec ι} {Period M PK SK S : Type}
    (_sigAlg : AggregateSignatureAlg (OracleComp spec) (Period × M) PK SK S) where
  /-- Return the target and certified co-signers after receiving the honest public key. -/
  main (pk : PK) : OracleComp (spec + ((Period × M) →ₒ S)) (Forgery Period M SK S)

open scoped Classical in
/-- The synchronized winning bit: freshness, one signing occurrence per period, and validity. -/
@[expose] noncomputable def winningEvent {Period M S : Type}
    (target : Period × M) (log : QueryLog ((Period × M) →ₒ S)) (verified : Bool) : Bool :=
  !log.wasQueried target && decide (OnePerPeriod (log.map Sigma.fst)) && verified

/-- Repeating a signing period makes the synchronized winning bit false regardless of validity. -/
theorem winningEvent_eq_false_of_not_onePerPeriod {Period M S : Type}
    (target : Period × M) (log : QueryLog ((Period × M) →ₒ S)) (verified : Bool)
    (h : ¬OnePerPeriod (log.map Sigma.fst)) : winningEvent target log verified = false := by
  simp [winningEvent, h]

open scoped Classical in
/-- Certified-key synchronized unforgeability. Every co-signer uses the target period and a
public key derived from its supplied secret key. Signing and verification share ambient oracles. -/
@[expose] noncomputable def unforgeableExperiment
    {ι : Type} {spec : OracleSpec ι} {Period M PK SK S : Type}
    {sigAlg : AggregateSignatureAlg (OracleComp spec) (Period × M) PK SK S}
    (publicKeyOf : SK → PK) (adv : Adversary sigAlg) : OracleComp spec Bool := do
  let (pk, sk) ← sigAlg.keygen
  let ((target, others, aggregate), log) ←
    sigAlg.toSignatureAlg.runWithSigningOracle pk sk (adv.main pk)
  let verified ← sigAlg.aggregateVerify
    ((pk, target) :: others.map (fun p => (publicKeyOf p.1, (target.1, p.2)))) aggregate
  return winningEvent target log verified

/-- Success probability under a supplied runtime; a random-oracle runtime shares its cache
across key generation, the adversary, signing, and final aggregate verification. -/
@[expose] noncomputable def unforgeableAdvantage
    {ι : Type} {spec : OracleSpec ι} {Period M PK SK S : Type}
    {sigAlg : AggregateSignatureAlg (OracleComp spec) (Period × M) PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (publicKeyOf : SK → PK)
    (adv : Adversary sigAlg) : ℝ≥0∞ :=
  runtime.evalDist (unforgeableExperiment publicKeyOf adv) {true}

end AggregateSignatureAlg.Synchronized
