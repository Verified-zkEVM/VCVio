/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.ScalarPolicy
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Certificates

/-!
# Existing security certificates under input-sensitive scalar caps

A declared event policy pointwise dominates original selected source work. The same counted
signing experiment's almost-sure scalar cap then bounds the original joint selected work at
the same value. Each theorem applies the matching existing certificate
under its original empty-cache shared-ROM model and per-request message/context interface.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.ScalarPolicy

/-- A model adversary with scalar work below 569 never wins, with no lifetime premise. -/
theorem advantage_eq_zero_model (policy : Event HashOutput → Nat)
    (hdom : ∀ event, selectedWork (sourcePolicy event) ≤ policy event)
    (adv : Game.Adversary HashOutput PublicKey)
    (q : Nat) (hq : q < 569)
    (hcap : Pr{let observed ← run policy Bridge.model adv}[observed.cost ≤ q] = 1) :
    Pr{let observed ← run policy Bridge.model adv}[SigningView.Wins id observed.toOutcome] = 0 := by
  rw [success_probability]
  exact SharedExperiment.advantage_eq_zero_model adv q hq (cap_transport policy hdom _ adv q hcap)

/-- A FIPS adversary with scalar work below 569 never wins, with no lifetime premise. -/
theorem advantage_eq_zero_fips (policy : Event FIPS205.Answer → Nat)
    (hdom : ∀ event, selectedWork (sourcePolicy event) ≤ policy event)
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (q : Nat) (hq : q < 569)
    (hcap : Pr{let observed ← run policy FIPS205.scheme adv}[observed.cost ≤ q] = 1) :
    Pr{let observed ← run policy FIPS205.scheme adv}[SigningView.Wins id observed.toOutcome] =
      0 := by
  rw [success_probability]
  exact SharedExperiment.advantage_eq_zero_fips adv q hq (cap_transport policy hdom _ adv q hcap)

/-- The original signing lifetime and a positive scalar cap give the same 127-bit certificate. -/
theorem advantage_le_127 (policy : Event FIPS205.Answer → Nat)
    (hdom : ∀ event, selectedWork (sourcePolicy event) ≤ policy event)
    (q : Nat) (hq : 1 ≤ q)
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (hlimit :
      Pr{let result ← (observedGame FIPS205.scheme).experiment () adv}[result.2 .sign ≤ 2 ^ 64] = 1)
    (hcap : Pr{let observed ← run policy FIPS205.scheme adv}[observed.cost ≤ q] = 1) :
    Pr{let observed ← run policy FIPS205.scheme adv}[SigningView.Wins id observed.toOutcome] ≤
      q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [success_probability]
  exact SharedExperiment.advantage_le_127 q hq adv hlimit (cap_transport policy hdom _ adv q hcap)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.ScalarPolicy
