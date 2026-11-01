/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import Examples.SLHDSA.WeightedPolicy
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.ScalarPolicy.Certificates

/-!
# Existing security certificates under input-sensitive scalar caps

The same counted signing experiment charges signing attempts one unit and selected public hash
calls one plus their actual raw input length. Its almost-sure scalar cap dominates the original
joint selected-work cap at the same value. Each theorem applies the matching existing certificate
under its original empty-cache shared-ROM model and per-request message/context interface.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.WeightedPolicy

/-- A model adversary with scalar work below 569 never wins, with no lifetime premise. -/
theorem advantage_eq_zero_model (adv : Game.Adversary HashOutput PublicKey)
    (q : Nat) (hq : q < 569)
    (hcap : Pr{let observed ← run Bridge.model adv}[observed.cost ≤ q] = 1) :
    Pr{let observed ← run Bridge.model adv}[SigningView.Wins id observed.toOutcome] = 0 := by
  exact ScalarPolicy.advantage_eq_zero_model policy policy_domination adv q hq hcap

/-- A FIPS adversary with scalar work below 569 never wins, with no lifetime premise. -/
theorem advantage_eq_zero_fips
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (q : Nat) (hq : q < 569)
    (hcap : Pr{let observed ← run FIPS205.scheme adv}[observed.cost ≤ q] = 1) :
    Pr{let observed ← run FIPS205.scheme adv}[SigningView.Wins id observed.toOutcome] = 0 := by
  exact ScalarPolicy.advantage_eq_zero_fips policy policy_domination adv q hq hcap

/-- The original signing lifetime and a positive scalar cap give the same 127-bit certificate. -/
theorem advantage_le_127 (q : Nat) (hq : 1 ≤ q)
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (hlimit :
      Pr{let result ← (observedGame FIPS205.scheme).experiment () adv}[result.2 .sign ≤ 2 ^ 64] = 1)
    (hcap : Pr{let observed ← run FIPS205.scheme adv}[observed.cost ≤ q] = 1) :
    Pr{let observed ← run FIPS205.scheme adv}[SigningView.Wins id observed.toOutcome] ≤
      q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  exact ScalarPolicy.advantage_le_127 policy policy_domination q hq adv hlimit hcap

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.WeightedPolicy
