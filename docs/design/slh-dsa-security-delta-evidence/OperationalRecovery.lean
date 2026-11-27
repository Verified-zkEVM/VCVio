/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget
public import HashSig.SLHDSA.SHAKE128s.Bridge.Scheme

/-!
# Verification work excludes small-budget success

The full source-counted experiment projects to the verifier's phase observation.
An accepting verification needs at least 569 charged calls, independently of a signing lifetime.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.SHAKE128s.OperationalRecovery

open SLHDSA.SHAKE128s.Security

/-- Interpretation in the empty-cache world commutes with a returned-value map. -/
theorem run_map {Output α β : Type} [SampleableType Output]
    (f : α → β) (program : OracleComp (Game.World Output) α) :
    RandomOracleModel.run (f <$> program) = f <$> RandomOracleModel.run program := by
  simp only [RandomOracleModel.run, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- The shared full observation retains the exact paper proof's outcome. -/
theorem outcome_projection (adversary : Adversary) :
    Game.Counted.legacyOutcome <$>
        RandomOracleModel.run (Game.Counted.canonicalExperiment externalScheme adversary) =
      Security.run adversary := by
  rw [Security.run, Security.experiment, run_map]

/-- A sub-569 actual joint cap excludes every successful forgery. -/
theorem advantage_eq_zero (adversary : Adversary) (q : Nat) (hq : q < 569)
    (hbound : (Game.securityGame externalScheme).HasQueryBound () Game.adversaryWork
      adversary q) :
    (Game.securityGame externalScheme).advantage () adversary = 0 := by
  unfold SecurityGame.advantage
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun result hresult hwin => ?_
  change result ∈ support ((fun pair => (decide (Game.Wins pair.1), pair.2)) <$>
    Game.runBySource externalScheme adversary) at hresult
  rw [support_map] at hresult
  obtain ⟨pair, hpair, rfl⟩ := hresult
  have wins : Game.Wins pair.1 := by simpa using hwin
  have capped := (OracleComp.prEvent_eq_one_iff _ _).mp hbound _ (by
    change _ ∈ support ((fun pair => (decide (Game.Wins pair.1), pair.2)) <$>
      Game.runBySource externalScheme adversary)
    rw [support_map]
    exact ⟨pair, hpair, rfl⟩)
  change pair ∈ support (RandomOracleModel.run
    (Game.experimentBySource externalScheme adversary)) at hpair
  rw [Game.experimentBySource, run_map, support_map] at hpair
  obtain ⟨observed, hobserved, rfl⟩ := hpair
  have houtcome : Game.Counted.legacyOutcome observed ∈ support (Security.run adversary) := by
    rw [← outcome_projection, support_map]
    exact ⟨observed, hobserved, rfl⟩
  have lower := VerificationBudget.accepted_outcome_work adversary
    (Game.Counted.legacyOutcome observed) houtcome wins.1
  simp only [Game.Counted.legacyObservation_counts] at capped
  have upper : observed.cost .sign + (observed.cost .hash + observed.cost .verifier) ≤ q := by
    simpa [Game.adversaryWork] using capped
  change 569 ≤ observed.cost .hash + observed.cost .verifier at lower
  omega

/-- The same zero guarantee holds at the full native byte-answer interface. -/
theorem advantage_eq_zero_fips
    (adversary : Game.Adversary FIPS205.Answer (SLHDSA.PublicKeyCore FIPS205.core))
    (q : Nat) (hq : q < 569)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork
      adversary q) :
    (Game.securityGame FIPS205.scheme).advantage () adversary = 0 := by
  have law := Bridge.experiment_evalDistEq Bridge.schemeBridge
    Bridge.map_answerEquiv_uniformSample adversary
  have capped : (Game.securityGame externalScheme).HasQueryBound () Game.adversaryWork
      (Bridge.adapt Bridge.schemeBridge adversary) q :=
    (law.prEvent_eq _).symm.trans hbound
  calc
    (Game.securityGame FIPS205.scheme).advantage () adversary =
        (Game.securityGame externalScheme).advantage ()
          (Bridge.adapt Bridge.schemeBridge adversary) := law.prEvent_eq _
    _ = 0 := advantage_eq_zero _ q hq capped

end SLHDSA.SHAKE128s.OperationalRecovery

#print axioms SLHDSA.SHAKE128s.OperationalRecovery.advantage_eq_zero
#print axioms SLHDSA.SHAKE128s.OperationalRecovery.advantage_eq_zero_fips
