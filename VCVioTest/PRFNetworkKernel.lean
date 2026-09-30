/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.Network.Kernel
public import VCVio.EvalDist.Defs.Measure
public import VCVio.EvalDist.WithFailure

/-!
# PRF reduction under joint-kernel replacement

Every service call draws and discards an additional fair bit before executing the reference
handler. The complete network reduction still applies to every bounded adaptive client.
This is semantic preservation; the added random draw changes implementation costs.
-/

public section

namespace PRFTagReader.Network.Tests

open OracleComp OracleSpec MeasureTheory UnlinkReduction ENNReal

@[expose] def noisy {S : Type}
    (impl : QueryImpl (UnlinkOracleSpec Bool Bool Bool) (StateT S ProbComp)) :
    QueryImpl (UnlinkOracleSpec Bool Bool Bool) (StateT S ProbComp) :=
  fun operation state => do
    let _ ← $ᵗ Bool
    (impl operation).run state

theorem noisy_joint_law {S : Type}
    (impl : QueryImpl (UnlinkOracleSpec Bool Bool Bool) (StateT S ProbComp))
    (operation : (UnlinkOracleSpec Bool Bool Bool).Domain) (state : S) :
    (noisy impl operation).run state =ᵈ (impl operation).run state :=
  EvalDistEq.of_forall_prEvent_eq fun p => by
    change wp⟦($ᵗ Bool) >>= fun _ => (impl operation).run state⟧ (predInd p) = _
    rw [prEvent_bind, MeasureProgramLogic.wp_const_of_oracle]

/-- The full three-term packet reduction admits a concretely changed implementation. -/
example (adversary : UnlinkAdversary Bool Bool Bool) (qReader qTag : ℕ)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    𝒟[verdict (noisy (multipleIdealQueryImpl (sessionsPerTag := 2)))
      (qReader + qTag) adversary (UnlinkState.init, ∅)] {true} ≤
    𝒟[verdict (noisy (singleIdealQueryImpl (sessionsPerTag := 2)))
      (qReader + qTag) adversary (UnlinkState.init, ∅)] {true} +
    𝒟[stateEvent (noisy (multipleBadQueryImpl _ _ _ 2))
      (qReader + qTag) adversary ((UnlinkState.init, ∅), UnlinkBadState.init)
      (fun state => state.2.bad)] {true} +
    ((qReader * Fintype.card Bool : ℕ) : ℝ≥0∞) / (Fintype.card Bool : ℝ≥0∞) +
    ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Bool : ℝ≥0∞) +
    ((qReader * Fintype.card Bool * 2 : ℕ) : ℝ≥0∞) / (Fintype.card Bool : ℝ≥0∞) := by
  exact multiple_le_single_add_bad_of_joint_law _ _ _
    (noisy_joint_law _) (noisy_joint_law _) (noisy_joint_law _)
    true adversary qReader qTag hReader hTag

end PRFTagReader.Network.Tests
