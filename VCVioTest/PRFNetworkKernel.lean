/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.Network.Kernel
public import VCVio.EvalDist.FailureMeasure

/-!
# PRF reduction under joint-kernel replacement

Every service call draws and discards an additional fair bit before executing the reference
handler. The complete network reduction still applies to every bounded adaptive client.
This is semantic preservation; the added random draw changes implementation costs.
-/

public section

namespace PRFTagReader.Network.Tests

open OracleComp OracleSpec MeasureTheory UnlinkReduction ENNReal

local instance : Countable (UnlinkState Bool) :=
  Function.Injective.countable (f := UnlinkState.sessionsUsed)
    (by rintro ⟨a⟩ ⟨b⟩ h; cases h; rfl)

local instance : Countable (UnlinkBadState Bool Bool Bool) :=
  Function.Injective.countable
    (f := fun s : UnlinkBadState Bool Bool Bool =>
      (s.sessionsUsed, s.responses, s.bad, s.cacheBad))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; cases Prod.mk.inj h; simp_all)

local instance : Countable (TagTranscript Bool Bool) :=
  Function.Injective.countable (f := fun t : TagTranscript Bool Bool => (t.nonce, t.auth))
    (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; cases Prod.mk.inj h; simp_all)

local instance : Countable ReaderReply :=
  Function.Injective.countable (f := ReaderReply.accepts)
    (by intro a b h; cases a <;> cases b <;> simp_all [ReaderReply.accepts])

local instance (operation : (UnlinkOracleSpec Bool Bool Bool).Domain) :
    Countable ((UnlinkOracleSpec Bool Bool Bool).Range operation) := by
  cases operation <;> dsimp [UnlinkOracleSpec] <;> infer_instance

local instance (operation : (UnlinkOracleSpec Bool Bool Bool).Domain) :
    MeasurableSpace ((UnlinkOracleSpec Bool Bool Bool).Range operation) := ⊤

local instance (operation : (UnlinkOracleSpec Bool Bool Bool).Domain) :
    DiscreteMeasurableSpace ((UnlinkOracleSpec Bool Bool Bool).Range operation) :=
  ⟨fun _ => trivial⟩

local instance : MeasurableSpace (MultipleServiceState Bool Bool Bool) := ⊤
local instance : DiscreteMeasurableSpace (MultipleServiceState Bool Bool Bool) :=
  ⟨fun _ => trivial⟩

local instance : MeasurableSpace (SingleServiceState Bool Bool Bool 2) := ⊤
local instance : DiscreteMeasurableSpace (SingleServiceState Bool Bool Bool 2) :=
  ⟨fun _ => trivial⟩

local instance : MeasurableSpace (MultipleBadState Bool Bool Bool 2) := ⊤
local instance : DiscreteMeasurableSpace (MultipleBadState Bool Bool Bool 2) :=
  ⟨fun _ => trivial⟩

@[expose] def noisy {S : Type}
    (impl : QueryImpl (UnlinkOracleSpec Bool Bool Bool) (StateT S ProbComp)) :
    QueryImpl (UnlinkOracleSpec Bool Bool Bool) (StateT S ProbComp) :=
  fun operation state => do
    let _ ← $ᵗ Bool
    (impl operation).run state

theorem noisy_joint_law {S : Type} [MeasurableSpace S]
    (impl : QueryImpl (UnlinkOracleSpec Bool Bool Bool) (StateT S ProbComp))
    (operation : (UnlinkOracleSpec Bool Bool Bool).Domain) (state : S) :
    𝒟[(noisy impl operation).run state] = 𝒟[(impl operation).run state] := by
  change 𝒟[(($ᵗ Bool) >>= fun _ => (impl operation).run state)] = _
  rw [_root_.evalDist_bind_const, measure_univ, one_smul]

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
    Measurable.of_discrete adversary qReader qTag hReader hTag

end PRFTagReader.Network.Tests
