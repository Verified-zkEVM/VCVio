/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVioTest.IncomparableEncoding.TargetCollisionResistance

/-!
# Encoding bridge observations

A concrete bridge uses a biased public-seed computation and a fallible encoding. Exhausted slots
retain their indices, and the source experiment and named hash adversary observe the same coupled
sample with the configured target and retry capacities.
-/

public section

namespace IncomparableEncoding.TargetCollisionProbe

open OracleComp OracleSpec TargetCollisionResistance TargetCollisionReduction TweakableHash

/-- A biased public seed, retaining the actual finite random draw. -/
@[expose] def seedGen : ProbComp Bool := do
  let r ← $ᵗ (Fin 3)
  return r != 0

/-- Hash outputs distinguish accepted randomizers from returned encoding failure. -/
@[expose] def bridge : Bridge Bool Bool (Fin 3) Bool Bool Bool 1 2 where
  enc := enc
  th := ⟨seedGen, fun _ _ pair => pair.2 != 0⟩
  epochToTweak := id
  epochToTweak_injective := Function.injective_id
  accepts := id
  word y := fun _ => if y then 0 else 1
  word_injective := by
    intro x y h
    have h0 := congrFun h 0
    cases x <;> cases y <;> simp_all
  value_eq := by
    intro pp msg r ep
    by_cases h : r = 0
    · simp [enc, IncomparableEncoding.value, h]
    · simp [enc, IncomparableEncoding.value, h]
      rfl

/-- Both resource limits and the actual public-seed computation are preserved definitionally. -/
theorem configured_problem (p K : ℕ) :
    (encodingProblem bridge p K).paramGen = seedGen ∧
    (hashProblem bridge p K).th.seedGen = seedGen ∧
    (encodingProblem bridge p K).numRecords = p ∧
    (hashProblem bridge p K).numTargets = p ∧
    (encodingProblem bridge p K).numRetries = K ∧
    (hashProblem bridge p K).numRetries = K := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhausted requests occupy the first target slot instead of shifting successful indices. -/
theorem failed_slot_index :
    targetHistory bridge [⟨false, false, none⟩, ⟨true, false, some (word, 1)⟩] =
      [(false, false, none), (true, false, some 1)] ∧
    witnessIndex bridge false
      [⟨false, false, none⟩, ⟨true, false, some (word, 1)⟩] (false, 2, true) = 1 := by
  decide

/-- The named hash collision retains the successful slot after a failed slot. -/
theorem hash_collision_after_failure :
    SM_DT_RTCR_IsCollision (hashProblem bridge 2 1) false
      (targetHistory bridge [⟨false, false, none⟩, ⟨true, false, some (word, 1)⟩])
      (1, false, 2) = true := by decide

/-- No target index is manufactured from a failed-only source history. -/
theorem failed_only_index :
    witnessIndex bridge false [⟨false, false, none⟩] (false, 2, false) = 1 ∧
    SM_DT_RTCR_IsCollision (hashProblem bridge 1 0) false
      (targetHistory bridge [⟨false, false, none⟩]) (0, false, 2) = false := by decide

/-- Zero retries retain exhausted requests in both coupled histories. -/
theorem coupled_zero_retry :
    (sourceCoupledChallenge bridge 1 0 false (false, false)).run ([], []) =
      pure (none, [⟨false, false, none⟩], [(false, false, none)]) := rfl

/-- A repeated epoch preserves its failed slot in both coupled histories. -/
theorem coupled_duplicate :
    (sourceCoupledChallenge bridge 2 1 false (true, false)).run
      ([⟨false, false, none⟩], [(false, false, none)]) =
      pure (none, [⟨false, false, none⟩], [(false, false, none)]) := rfl

/-- The source adversary adapts its new pair to the returned successful randomizer. -/
@[expose] def bridgeAdversary (p K : ℕ) : Adversary (encodingProblem bridge p K) where
  find _ := do
    let answer ← challenge false false
    return (false, if answer.map Prod.snd == some 1 then 2 else 1, false)

/-- The actual source experiment is the source observation of the common computation. -/
theorem source_program (p K : ℕ) :
    experiment (bridgeAdversary p K) =
      sourceObservation bridge <$> runCoupled bridge p K (bridgeAdversary p K) :=
  source_experiment_eq_coupled bridge p K (bridgeAdversary p K)

/-- The actual reduced experiment uses the same common computation and its target observation. -/
theorem target_program (p K : ℕ) :
    SM_DT_RTCR_Experiment (reduction bridge p K (bridgeAdversary p K)) =
      targetObservation bridge p K <$> runCoupled bridge p K (bridgeAdversary p K) :=
  target_experiment_eq_coupled bridge p K (bridgeAdversary p K)

/-- The public native winning-mass theorem applies without a uniform-seed premise. -/
theorem bridge_bound (p K : ℕ) :
    advantage (bridgeAdversary p K) ≤
      SM_DT_RTCR_Advantage (reduction bridge p K (bridgeAdversary p K)) :=
  advantage_le_hash bridge p K (bridgeAdversary p K)

end IncomparableEncoding.TargetCollisionProbe
