/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVioTest.IncomparableEncoding.TargetCollisionResistance

/-!
# Encoding-to-hash bridge tests

A concrete bridge over a fallible encoding checks that exhausted queries keep their slots in the
SM-rTCR history, so the reduction names the right target index, and that the coupled handler
records exhausted and repeated queries in both histories.
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
  encode_eq := by
    intro pp msg r ep
    by_cases h : r = 0
    · simp [enc, h]
    · simp [enc, h]
      rfl

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

end IncomparableEncoding.TargetCollisionProbe
