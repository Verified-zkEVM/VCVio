/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal.Programming

/-!
# Nonfinite, repeated-coordinate and colliding-input programming client

This is the deterministic full-state/cache program, with arbitrary initial cache.
It makes no sampling, freshness, query-cost or runtime claim.
-/

public section
open OracleComp OracleSpec RandomOracleTraversal RandomOracleTraversal.Programming

namespace VCVioTest.QueryTracking.TraversalProgramming

/-- Repeated coordinates and input collisions retain the full target and left-to-right cache. -/
theorem ordered_repeated_program (cache : QueryCache (Nat →ₒ Nat)) :
    program (fun (_ : Nat) (_ : Nat → Nat) => 5)
      (fun node cells answer => Function.update cells node answer)
      (fun node => if node = 0 then 7 else 11) [0, 1, 0] (fun _ => 3) cache =
      ((fun key => if key = 0 then 7 else if key = 1 then 11 else 3),
        ((cache.cacheQuery 5 7).cacheQuery 5 11).cacheQuery 5 7) := by
  have result := OracleComp.RandomOracleTraversal.Programming.program_eq_cacheFrom
    (Index := Nat) (Key := Nat) (Cell := Nat) (Input := Nat) (Output := Nat)
    id (fun _ => []) (fun _ _ => 5) (fun _ answer => answer)
    (by intros; rfl) (fun node => if node = 0 then 7 else 11) [0, 1, 0]
    (fun _ => 3) (fun key => if key = 0 then 7 else if key = 1 then 11 else 3)
    (by intro position child member; simp at member)
    (by
      intro key outside
      have zero : key ≠ 0 := Ne.symm (outside 0 (by simp))
      have one : key ≠ 1 := Ne.symm (outside 1 (by simp))
      simp [zero, one])
    (by
      intro node member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp)
    cache
  simpa [cacheFrom] using result

/-- The last occurrence writes the retained full answer even with a preloaded arbitrary cache. -/
theorem repeated_last_answer (cache : QueryCache (Nat →ₒ Nat)) :
    (program (fun (_ : Nat) (_ : Nat → Nat) => 5)
      (fun node cells answer => Function.update cells node answer)
      (fun node => if node = 0 then 7 else 11) [0, 1, 0] (fun _ => 3) cache).2 5 = some 7 := by
  rw [ordered_repeated_program]
  exact QueryCache.cacheQuery_self _ _ _

/-- An unscheduled cell cannot acquire an unrelated target value. -/
theorem unscheduled_target_requires_agreement :
    ¬ AgreesOutside id ([] : List Nat) (fun _ : Nat => 0) (fun _ => 1) := by
  intro agrees
  have impossible : (0 : Nat) = 1 := agrees 0 (by simp)
  omega

/-- Read-before-write excludes reading a key at the position that overwrites it. -/
theorem self_read_not_ordered :
    ¬ ReadBeforeWrite id (fun node : Nat => [node]) [0] := by
  intro order
  exact order ⟨0, by decide⟩ 0 (by simp) 0 (by simp) rfl

end VCVioTest.QueryTracking.TraversalProgramming
