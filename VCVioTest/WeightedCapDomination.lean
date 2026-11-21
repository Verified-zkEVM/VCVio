/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.WeightedCap.Domination

/-!
# Relaxed tariffs on queries that already caused a persistent event
-/

public section
open OracleSpec OracleComp
namespace OracleComp.WeightedCap.DominationTest

abbrev Calls := Bool →ₒ Unit

/-- Each selected request sets the persistent flag. -/
private def impl : QueryImpl Calls (StateT Bool ProbComp) :=
  fun t => StateT.mk fun s => pure ((), s || t)

private def twice : OracleComp Calls Unit := do
  let _ ← liftM (Calls.query true)
  liftM (Calls.query true)

/-- Refusing the second query retains the flag set by the first. -/
example : (simulateQ impl (capCompOpt (fun _ => 1) 1 twice)).run false =
    pure (none, true) := by
  rfl

/-- Dropping the charge lets the same marked request return, without clearing the flag. -/
example : (simulateQ impl (capCompOpt (fun _ => 0) 1 twice)).run false =
    pure (some (), true) := by
  rfl

/-- Arbitrary continuations can use the different fees and the same persistent flag. -/
example (caller : OracleComp Calls Bool) (s : Bool) (n : Nat) :
    let event (z : Option Bool × Bool) := z.1.elim False (fun b => b = true) ∨ z.2 = true
    Pr{let z ← (simulateQ impl (capCompOpt (fun _ => 1) n caller)).run s}[event z] ≤
      Pr{let z ← (simulateQ impl (capCompOpt (fun _ => 0) n caller)).run s}[event z] := by
  intro event
  apply prEvent_cap_le_cap_of_preserves impl _ _ (fun _ => Nat.zero_le _) (· = true) _
    (fun b _ => b = true) caller n n le_rfl s
  intro t initial bad z hz
  rw [impl, StateT.run_mk, mem_support_pure_iff] at hz
  simp [hz, bad]

end OracleComp.WeightedCap.DominationTest
