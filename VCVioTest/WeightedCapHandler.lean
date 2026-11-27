/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.WeightedCap.Handler

/-!
# Effects of a refused request

The handler appends each admitted request to a list. A refused request adds no entry,
and earlier entries survive the refusal.
-/

public section

open OracleSpec OracleComp

namespace OracleComp.WeightedCap.HandlerTest

/-- Boolean requests are logged and return `()`. -/
abbrev Calls := Bool →ₒ Unit

private def record : QueryImpl Calls (StateM (List Bool)) :=
  fun t => modify (fun xs => xs ++ [t])

private def caller : OracleComp Calls Unit := do
  let _ ← liftM (Calls.query false)
  liftM (Calls.query true)

/-- The uncharged first action runs at zero budget. The refused action leaves no entry. -/
example : ((((simulateQ (guard (fun t => if t then 1 else 0) record) caller).run).run 0).run [])
    = ((none, 0), [false]) := by
  rfl

/-- One unit admits both actions and preserves the previously stored entries. -/
example : ((((simulateQ (guard (fun t => if t then 1 else 0) record) caller).run).run 1).run [true])
    = ((some (), 0), [true, false, true]) := by
  rfl

end OracleComp.WeightedCap.HandlerTest
