/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.SimSemantics.OptionT.Answer

/-!
# Stop an adaptive caller after a refusal

The refused second query increments the counter.
Its continuation cannot issue a third query.
-/

open OracleComp OracleSpec

public section

namespace VCVioTest.OptionalAnswer

/-- A Boolean request with a Boolean answer. -/
abbrev Calls := Bool →ₒ Bool

/-- Count every call, including a false request that the handler refuses. -/
def backend : QueryImpl Calls (OptionT (StateT Nat ProbComp)) :=
  fun b => OptionT.mk <| StateT.mk fun n => pure (if b then some false else none, n + 1)

/-- Use the first reply as the second request, then request once more on success. -/
def caller : OracleComp Calls Bool := do
  let reply ← Calls.query true
  let _ ← Calls.query reply
  Calls.query true

/-- The refusal leaves two calls on the counter and stops the third call. -/
theorem refused_second_query :
    (simulateQ (spec := OptionalAnswer.Spec Calls) (fun t => (backend t).run)
    (OptionalAnswer.program caller)).run 0 = pure (none, 2) := by
  rw [OptionalAnswer.simulate_program]
  simp [caller, backend, OptionT.run_bind, StateT.run_bind, Option.elimM]

end VCVioTest.OptionalAnswer
