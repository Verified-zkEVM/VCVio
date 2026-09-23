/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.QueryTracking.CountingOracle

/-!
# Additive counting without function-instance leakage

Ordinary functions keep their pointwise multiplicative monoid. Counting instrumentation uses
an additive writer and preserves both query answers and per-index counts. Failure observations
distinguish a writer outside an optional result from an optional result outside a writer.
-/

public section

open OracleSpec OracleComp

namespace VCVioTest.ModuleAPI.Counting

example : (inferInstance : Monoid (Bool → Nat)).one false = 1 := rfl

example : (inferInstance : Monoid (Bool → Nat)).mul (fun _ => 2) (fun _ => 3) false = 6 := rfl

/-- Two query labels, both returning booleans. -/
abbrev signature : OracleSpec Bool := fun _ => Bool

/-- Three queries with a repeated label and an observed answer. -/
def program : OracleComp signature Bool := do
  let answer ← query (spec := signature) false
  let _ ← query (spec := signature) true
  let _ ← query (spec := signature) false
  pure answer

/-- A deterministic implementation reflecting each query label. -/
def handler : QueryImpl signature Id := fun label => pure label

example : (simulateQ handler.withCounting program).runAdd.run.1 = false := by
  simp [program, QueryImpl.withCounting_apply, handler]

example : (simulateQ handler.withCounting program).runAdd.run.2 false = 2 := by
  simp [program, QueryImpl.withCounting_apply, handler, QueryCount.single]

example : (simulateQ handler.withCounting program).runAdd.run.2 true = 1 := by
  simp [program, QueryImpl.withCounting_apply, handler, QueryCount.single]

example :
    (simulateQ handler.withCounting (pure true : OracleComp signature Bool)).runAdd.run.2 = 0 := by
  simp

/-- An implementation that aborts before returning an answer. -/
def refusing : QueryImpl signature Option := fun _ => none

example : (simulateQ refusing.withCounting program).runAdd = none := by
  simp [program, QueryImpl.withCounting_apply, refusing]

/-- Optional results inside a writer retain the cost accumulated before failure. -/
def retainedFailure : OptionT (AddWriterT (QueryCount Bool) Id) Bool := do
  liftM (AddWriterT.addTell (M := Id) (QueryCount.single false))
  failure

example : retainedFailure.run.runAdd.run.1 = none := by decide

example : retainedFailure.run.runAdd.run.2 false = 1 := by decide

end VCVioTest.ModuleAPI.Counting
