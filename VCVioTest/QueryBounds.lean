/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Allowed-query predicates and adaptive response paths

A handler that returns false avoids the forbidden second query. The structural predicate must
nevertheless reject the program, since a true response reaches that query. The zero-budget bridge
must count forbidden indices, rather than the allowed first query.
-/

public section

namespace VCVioTest.QueryBounds

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery

abbrev flagSpec : OracleSpec Bool := fun _ => Bool

/-- Query the forbidden index only when the first answer is true. -/
def adaptive : OracleComp flagSpec Bool := do
  let answer ← liftM (flagSpec.query true)
  if answer then liftM (flagSpec.query false) else pure false

/-- All response paths are checked, including the path not taken by the handler below. -/
example : ¬ AllQueriesSatisfy adaptive (· = true) := by
  simp [adaptive, allQueriesSatisfy_query_bind_iff]

/-- With only the allowed query, the budget for its complement is zero. -/
example : IsQueryBoundP (liftM (flagSpec.query true) : OracleComp flagSpec Bool)
    (fun t => ¬ t = true) 0 := by
  rw [isQueryBoundP_zero_iff]
  simp

/-- This deterministic run avoids the forbidden branch and records the answer it received. -/
example :
    (simulateQ (QueryImpl.withLogging (m := Id)
      ((fun _ => false) : QueryImpl flagSpec Id)) adaptive).run.run =
    (false, ([⟨true, false⟩] : QueryLog flagSpec)) := by
  simp [adaptive, show Id.run false = false from rfl]

/-- Two bounds on one computation combine into one with a product budget. -/
example (htotal : adaptive.IsTotalQueryBound 2)
    (hper : adaptive.IsPerIndexQueryBound fun _ => 1) :
    IsQueryBound adaptive (2, fun _ : Bool => 1) (fun t p => 0 < p.1 ∧ 0 < p.2 t)
      (fun t p => (p.1 - 1, Function.update p.2 t (p.2 t - 1))) :=
  IsQueryBound.prod htotal hper

/-- A family of bounds on one computation combines into one with a budget for each member. -/
example (h : ∀ b : Bool, adaptive.IsTotalQueryBound (if b then 2 else 3)) :
    IsQueryBound adaptive (fun b : Bool => if b then 2 else 3) (fun _ p => ∀ i, 0 < p i)
      (fun _ p i => p i - 1) :=
  IsQueryBound.pi h

end VCVioTest.QueryBounds
