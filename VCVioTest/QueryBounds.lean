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

/-- Two predicates every query satisfies hold jointly: every query of `adaptive` is to an index
that is `true` or `false`, and to an index equal to itself. -/
example : AllQueriesSatisfy adaptive fun t => (t = true ∨ t = false) ∧ t = t :=
  (allQueriesSatisfy_of_forall (fun t => by cases t <;> simp) adaptive).and
    (allQueriesSatisfy_of_forall (fun _ => rfl) adaptive)

/-- With only the allowed query, the budget for its complement is zero. -/
example : IsQueryBoundP (liftM (flagSpec.query true) : OracleComp flagSpec Bool)
    (fun t => ¬ t = true) 0 := by
  rw [isQueryBoundP_zero_iff]
  simp

/-- Each index is queried at most once, on every response path. -/
theorem adaptive_isQueryBoundP_eq (b : Bool) : IsQueryBoundP adaptive (· = b) 1 := by
  cases b <;> simp [adaptive]

/-- Budgets on the two indices add up to a budget on their disjunction: every query of
`adaptive`, and there are two on the path through a true answer. -/
example : IsQueryBoundP adaptive (fun t => t = true ∨ t = false) 2 :=
  (adaptive_isQueryBoundP_eq true).or (adaptive_isQueryBoundP_eq false)

/-- The sum is not sharp when the predicates overlap: a single query, counted under both. -/
example : IsQueryBoundP (liftM (flagSpec.query true) : OracleComp flagSpec Bool)
    (fun t => t = true ∨ t = true) 2 :=
  IsQueryBoundP.or (p := (· = true)) (q := (· = true)) (n := 1) (m := 1) (by simp) (by simp)

/-- This deterministic run avoids the forbidden branch and records the answer it received. -/
example :
    (simulateQ (QueryImpl.withLogging (m := Id)
      ((fun _ => false) : QueryImpl flagSpec Id)) adaptive).run.run =
    (false, ([⟨true, false⟩] : QueryLog flagSpec)) := by
  simp [adaptive, show Id.run false = false from rfl]

end VCVioTest.QueryBounds
