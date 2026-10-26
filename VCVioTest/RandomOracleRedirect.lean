/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Redirect

/-!
# A redirect that moves a query

The oracle is a random oracle on `Bool`. The redirect `toFalse` answers every query at the point
`false`, so it moves the query at `true` and passes the query at `false` on unchanged.

* The redirect changes a program: on the cache holding only the point `false`, the query at
  `true` fails to replay, while its redirected form succeeds. So the view of that cache through
  `toFalse` differs from the cache, and the replay identity relates two different readings.
* On the cache holding both points, the view disagrees with the cache at `true`, so the cache is
  not below its view; restricting the cache to `false` drops the entry at `true`, and the
  restriction is below the view.
* The view through `expand`, from a one-point signature into `Bool`, reads the entry at `false`.
* An encoding that sends both points to one underlying query cannot see `toFalse`, and undoes
  `expand`, although both change the program.
-/

public section

open OracleComp OracleSpec

namespace RedirectToy

/-- A random oracle on `Bool`. -/
abbrev spec := Bool →ₒ Bool

/-- Answer every query at the point `false`. -/
def toFalse : QueryImpl spec (OracleComp spec) := fun _ => spec.query false

/-- The cache holding the answer `b` at `false` and nothing at `true`. -/
def cacheAt (b : Bool) : spec.QueryCache := (∅ : spec.QueryCache).cacheQuery false b

/-- The cache holding `true` at `false` and `false` at `true`. -/
def both : spec.QueryCache := (cacheAt true).cacheQuery true false

theorem cacheAt_true (b : Bool) : cacheAt b true = none := by
  simp [cacheAt, QueryCache.cacheQuery_of_ne]

theorem cacheAt_le_both : cacheAt true ≤ both := QueryCache.le_cacheQuery _ (cacheAt_true true)

theorem simulateQ_cacheAt_query_true (b : Bool) :
    simulateQ (cacheAt b).toPartialImpl (spec.query true : OracleComp spec Bool) = none := by
  simp [cacheAt, QueryCache.cacheQuery_of_ne]

theorem simulateQ_viewBy_cacheAt_query_true (b : Bool) :
    simulateQ ((cacheAt b).viewBy toFalse).toPartialImpl
      (spec.query true : OracleComp spec Bool) = some b := by
  rw [QueryCache.simulateQ_viewBy_toPartialImpl]
  simp [toFalse, cacheAt]

/-- The redirect changes the program. -/
theorem simulateQ_toFalse_ne (b : Bool) :
    simulateQ toFalse (spec.query true : OracleComp spec Bool) ≠ spec.query true := by
  intro h
  have := simulateQ_viewBy_cacheAt_query_true b
  rw [QueryCache.simulateQ_viewBy_toPartialImpl, h, simulateQ_cacheAt_query_true] at this
  exact Option.some_ne_none b this.symm

theorem viewBy_cacheAt_ne (b : Bool) : (cacheAt b).viewBy toFalse ≠ cacheAt b := fun h => by
  have := simulateQ_viewBy_cacheAt_query_true b
  rw [h, simulateQ_cacheAt_query_true] at this
  exact Option.some_ne_none b this.symm

/-! ## Restriction on a cache with both points set -/

theorem viewBy_both_true : both.viewBy toFalse true = some true ∧ both true = some false := by
  constructor <;> simp [toFalse, both, cacheAt, QueryCache.cacheQuery_of_ne]

theorem viewBy_both_false : both.viewBy toFalse false = some true := by
  rw [QueryCache.viewBy_apply_of_eq_query (ρ := toFalse) rfl]
  simp [both, cacheAt, QueryCache.cacheQuery_of_ne]

theorem not_both_le_viewBy : ¬ both ≤ both.viewBy toFalse := fun h => by
  have := h viewBy_both_true.2
  rw [viewBy_both_true.1] at this
  exact Bool.false_ne_true (Option.some.inj this).symm

theorem filter_both_ne : QueryCache.filter (· = false) both ≠ both := fun h => by
  have := congrArg (· true) h
  simp [both] at this

theorem filter_both_le_viewBy : QueryCache.filter (· = false) both ≤ both.viewBy toFalse :=
  QueryCache.filter_le_viewBy _ fun t ht => by subst ht; rfl

theorem cacheAt_le_filter_both : cacheAt true ≤ QueryCache.filter (· = false) both :=
  QueryCache.le_filter cacheAt_le_both fun t ht => by
    cases t
    · rfl
    · simp [cacheAt_true] at ht

theorem viewBy_cacheAt_le_viewBy_both : (cacheAt true).viewBy toFalse ≤ both.viewBy toFalse :=
  QueryCache.viewBy_mono cacheAt_le_both toFalse

/-! ## Redirects across signatures -/

/-- One underlying query answering both points of `spec`. -/
abbrev single := Unit →ₒ Bool

/-- Send every point of `spec` to the one point of `single`. -/
def collapse : QueryImpl spec (OracleComp single) := fun _ => single.query ()

/-- Answer the one point of `single` at the point `false` of `spec`. -/
def expand : QueryImpl single (OracleComp spec) := fun _ => spec.query false

theorem viewBy_both_expand : both.viewBy expand () = some true := by
  simp [expand, both, cacheAt, QueryCache.cacheQuery_of_ne]

/-- The collapsing encoding cannot see the redirect. -/
theorem simulateQ_collapse_simulateQ_toFalse {α : Type} (oa : OracleComp spec α) :
    simulateQ collapse (simulateQ toFalse oa) = simulateQ collapse oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => by simp [toFalse, collapse]) oa

/-- The collapsing encoding undoes `expand`. -/
theorem simulateQ_collapse_simulateQ_expand {α : Type} (oa : OracleComp single α) :
    simulateQ collapse (simulateQ expand oa) = oa := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' single)
    (fun _ => by simp [expand, collapse]) oa, simulateQ_id']

end RedirectToy
