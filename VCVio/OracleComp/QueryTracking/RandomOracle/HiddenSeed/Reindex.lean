/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Reindex private derivation labels

A bijection changes the names of private queries and transports their complete table.
The public and uniform oracles keep their original queries and caches.
-/

public section
open OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery
namespace SecretEncoding

variable {I X Y R : Type} (pub : OracleSpec I) (e : X ≃ Y)

/-- Apply the bijection only on the private derivation branch. -/
@[expose] def reindexQueries : QueryImpl (pub.withDerivations X R)
    (OracleComp (pub.withDerivations Y R))
  | .inl t => liftM ((pub.withDerivations Y R).query (.inl t))
  | .inr x => liftM ((pub.withDerivations Y R).query (.inr (e x)))

/-- The public cache stays intact and the private table follows the inverse bijection. -/
@[expose] def reindexState (s : SplitCache pub X R) : SplitCache pub Y R :=
  (s.1, .ofFn (fun y => s.2 (e.symm y)))

@[simp] theorem reindexState_apply (s : SplitCache pub X R) (x : X) :
    (reindexState pub e s).2 (e x) = s.2 x := by
  change s.2 (e.symm (e x)) = s.2 x
  exact congrArg (β := Option R) (fun k : X => s.2 k) (e.symm_apply_apply x)

theorem reindexState_symm (s : SplitCache pub X R) :
    reindexState pub e.symm (reindexState pub e s) = s := by
  refine Prod.ext rfl ?_
  apply QueryCache.ext
  intro x
  exact reindexState_apply pub e s x

private theorem reindex_store [DecidableEq X] [DecidableEq Y]
    (s : SplitCache pub X R) (x : X) (r : R) :
    reindexState pub e (s.1, s.2.cacheQuery x r) =
      (s.1, (reindexState pub e s).2.cacheQuery (e x) r) := by
  refine Prod.ext rfl ?_
  apply QueryCache.ext
  intro y
  by_cases h : y = e x
  · subst y
    rw [reindexState_apply, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · have ne : e.symm y ≠ x := fun hxy => h (e.symm_apply_eq.mp hxy)
    simp [reindexState, QueryCache.cacheQuery_of_ne _ _ h, QueryCache.cacheQuery_of_ne _ _ ne]

variable [DecidableEq I] [DecidableEq X] [DecidableEq Y] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- Both executions draw the same words and return the same observations after reindexing.
This equality of computations holds from arbitrary, independently populated private tables. -/
theorem reindex_ideal {α : Type} (body : OracleComp (pub.withDerivations X R) α)
    (start : SplitCache pub X R) :
    Prod.map id (reindexState pub e) <$>
      (simulateQ (idealImpl pub X R) body).run start =
    (simulateQ (idealImpl pub Y R) (simulateQ (reindexQueries pub e) body)).run
      (reindexState pub e start) := by
  rw [← QueryImpl.simulateQ_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ ?_ _ _
  rintro ((n | t) | x) s
  · simp [QueryImpl.compose, reindexQueries, idealImpl, Functor.map_map, Prod.map]
  · simp [QueryImpl.compose, reindexQueries, idealImpl, reindexState, Functor.map_map, Prod.map]
  · simp only [QueryImpl.compose, reindexQueries, simulateQ_spec_query]
    cases h : s.2 x with
    | some v =>
      rw [idealImpl_run_derive_some h, idealImpl_run_derive_some
        (show (reindexState pub e s).2 (e x) = some v by simpa using h)]
      rfl
    | none =>
      rw [idealImpl_run_derive_none h, idealImpl_run_derive_none
        (show (reindexState pub e s).2 (e x) = none by simpa using h)]
      simp only [Functor.map_map, Prod.map_apply, id_eq, reindex_store]
      rfl

end SecretEncoding
