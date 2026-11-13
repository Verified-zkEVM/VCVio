/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF.DomainTransport

/-!
# Native PRF input transport controls

Two projections at a repeated input use one complete pair response. An unrelated preprogrammed
cache entry lies outside the embedding; the whole native run projects back to the small cache.
-/

public section
namespace PRFDomainTransportProbe
open OracleComp OracleSpec PRFScheme.DomainTransport

/-- Correlated observations of the same cached response, with private sampling between calls. -/
@[expose] def program : OracleComp (PRFScheme.PRFOracleSpec Bool (Bool × Bool)) (Bool × Bool) := do
  let first ← PRFScheme.functionQuery false
  let _ ← (PRFScheme.PRFOracleSpec Bool (Bool × Bool)).query (.inl 0)
  let second ← PRFScheme.functionQuery false
  pure (first.1, !second.2)

/-- A fixed complete response programmed at a coordinate outside the embedding. -/
@[expose] def cache : ((Bool ⊕ Unit) →ₒ (Bool × Bool)).QueryCache :=
  QueryCache.ofFn fun input => if input = Sum.inr () then some (true, false) else none

/-- The outside entry contributes nothing to the pulled-back cache. -/
theorem cache_pullback_empty : pullbackCache Sum.inl cache = ∅ := by
  ext input
  simp [pullbackCache, cache]

/-- Entire output and complete in-image cache agree, including the repeated pair response. -/
theorem native_ideal_run :
    Prod.map id (pullbackCache Sum.inl) <$>
        (simulateQ PRFScheme.prfIdealQueryImpl
          (simulateQ (inputMap (Sum.inl : Bool → Bool ⊕ Unit)) program)).run cache =
      (simulateQ PRFScheme.prfIdealQueryImpl program).run ∅ := by
  rw [ideal_run Sum.inl Sum.inl_injective, cache_pullback_empty]

/-- Input transport charges both function calls, even though they use the same cached input. -/
theorem two_function_calls :
    IsQueryBoundP (simulateQ (inputMap (Sum.inl : Bool → Bool ⊕ Unit)) program)
      (fun query => query.isRight = true) 2 := by
  rw [functionQuery_bound_iff]
  simp [program, PRFScheme.functionQuery, isQueryBoundP_query_bind_iff]

/-- Cache reuse does not lower the pathwise function-query count to one. -/
theorem not_one_function_call :
    ¬ IsQueryBoundP (simulateQ (inputMap (Sum.inl : Bool → Bool ⊕ Unit)) program)
      (fun query => query.isRight = true) 1 := by
  rw [functionQuery_bound_iff]
  simp [program, PRFScheme.functionQuery, isQueryBoundP_query_bind_iff]

end PRFDomainTransportProbe
