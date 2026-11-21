/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF.ProjectedQueries

/-!
# Full-response projection controls

Two different projections at the same input use the same cached complete response. Their outputs
are correlated even though only one Boolean component is exposed by each query list.
-/

public section
namespace VCVioTest.PRFProjectedQueries
open OracleComp OracleSpec PRFScheme.ProjectedQueries

private theorem one {D S R : Type} (project : S → R) (input : Fin 1 → D) :
    responseQueries project 1 input =
      (fun r => [project r]) <$> PRFScheme.functionQuery (input 0) := by
  simp [responseQueries, Fin.mOfFn, List.ofFn_succ, List.ofFn_zero,
    map_eq_bind_pure_comp]

/-- Two views at the same address share a complete pair response. -/
@[expose] def program :
    OracleComp (PRFScheme.PRFOracleSpec Unit (Bool × Bool)) (List Bool × List Bool) := do
  let left ← responseQueries Prod.fst 1 (fun _ => ())
  let right ← responseQueries (fun r : Bool × Bool => !r.1) 1 (fun _ => ())
  pure (left, right)

/-- The actual ideal handler draws once and retains the entire pair, including its hidden field. -/
theorem full_cache :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Unit) (R := Bool × Bool)) program).run ∅ =
      (fun r : Bool × Bool =>
        (([r.1], [!r.1]), (∅ : (Unit →ₒ (Bool × Bool)).QueryCache).cacheQuery () r)) <$>
          ($ᵗ (Bool × Bool)) := by
  simp [program, one, PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery,
    StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

/-- Eager accounting charges both calls even though the second response is already cached. -/
theorem two_calls : IsTotalQueryBound program 2 := by
  unfold program
  apply isTotalQueryBound_bind (n₂ := 1) (responseQueries_bound Prod.fst 1 (fun _ => ()))
  intro left
  apply isTotalQueryBound_bind (n₂ := 0) (responseQueries_bound (fun r : Bool × Bool => !r.1) 1
    (fun _ => ()))
  intro right
  trivial

end VCVioTest.PRFProjectedQueries
