/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! # Completed tables for fixed-table runs

Forgetting the cache and log of a fixed-table execution whose table completes the initial cache
gives direct interpretation of the program by that table
(`fixedTableLoggedRun_completeTable_project`). Together with
`evalDist_simulateQ_romImpl_run'_eq_completeTable`, one sampled table then interprets an entire
adaptive execution, including later extraction lookups, while uniform queries stay independent.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Forgetting the cache and log of a completed fixed-table execution gives direct table
interpretation. The completion preserves all answers already present in the initial cache. -/
theorem fixedTableLoggedRun_completeTable_project {D α : Type} {R : D → Type}
    [DecidableEq D] (oa : OracleComp (unifSpec + ofFn R) α)
    (c : (ofFn R).QueryCache) (g : ∀ d, R d) :
    (fun z => z.1.1) <$> fixedTableLoggedRun oa (completeTable c g) c =
      simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c g))) oa := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [fixedTableLoggedRun]
  | query_bind q next ih =>
      rw [fixedTableLoggedRun_bind, simulateQ_bind, simulateQ_spec_query]
      cases q with
      | inl n =>
          rw [fixedTableLoggedRun_uniformQuery]
          simpa [unifFwdAnswerImpl] using
            bind_congr (x := (unifSpec.query n : ProbComp _)) (fun r => ih r c)
      | inr d =>
          rw [fixedTableLoggedRun_hashQuery]
          cases hc : c d with
          | none =>
              rw [QueryImpl.withCaching_run_none _ hc]
              simp only [add_apply_inr, PFunctor.Handler.liftTarget_apply,
                ofPFunctor_toPFunctor, QueryImpl.ofFn_apply, Functor.map_map, bind_map_left,
                List.cons_append, List.nil_append, map_bind]
              have hi := ih (completeTable c g d) (c.cacheQuery d (completeTable c g d))
              rw [completeTable_cacheQuery_value] at hi
              exact hi
          | some r =>
              rw [QueryImpl.withCaching_run_some _ hc]
              simp only [map_pure, pure_bind, Functor.map_map]
              change _ = ((pure (completeTable c g d) : ProbComp _) >>= _)
              have hval : completeTable c g d = r := by simp [completeTable, hc]
              rw [hval, pure_bind]
              exact ih r c

end GroupModel.LinearFunctional
