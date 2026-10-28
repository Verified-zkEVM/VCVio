/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQuery

/-! # Deferred tables for adaptive algebraic reductions

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). A single table interprets the entire adaptive
execution and its final extraction lookups. Ordinary random queries remain independent.
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

/-- An entire lazy execution, including adaptive extraction lookups, has the law obtained by
sampling a full table first. The initial cache overrides the sampled table. -/
theorem simulateQ_romImpl_evalDistEq_table {D R α : Type} [DecidableEq D] [Finite D]
    [SampleableType R] [SampleableType (D → R)]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (c : (D →ₒ R).QueryCache) :
    (simulateQ (D →ₒ R).romImpl oa).run' c =ᵈ
      (do
        let table ← $ᵗ (D → R)
        simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c table))) oa) := by
  let : MeasurableSpace ((α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache) := ⊤
  have h := (EvalDistEq.of_evalDist_eq
    (evalDist_randomOracleLoggedRun_eq_fixedTable_finite oa c)).map (fun z => z.1.1)
  simp only [StateT.run'_eq, ← randomOracleLoggedRun_project, Functor.map_map]
  simpa only [map_bind, fixedTableLoggedRun_completeTable_project] using h

end GroupModel.LinearFunctional
