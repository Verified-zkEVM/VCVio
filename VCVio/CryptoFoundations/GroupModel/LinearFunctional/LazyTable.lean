/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! # Deferred tables for adaptive algebraic reductions

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). A single table interprets the entire adaptive
execution and its final extraction lookups. Ordinary random queries remain independent.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- An entire lazy execution, including adaptive extraction lookups, has the law obtained by
sampling a full table first. The initial cache overrides the sampled table. -/
theorem simulateQ_romImpl_evalDistEq_table {D R α : Type} [DecidableEq D] [Finite D]
    [SampleableType R] [SampleableType (D → R)]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (c : (D →ₒ R).QueryCache) :
    (simulateQ (D →ₒ R).romImpl oa).run' c =ᵈ
      (do
        let table ← $ᵗ (D → R)
        simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c table))) oa) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (OracleComp.EvalDistEq.bind_const ($ᵗ (D → R)) (pure a)).symm
  | query_bind q next ih =>
      cases q with
      | inl n =>
          have hl : (simulateQ (D →ₒ R).romImpl
              (liftM ((unifSpec + (D →ₒ R)).query (.inl n)) >>= next)).run' c =
              (unifSpec.query n : ProbComp _) >>= fun r =>
                (simulateQ (D →ₒ R).romImpl (next r)).run' c := by
            simp [romImpl, unifFwdImpl]
          rw [hl]
          simp only [simulateQ_bind, simulateQ_spec_query, unifFwdAnswerImpl]
          exact (_root_.EvalDistEq.bind_right _ fun r => ih r c).trans
            (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
      | inr d =>
          have hl : (simulateQ (D →ₒ R).romImpl
              (liftM ((unifSpec + (D →ₒ R)).query (.inr d)) >>= next)).run' c =
              ((D →ₒ R).randomOracle d).run c >>= fun z =>
                (simulateQ (D →ₒ R).romImpl (next z.1)).run' z.2 := by
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq,
              StateT.run_bind, map_bind, romImpl_apply_inr]
            rfl
          rw [hl]
          have hr : (do
              let table ← $ᵗ (D → R)
              simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c table)))
                (liftM ((unifSpec + (D →ₒ R)).query (.inr d)) >>= next)) =
              (do
                  let table ← $ᵗ (D → R)
                  simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c table)))
                    (next (completeTable c table d))) := by
            apply bind_congr
            intro table
            rw [simulateQ_bind, simulateQ_spec_query]
            change (pure (completeTable c table d) >>= _) = _
            rw [pure_bind]
          rw [hr]
          cases hc : c d with
          | none =>
              rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
              trans ($ᵗ R >>= fun r => $ᵗ (D → R) >>= fun table =>
                simulateQ (unifFwdAnswerImpl
                  (QueryImpl.ofFn (completeTable (c.cacheQuery d r) table))) (next r))
              · exact _root_.EvalDistEq.bind_right _ fun r => ih r (c.cacheQuery d r)
              · let ψ := fun table =>
                  simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c table)))
                    (next (completeTable c table d))
                have h (r : R) (table : D → R) :
                    simulateQ (unifFwdAnswerImpl
                  (QueryImpl.ofFn (completeTable (c.cacheQuery d r) table))) (next r) =
                      ψ (Function.update table d r) := by
                  dsimp [ψ]
                  rw [completeTable_cacheQuery, ← completeTable_update_of_none c table hc r]
                  simp
                simp_rw [h]
                let : MeasurableSpace R := ⊤
                let : MeasurableSpace α := ⊤
                exact EvalDistEq.of_evalDist_eq
                  (evalDist_bind_bind_update_dependent d ($ᵗ R) ($ᵗ (D → R))
                    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample ψ)
          | some r =>
              rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
              simpa only [completeTable, hc, Option.getD_some] using ih r c

end GroupModel.LinearFunctional
