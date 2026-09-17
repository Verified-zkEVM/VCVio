/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.EvalDist.Monad.Measure

/-!
# Joint measure laws for stateful oracle interpretation

Local equality of the joint response and retained-state measures preserves the complete
result/state measure of every adaptive oracle computation. The response/state products
carry explicit discrete measurable structures. This interface retains service state in its
premise because later adaptive calls may reveal changes hidden from the immediate response.
-/

public section

namespace OracleComp

open OracleSpec MeasureTheory

variable {ι S α : Type} {spec : OracleSpec ι}
  [MeasurableSpace S] [MeasurableSpace α]
  [∀ operation : spec.Domain, MeasurableSpace (spec.Range operation)]
  [∀ operation : spec.Domain, DiscreteMeasurableSpace (spec.Range operation × S)]

/-- Equal joint local kernels preserve the full result and retained service-state measure. -/
theorem evalDist_simulateQ_run_congr
    (left right : QueryImpl spec (StateT S ProbComp))
    (h : ∀ operation state, 𝒟[(left operation).run state] = 𝒟[(right operation).run state])
    (program : OracleComp spec α) (state : S) :
    𝒟[(simulateQ left program).run state] = 𝒟[(simulateQ right program).run state] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind operation next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, evalDist_bind_of_discrete]
    rw [h]
    apply Measure.bind_congr_right
    filter_upwards [] with output
    exact ih output.1 output.2

end OracleComp
