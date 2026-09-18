/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native
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

universe u v

/-- Equality of joint local measures in every output space preserves adaptive execution.
The intermediate response/state type uses a discrete space locally; no product-space
discreteness or uniform sampling assumption is needed. -/
theorem evalDist_simulateQ_run_congr_of_forall
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type u} {S α : Type} {spec : OracleSpec.{u, 0} ι} [MeasurableSpace (α × S)]
    (left right : QueryImpl spec (StateT S m))
    (h : ∀ operation state, ∀ [MeasurableSpace (spec.Range operation × S)],
      𝒟[(left operation).run state] = 𝒟[(right operation).run state])
    (program : OracleComp spec α) (state : S) :
    𝒟[(simulateQ left program).run state] = 𝒟[(simulateQ right program).run state] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind operation next ih =>
    let : MeasurableSpace (spec.Range operation × S) := ⊤
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, evalDist_bind_of_discrete]
    rw [h]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall fun output ↦
      ih output.1 output.2)

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  {ι : Type u} {S α : Type} {spec : OracleSpec.{u, 0} ι}
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [MeasurableSpace S] [MeasurableSpace α]
  [∀ operation : spec.Domain, MeasurableSpace (spec.Range operation)]
  [∀ operation : spec.Domain, DiscreteMeasurableSpace (spec.Range operation × S)]

/-- Equal joint local kernels preserve the full result and retained service-state measure. -/
theorem evalDist_simulateQ_run_congr
    (left right : QueryImpl spec (StateT S m))
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
