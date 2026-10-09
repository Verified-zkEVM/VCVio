/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Measure preservation by oracle simulation

A query implementation is observed through the output measures of its query answers. Two
implementations whose answer measures agree simulate every oracle computation to the same output
measure, and an implementation that denotes each query's configured answer measure preserves the
computation's own denotation. The target monad is arbitrary: any lawful measure semantics works,
including `OracleComp` itself and executable samplers.
-/

public section

open OracleSpec MeasureTheory

universe u v

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- Implementations whose query answers have the same measures simulate every computation to
the same output measure. -/
theorem evalDist_simulateQ_congr (impl₁ impl₂ : QueryImpl spec m)
    (h : ∀ t, 𝒟[impl₁ t] = 𝒟[impl₂ t]) {α : Type} [MeasurableSpace α]
    (oa : OracleComp spec α) :
    𝒟[simulateQ impl₁ oa] = 𝒟[simulateQ impl₂ oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, h t]
    simp_rw [ih]

/-- An implementation that denotes each query's configured answer measure preserves the output
measure of every simulated computation. -/
theorem evalDist_simulateQ_eq_of_forall [OracleSpec.IsMeasureSpec spec]
    (impl : QueryImpl spec m) (h : ∀ t, 𝒟[impl t] = OracleSpec.IsMeasureSpec.toMeasure t)
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) :
    𝒟[simulateQ impl oa] = 𝒟[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, h t, evalDist_liftM_query]
    simp_rw [ih]

end OracleComp
