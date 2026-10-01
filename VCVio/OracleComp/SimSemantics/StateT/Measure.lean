/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Joint measure laws for stateful oracle interpretation

Local equality in distribution of the joint response and retained state preserves the
distribution of the complete result and state of every adaptive oracle computation. This
interface retains service state in its premise because later adaptive calls may reveal changes
hidden from the immediate response.

Stateful simulation from a sampled initial state satisfies an event with probability one
whenever every structurally possible output of the original computation does: simulation only
shrinks operational support, so no property of the handler is needed.
-/

public section

namespace OracleComp

open OracleSpec MeasureTheory

universe u v

/-- Implementations whose local steps, from every state, are equal in distribution give equal
distributions of the complete result and retained state. Neither the service state nor the
response needs a measurable structure. -/
theorem evalDistEq_simulateQ_run
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type u} {S α : Type} {spec : OracleSpec.{u, 0} ι}
    (left right : QueryImpl spec (StateT S m))
    (h : ∀ operation state, (left operation).run state =ᵈ (right operation).run state)
    (program : OracleComp spec α) (state : S) :
    (simulateQ left program).run state =ᵈ (simulateQ right program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact EvalDistEq.rfl
  | query_bind operation next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind]
    exact (h operation state).bind fun output ↦ ih output.1 output.2

/-- Implementations whose local steps, from every state, are equal in distribution give equal
measures of the complete result and retained state. -/
theorem evalDist_simulateQ_run_congr
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type u} {S α : Type} {spec : OracleSpec.{u, 0} ι} [MeasurableSpace (α × S)]
    (left right : QueryImpl spec (StateT S m))
    (h : ∀ operation state, (left operation).run state =ᵈ (right operation).run state)
    (program : OracleComp spec α) (state : S) :
    𝒟[(simulateQ left program).run state] = 𝒟[(simulateQ right program).run state] :=
  (evalDistEq_simulateQ_run left right h program state).evalDist_eq

/-- A stateful implementation that, from every state, denotes each query's configured answer
measure preserves the output measure of every simulated computation once the final state is
discarded. Only the answer marginal is constrained: the service state may evolve arbitrarily and
needs no measurable space. A caching oracle, whose answer from a warm cache is a Dirac measure,
does not satisfy the hypothesis. -/
theorem evalDist_simulateQ_run'_eq_of_forall
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type u} {S α : Type} {spec : OracleSpec.{u, 0} ι}
    [OracleSpec.AnswerMeasure spec] [MeasurableSpace α]
    (impl : QueryImpl spec (StateT S m))
    (h : ∀ t state,
      (impl t).run' state =ᵈ (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)))
    (program : OracleComp spec α) (state : S) :
    𝒟[(simulateQ impl program).run' state] = 𝒟[program] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind operation next ih =>
    let : MeasurableSpace (spec.Range operation × S) := ⊤
    let : MeasurableSpace (spec.Range operation) := ⊤
    have hfst : Measurable (Prod.fst : spec.Range operation × S → spec.Range operation) :=
      measurable_from_top
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      ← (h operation state).evalDist_eq, StateT.run'_eq, evalDist_map _ hfst,
      Measure.bind_map _ hfst Measurable.of_discrete]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall fun output ↦ by
      simpa only [StateT.run'_eq] using ih output.1 output.2)

end OracleComp

section simulateQ

open OracleComp

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- Simulating with a stateful implementation from a sampled initial state satisfies an event
with probability one whenever every possible output of the original computation is a present
value satisfying it. The hypothesis is on the original computation, whose queries may return
any value, so nothing about the implementation is needed. -/
theorem OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support
    (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (p : α → Prop)
    (h : ∀ o ∈ support oa, ∃ a, o = some a ∧ p a) :
    Pr{let a ← OptionT.mk (do let s ← init; (simulateQ impl oa).run' s)}[p a] = 1 := by
  refine OptionT.prEvent_mk_bind_eq_one_of_support init (prEvent_true_eq_one init) _ p
    fun s _ ↦ ?_
  rw [OracleComp.OptionT.prEvent_mk_eq_one_iff]
  exact fun o ho ↦ h o (support_simulateQ_run'_subset impl oa s ho)

end simulateQ
