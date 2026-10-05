/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Joint measure laws for stateful oracle interpretation

Local equality of the joint response and retained-state measures preserves the complete
result/state measure of every adaptive oracle computation. The response/state products
carry explicit discrete measurable structures. This interface retains service state in its
premise because later adaptive calls may reveal changes hidden from the immediate response.

A probabilistic state map that intertwines two handlers step by step, `QueryImpl.Intertwines`,
intertwines their runs of every oracle computation
(`QueryImpl.Intertwines.evalDist_simulateQ_run`).

Stateful simulation from a sampled initial state satisfies an event with probability one
whenever every structurally possible output of the original computation does: simulation only
shrinks operational support, so no property of the handler is needed.
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

namespace QueryImpl

open OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type}

/-- A probabilistic state map `fill` intertwines `impl₁` with `impl₂`: from every state, a step
of `impl₁` followed by `fill` of its post-state has, before any continuation, the distribution of
`fill` followed by the step of `impl₂`. With `fill = pure` this is the equality of step measures
of `OracleComp.evalDist_simulateQ_run_congr_of_forall`. -/
@[expose] def Intertwines (fill : σ₁ → ProbComp σ₂)
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp)) :
    Prop :=
  ∀ t s {γ : Type} [MeasurableSpace γ] (f : spec.Range t → σ₂ → ProbComp γ),
    𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (impl₂ t).run s' >>= fun z ↦ f z.1 z.2]

/-- If `fill` intertwines `impl₁` with `impl₂` step by step, it intertwines their runs of every
oracle computation. -/
theorem Intertwines.evalDist_simulateQ_run {fill : σ₁ → ProbComp σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ ProbComp)} {impl₂ : QueryImpl spec (StateT σ₂ ProbComp)}
    (h : Intertwines fill impl₁ impl₂) {α γ : Type} [MeasurableSpace γ]
    (oa : OracleComp spec α) (s : σ₁) (f : α → σ₂ → ProbComp γ) :
    𝒟[(simulateQ impl₁ oa).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (simulateQ impl₂ oa).run s' >>= fun z ↦ f z.1 z.2] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    calc _ = 𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= fun s' ↦
          (simulateQ impl₂ (k z.1)).run s' >>= fun w ↦ f w.1 w.2] :=
          evalDist_bind_congr_of_support _ _ _ fun z _ ↦ ih z.1 z.2
      _ = _ := h t s fun u s' ↦ (simulateQ impl₂ (k u)).run s' >>= fun w ↦ f w.1 w.2

end QueryImpl

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
