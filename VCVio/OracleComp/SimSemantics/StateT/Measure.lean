/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Joint measure laws for stateful oracle interpretation

Local equality in distribution of the joint response and retained state preserves the
distribution of the complete result and state of every adaptive oracle computation. This
interface retains service state in its premise because later adaptive calls may reveal changes
hidden from the immediate response.

A probabilistic state map that intertwines two handlers step by step, `QueryImpl.Intertwines`,
intertwines their runs of every oracle computation
(`QueryImpl.Intertwines.evalDist_simulateQ_run`). The step condition may be restricted to the
states satisfying an invariant that the first handler preserves (`QueryImpl.IntertwinesOn` and
`QueryImpl.IntertwinesOn.evalDist_simulateQ_run`), so a state map that is only meaningful on
reachable states, such as one drawing a value for each of finitely many cached points, still
intertwines whole runs.

Stateful simulation from a sampled initial state satisfies an event with probability one
whenever every possible output of the original computation does: simulation only
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
      Measure.bind_map hfst.aemeasurable Measurable.of_discrete.aemeasurable]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall fun output ↦ by
      simpa only [StateT.run'_eq] using ih output.1 output.2)

end OracleComp

namespace QueryImpl

open OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type}

/-- A probabilistic state map `fill` intertwines `impl₁` with `impl₂`: from every state, a step
of `impl₁` followed by `fill` of its post-state has, before any continuation, the distribution of
`fill` followed by the step of `impl₂`. With `fill = pure` this is the equality of step measures
of `OracleComp.evalDist_simulateQ_run_congr`. -/
@[expose] def Intertwines (fill : σ₁ → ProbComp σ₂)
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp)) :
    Prop :=
  ∀ t s {γ : Type} [MeasurableSpace γ] (f : spec.Range t → σ₂ → ProbComp γ),
    𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (impl₂ t).run s' >>= fun z ↦ f z.1 z.2]

/-- A probabilistic state map `fill` intertwines `impl₁` with `impl₂` on the states satisfying
`inv`: from every state satisfying `inv`, a step of `impl₁` followed by `fill` of its post-state
has, before any continuation, the distribution of `fill` followed by the step of `impl₂`. With the
trivial invariant this is `QueryImpl.Intertwines`. -/
@[expose] def IntertwinesOn (inv : σ₁ → Prop) (fill : σ₁ → ProbComp σ₂)
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp)) :
    Prop :=
  ∀ t s, inv s → ∀ {γ : Type} [MeasurableSpace γ] (f : spec.Range t → σ₂ → ProbComp γ),
    𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (impl₂ t).run s' >>= fun z ↦ f z.1 z.2]

/-- A state map that intertwines two handlers from every state intertwines them on the states
satisfying any invariant. -/
theorem Intertwines.intertwinesOn {fill : σ₁ → ProbComp σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ ProbComp)} {impl₂ : QueryImpl spec (StateT σ₂ ProbComp)}
    (h : Intertwines fill impl₁ impl₂) (inv : σ₁ → Prop) : IntertwinesOn inv fill impl₁ impl₂ :=
  fun t s _ ↦ h t s

/-- If `fill` intertwines `impl₁` with `impl₂` on the states satisfying an invariant that `impl₁`
preserves, it intertwines their runs of every oracle computation from every such state. -/
theorem IntertwinesOn.evalDist_simulateQ_run {inv : σ₁ → Prop} {fill : σ₁ → ProbComp σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ ProbComp)} {impl₂ : QueryImpl spec (StateT σ₂ ProbComp)}
    (h : IntertwinesOn inv fill impl₁ impl₂) (hinv : PreservesInv impl₁ inv) {α γ : Type}
    [MeasurableSpace γ] (oa : OracleComp spec α) (s : σ₁) (hs : inv s)
    (f : α → σ₂ → ProbComp γ) :
    𝒟[(simulateQ impl₁ oa).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (simulateQ impl₂ oa).run s' >>= fun z ↦ f z.1 z.2] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    calc _ = 𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= fun s' ↦
          (simulateQ impl₂ (k z.1)).run s' >>= fun w ↦ f w.1 w.2] :=
          evalDist_bind_congr_of_support _ _ _ fun z hz ↦ ih z.1 z.2 (hinv t s hs z hz)
      _ = _ := h t s hs fun u s' ↦ (simulateQ impl₂ (k u)).run s' >>= fun w ↦ f w.1 w.2

/-- If `fill` intertwines `impl₁` with `impl₂` step by step, it intertwines their runs of every
oracle computation. -/
theorem Intertwines.evalDist_simulateQ_run {fill : σ₁ → ProbComp σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ ProbComp)} {impl₂ : QueryImpl spec (StateT σ₂ ProbComp)}
    (h : Intertwines fill impl₁ impl₂) {α γ : Type} [MeasurableSpace γ]
    (oa : OracleComp spec α) (s : σ₁) (f : α → σ₂ → ProbComp γ) :
    𝒟[(simulateQ impl₁ oa).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (simulateQ impl₂ oa).run s' >>= fun z ↦ f z.1 z.2] :=
  (h.intertwinesOn fun _ ↦ True).evalDist_simulateQ_run (fun _ _ _ _ _ ↦ trivial) oa s trivial f

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
