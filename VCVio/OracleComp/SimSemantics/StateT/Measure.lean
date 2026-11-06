/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Chung Thai Nguyen, Yuxi Zheng
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Joint measure laws for stateful oracle interpretation

Local equality in distribution of the joint response and retained state preserves the
distribution of the complete result and state of every adaptive oracle computation, possibly
across two base monads. This interface retains service state in its premise because later adaptive
calls may reveal changes hidden from the immediate response. Local discrete domination of the joint
laws is preserved by adaptive execution (`OracleComp.evalDist_simulateQ_run_le_of_discrete`), and
local laws agreeing on transitions into a monotone good state set give run laws agreeing on good
final states (`OracleComp.evalDist_simulateQ_run_restrict_eq_of_good`). No local law is assumed to
be a probability measure, so handlers may discard mass.

Running a computation through a stateful handler into a second interface and then through a
stateful handler of that interface is equal in distribution to running it through one handler on
the pair of states, if this holds query by query
(`OracleComp.simulateQ_run_simulateQ_run_evalDistEq`).

A probabilistic state map that intertwines two handlers step by step, `QueryImpl.Intertwines`,
intertwines their runs of every oracle computation
(`QueryImpl.Intertwines.evalDist_simulateQ_run`). The step condition may be restricted to the
states satisfying an invariant that the first handler preserves (`QueryImpl.IntertwinesOn` and
`QueryImpl.IntertwinesOn.evalDist_simulateQ_run`), so a state map that is only meaningful on
reachable states, such as one drawing a value for each of finitely many cached points, still
intertwines whole runs. A joint law of answer and mapped state at each step suffices
(`QueryImpl.IntertwinesOn.of_evalDistEq`, `OracleComp.simulateQ_intertwine_of_invariant`).

Stateful simulation from a sampled initial state satisfies an event with probability one
whenever every possible output of the original computation does: simulation only
shrinks operational support, so no property of the handler is needed.
-/

public section

universe u v w

namespace OracleComp

open OracleSpec MeasureTheory

/-- Implementations whose local steps, from every state, are equal in distribution give equal
distributions of the complete result and retained state, possibly over two different base monads.
Neither the service state nor the response needs a measurable structure. -/
theorem evalDistEq_simulateQ_run
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {m' : Type → Type w} [Monad m'] [LawfulMonad m']
    [EvalDistSemantics m'] [LawfulEvalDistSemantics m']
    {ι : Type u} {S α : Type} {spec : OracleSpec.{u, 0} ι}
    (left : QueryImpl spec (StateT S m)) (right : QueryImpl spec (StateT S m'))
    (h : ∀ operation state, (left operation).run state =ᵈ (right operation).run state)
    (program : OracleComp spec α) (state : S) :
    (simulateQ left program).run state =ᵈ (simulateQ right program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact evalDistEq_iff_evalDist_eq.mpr (by simp)
  | query_bind operation next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind]
    exact (h operation state).bind fun output ↦ ih output.1 output.2

/-- Implementations whose local steps, from every state, are equal in distribution give equal
measures of the complete result and retained state, possibly over two different base monads, in
any measurable space of final outputs. -/
theorem evalDist_simulateQ_run_congr
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {m' : Type → Type w} [Monad m'] [LawfulMonad m']
    [EvalDistSemantics m'] [LawfulEvalDistSemantics m']
    {ι : Type u} {S α : Type} {spec : OracleSpec.{u, 0} ι} [MeasurableSpace (α × S)]
    (left : QueryImpl spec (StateT S m)) (right : QueryImpl spec (StateT S m'))
    (h : ∀ operation state, (left operation).run state =ᵈ (right operation).run state)
    (program : OracleComp spec α) (state : S) :
    𝒟[(simulateQ left program).run state] = 𝒟[(simulateQ right program).run state] :=
  (evalDistEq_simulateQ_run left right h program state).evalDist_eq

/-- Local discrete domination of joint answer/state measures is preserved by adaptive
execution, in any measurable space of final outputs. -/
theorem evalDist_simulateQ_run_le_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ β : Type} [MeasurableSpace (β × σ)]
    (left right : QueryImpl spec (StateT σ m))
    (hstep : ∀ q s, (letI : MeasurableSpace (spec.Range q × σ) := ⊤;
      𝒟[(left q).run s] ≤ 𝒟[(right q).run s]))
    (oa : OracleComp spec β) (s : σ) :
    𝒟[(simulateQ left oa).run s] ≤ 𝒟[(simulateQ right oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => simp
  | query_bind q next ih =>
    let : MeasurableSpace (spec.Range q × σ) := ⊤
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, evalDist_bind_of_discrete]
    refine Measure.le_iff.mpr fun T hT => ?_
    rw [Measure.bind_apply hT Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hT Measurable.of_discrete.aemeasurable]
    exact (lintegral_mono fun z => Measure.le_iff'.mp (ih z.1 z.2) T).trans
      (lintegral_mono' (hstep q s) le_rfl)

/-- Local joint measures agreeing on transitions into a good state give run measures
agreeing on good final states. Monotonicity is assumed only of the right handler. Agreement is
required at every state, so from a bad state the left handler also puts no mass on good states;
its behaviour among bad states is unconstrained. Either handler may discard mass. -/
theorem evalDist_simulateQ_run_restrict_eq_of_good
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [MonadAttach m] [LawfulMonadAttach m]
    {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ β : Type}
    (left right : QueryImpl spec (StateT σ m)) (good : σ → Prop)
    (hstep : ∀ q s, (letI : MeasurableSpace (spec.Range q × σ) := ⊤;
      (𝒟[(left q).run s]).restrict {z | good z.2} =
        (𝒟[(right q).run s]).restrict {z | good z.2}))
    (hmono : ∀ q s, ¬good s → ∀ z ∈ support ((right q).run s), ¬good z.2)
    (oa : OracleComp spec β) (s : σ) :
    (letI : MeasurableSpace (β × σ) := ⊤;
      (𝒟[(simulateQ left oa).run s]).restrict {z | good z.2} =
        (𝒟[(simulateQ right oa).run s]).restrict {z | good z.2}) := by
  let : MeasurableSpace (β × σ) := ⊤
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => rfl
  | query_bind q next ih =>
    let : MeasurableSpace (spec.Range q × σ) := ⊤
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, evalDist_bind_of_discrete]
    ext T hT
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT,
      Measure.bind_apply (hT.inter MeasurableSet.of_discrete)
        Measurable.of_discrete.aemeasurable,
      Measure.bind_apply (hT.inter MeasurableSet.of_discrete)
        Measurable.of_discrete.aemeasurable]
    have hih : ∀ z : spec.Range q × σ,
        𝒟[(simulateQ left (next z.1)).run z.2] (T ∩ {z | good z.2}) =
          𝒟[(simulateQ right (next z.1)).run z.2] (T ∩ {z | good z.2}) := fun z => by
      rw [← Measure.restrict_apply hT, ← Measure.restrict_apply hT, ih z.1 z.2]
    simp only [hih]
    have hbad : (Function.support fun z : spec.Range q × σ =>
        𝒟[(simulateQ right (next z.1)).run z.2] (T ∩ {z | good z.2})) ⊆
          {z | good z.2} := by
      intro z hz
      by_contra hg
      apply hz
      refine measure_mono_null Set.inter_subset_right
        (evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete ?_)
      intro y hy hgy
      exact simulateQ_run_preservesInv right (fun s => ¬good s) hmono (next z.1) z.2 hg y hy hgy
    rw [← setLIntegral_eq_of_support_subset hbad, hstep q s]
    exact setLIntegral_eq_of_support_subset hbad

/-- Running a computation through a stateful handler into a second interface, then through a
stateful handler of that interface, is equal in distribution to running it through one handler on
the pair of states, if this holds for every query. -/
theorem simulateQ_run_simulateQ_run_evalDistEq {ι₀ ι₁ σ τ α : Type}
    {spec₀ : OracleSpec.{0, 0} ι₀} {spec₁ : OracleSpec.{0, 0} ι₁}
    (outer : QueryImpl spec₁ (StateT τ ProbComp))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (impl : QueryImpl spec₀ (StateT (τ × σ) ProbComp))
    (h : ∀ t s q, (simulateQ outer ((inner t).run s)).run q =ᵈ
      (fun z => ((z.1, z.2.2), z.2.1)) <$> (impl t).run (q, s))
    (oa : OracleComp spec₀ α) (s : σ) (q : τ) :
    (simulateQ outer ((simulateQ inner oa).run s)).run q =ᵈ
      (fun z => ((z.1, z.2.2), z.2.1)) <$> (simulateQ impl oa).run (q, s) := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    refine ((h t s q).bind_left _).trans ?_
    simp only [bind_map_left]
    exact EvalDistEq.bind_right _ fun z => ih z.1 z.2.2 z.2.1

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

open OracleComp MeasureTheory

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ₁ σ₂ : Type} {m : Type → Type v} [Monad m]
  [EvalDistSemantics m]

/-- A probabilistic state map `fill` intertwines `impl₁` with `impl₂`: from every state, a step
of `impl₁` followed by `fill` of its post-state has, before any continuation, the distribution of
`fill` followed by the step of `impl₂`. With `fill = pure` this is the equality of step measures
of `OracleComp.evalDist_simulateQ_run_congr`. -/
@[expose] def Intertwines (fill : σ₁ → m σ₂)
    (impl₁ : QueryImpl spec (StateT σ₁ m)) (impl₂ : QueryImpl spec (StateT σ₂ m)) :
    Prop :=
  ∀ t s {γ : Type} [MeasurableSpace γ] (f : spec.Range t → σ₂ → m γ),
    𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (impl₂ t).run s' >>= fun z ↦ f z.1 z.2]

/-- A probabilistic state map `fill` intertwines `impl₁` with `impl₂` on the states satisfying
`inv`: from every state satisfying `inv`, a step of `impl₁` followed by `fill` of its post-state
has, before any continuation, the distribution of `fill` followed by the step of `impl₂`. With the
trivial invariant this is `QueryImpl.Intertwines`. -/
@[expose] def IntertwinesOn (inv : σ₁ → Prop) (fill : σ₁ → m σ₂)
    (impl₁ : QueryImpl spec (StateT σ₁ m)) (impl₂ : QueryImpl spec (StateT σ₂ m)) :
    Prop :=
  ∀ t s, inv s → ∀ {γ : Type} [MeasurableSpace γ] (f : spec.Range t → σ₂ → m γ),
    𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (impl₂ t).run s' >>= fun z ↦ f z.1 z.2]

/-- A state map that intertwines two handlers from every state intertwines them on the states
satisfying any invariant. -/
theorem Intertwines.intertwinesOn {fill : σ₁ → m σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ m)} {impl₂ : QueryImpl spec (StateT σ₂ m)}
    (h : Intertwines fill impl₁ impl₂) (inv : σ₁ → Prop) : IntertwinesOn inv fill impl₁ impl₂ :=
  fun t s _ ↦ h t s

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- A joint law of answer and mapped post-state at each step, on the states satisfying `inv`, gives
the intertwining of `impl₁` with `impl₂` before any continuation. -/
theorem IntertwinesOn.of_evalDistEq {inv : σ₁ → Prop} {fill : σ₁ → m σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ m)} {impl₂ : QueryImpl spec (StateT σ₂ m)}
    (step : ∀ t s, inv s →
      (impl₁ t).run s >>= (fun z ↦ fill z.2 >>= fun s' ↦ pure (z.1, s')) =ᵈ
        fill s >>= fun s' ↦ (impl₂ t).run s') :
    IntertwinesOn inv fill impl₁ impl₂ := by
  intro t s hs γ _ f
  simpa only [bind_assoc, pure_bind] using
    ((step t s hs).bind_left fun w ↦ f w.1 w.2).evalDist_eq

variable [MonadAttach m] [WeaklyLawfulMonadAttach m]

/-- If `fill` intertwines `impl₁` with `impl₂` on the states satisfying an invariant that `impl₁`
preserves, it intertwines their runs of every oracle computation from every such state. -/
theorem IntertwinesOn.evalDist_simulateQ_run {inv : σ₁ → Prop} {fill : σ₁ → m σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ m)} {impl₂ : QueryImpl spec (StateT σ₂ m)}
    (h : IntertwinesOn inv fill impl₁ impl₂) (hinv : PreservesInv impl₁ inv) {α γ : Type}
    [MeasurableSpace γ] (oa : OracleComp spec α) (s : σ₁) (hs : inv s)
    (f : α → σ₂ → m γ) :
    𝒟[(simulateQ impl₁ oa).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (simulateQ impl₂ oa).run s' >>= fun z ↦ f z.1 z.2] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t k ih =>
    let : MeasurableSpace (spec.Range t × σ₁) := ⊤
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    calc _ = 𝒟[(impl₁ t).run s >>= fun z ↦ fill z.2 >>= fun s' ↦
          (simulateQ impl₂ (k z.1)).run s' >>= fun w ↦ f w.1 w.2] :=
          evalDist_bind_congr_ae _ _ _ Measurable.of_discrete Measurable.of_discrete
            (evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
              fun z hz ↦ ih z.1 z.2 (hinv t s hs z hz))
      _ = _ := h t s hs fun u s' ↦ (simulateQ impl₂ (k u)).run s' >>= fun w ↦ f w.1 w.2

/-- If `fill` intertwines `impl₁` with `impl₂` step by step, it intertwines their runs of every
oracle computation. -/
theorem Intertwines.evalDist_simulateQ_run {fill : σ₁ → m σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ m)} {impl₂ : QueryImpl spec (StateT σ₂ m)}
    (h : Intertwines fill impl₁ impl₂) {α γ : Type} [MeasurableSpace γ]
    (oa : OracleComp spec α) (s : σ₁) (f : α → σ₂ → m γ) :
    𝒟[(simulateQ impl₁ oa).run s >>= fun z ↦ fill z.2 >>= f z.1] =
      𝒟[fill s >>= fun s' ↦ (simulateQ impl₂ oa).run s' >>= fun z ↦ f z.1 z.2] :=
  (h.intertwinesOn fun _ ↦ True).evalDist_simulateQ_run (fun _ _ _ _ _ ↦ trivial) oa s trivial f

end QueryImpl

namespace OracleComp

/-- A completion kernel intertwines two stateful handlers: if running a `source` step and then
`kernel` has the discrete joint law of running `kernel` and then a `target` step, at every state
of an invariant closed under supported `source` transitions, then the same law holds for whole
simulated runs. -/
theorem simulateQ_intertwine_of_invariant
    {ι : Type u} {S T A : Type} {spec : OracleSpec.{u, 0} ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (source : QueryImpl spec (StateT S m))
    (target : QueryImpl spec (StateT T m))
    (kernel : S → m T)
    (invariant : S → Prop)
    (closed : ∀ q s, invariant s → ∀ z ∈ support ((source q).run s), invariant z.2)
    (step : ∀ (q : spec.Domain) (s : S), invariant s →
      (source q).run s >>= (fun z => kernel z.2 >>= fun t => pure (z.1, t)) =ᵈ
        kernel s >>= fun t => (target q).run t)
    (oa : OracleComp spec A) (s : S) (hs : invariant s) :
    (letI : MeasurableSpace (A × T) := ⊤;
      𝒟[(simulateQ source oa).run s >>= fun z => kernel z.2 >>= fun t => pure (z.1, t)] =
        𝒟[kernel s >>= fun t => (simulateQ target oa).run t]) := by
  let : MeasurableSpace (A × T) := ⊤
  simpa only [Prod.mk.eta, bind_pure] using
    (QueryImpl.IntertwinesOn.of_evalDistEq step).evalDist_simulateQ_run closed oa s hs
      fun a t => pure (a, t)

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
