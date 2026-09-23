/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Support
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Control.StateT

/-!
# Operational stateful oracle handlers

Stateful handlers compose through the universal oracle fold. Running, flattening, and changing
the base monad preserve the corresponding public equations. Operational support bounds adaptive
outputs without a probability assumption.
-/

public section

universe u v w x

open OracleSpec

namespace QueryImpl

/-- Push an outer oracle interpretation through the base monad of a
`StateT`-valued query implementation. -/
@[expose]
def mapStateTBase {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁))) :
    QueryImpl spec₀ (StateT σ m) := fun t =>
  StateT.mk fun s => simulateQ outer ((inner t).run s)

/-- Running a `StateT` handler and then interpreting its base oracle
computations is the same as first mapping the handler's base through the
outer interpreter. -/
theorem simulateQ_mapStateTBase_run {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run s) =
      (simulateQ (outer.mapStateTBase inner) oa).run s :=
  simulateQ_StateT_compose inner outer (outer.mapStateTBase inner) (fun _ _ => rfl) oa s

/-- Output-only corollary of `simulateQ_mapStateTBase_run`. -/
theorem simulateQ_mapStateTBase_run' {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run' s) =
      (simulateQ (outer.mapStateTBase inner) oa).run' s := by
  simp [simulateQ_mapStateTBase_run]

/-- Interpreting the base oracle of a stateful query implementation preserves every
state invariant already preserved by the inner implementation, provided the outer
interpreter preserves support. -/
theorem mapStateTBase_preserves_inv {ι₀ ι₁ ι₂ : Type u}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {σ : Type u}
    (outer : QueryImpl spec₁ (OracleComp spec₂))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (inv : σ → Prop)
    (houter : ∀ {α : Type u} (oa : OracleComp spec₁ α),
      support (simulateQ outer oa) = support oa)
    (hinner : ∀ t s, inv s →
      ∀ y ∈ support ((inner t).run s), inv y.2) :
    ∀ t s, inv s →
      ∀ y ∈ support ((outer.mapStateTBase inner t).run s), inv y.2 := by
  intro t s hs y hy
  rw [mapStateTBase, StateT.run_mk, houter] at hy
  exact hinner t s hs y hy

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of state monads for
two different contexts `σ₁` and `σ₂`, implement the combined set `spec₁ + spec₂` in terms
of a combined `σ₁ × σ₂` state. -/
@[expose]
def parallelStateT {ι₁ : Type u} {ι₂ : Type v}
    {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{v, w} ι₂}
    {m : Type w → Type x} [Functor m] {σ₁ σ₂ : Type w}
    (impl₁ : QueryImpl spec₁ (StateT σ₁ m))
    (impl₂ : QueryImpl spec₂ (StateT σ₂ m)) :
    QueryImpl (spec₁ + spec₂) (StateT (σ₁ × σ₂) m)
  | .inl t => StateT.mk fun | (s₁, s₂) => Prod.map id (·, s₂) <$> (impl₁ t).run s₁
  | .inr t => StateT.mk fun | (s₁, s₂) => Prod.map id (s₁, ·) <$> (impl₂ t).run s₂

/-- Reassociate a nested state transformer into one product state.

The outer state is the first component of the product; the inner/base state is
the second component. This is the state-transformer analogue of reassociating
handler stacks into an explicit joint state before applying projection lemmas. -/
@[expose]
def flattenStateT {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] {σ τ : Type u}
    (impl : QueryImpl spec (StateT σ (StateT τ m))) :
    QueryImpl spec (StateT (σ × τ) m) := fun t =>
  StateT.mk fun (s, q) =>
    (fun ((u, s'), q') => (u, (s', q'))) <$> ((impl t).run s |>.run q)

@[simp, grind =] theorem flattenStateT_liftTarget_apply_run {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ τ : Type u}
    (impl : QueryImpl spec (StateT τ m)) (t : spec.Domain) (s : σ) (q : τ) :
    ((impl.liftTarget (StateT σ (StateT τ m))).flattenStateT t).run (s, q) =
      (fun y : spec.Range t × τ => (y.1, (s, y.2))) <$> (impl t).run q := by
  simp [flattenStateT]

/-- Indexed version of `QueryImpl.parallelStateT`. Note that `m` cannot vary with `t`.
dtumad: The `Function.update` thing is nice but forces `DecidableEq`. -/
@[expose]
def piStateT {τ : Type} [DecidableEq τ] {ι : τ → Type v}
    {spec : (t : τ) → OracleSpec.{v, w} (ι t)}
    {m : Type w → Type x} [Monad m] {σ : τ → Type w}
    (impl : (t : τ) → QueryImpl (spec t) (StateT (σ t) m)) :
    QueryImpl (OracleSpec.sigma spec) (StateT ((t : τ) → σ t) m)
  | ⟨t, q⟩ => StateT.mk fun s => Prod.map id (Function.update s t) <$> (impl t q).run (s t)

/-- Lift a stateful query implementation to a `(state × Bool)`-stateful version that threads
the boolean (bad) flag unchanged. The output value and updated state come from the
underlying `impl`; the second `Bool` component is preserved verbatim across each query. -/
@[expose]
def withBadFlag {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {m : Type v → Type w} [Functor m] {σ : Type v}
    (impl : QueryImpl spec (StateT σ m)) :
    QueryImpl spec (StateT (σ × Bool) m) := fun t =>
  StateT.mk fun | (s, b) => Prod.map id (·, b) <$> (impl t).run s

/-- Lift a stateful query implementation to a `(state × Bool)`-stateful version that OR-updates
the boolean (bad) flag with a predicate `f` evaluated on the pre-state and produced output.
The flag is monotone: if it was already `true`, it stays `true`. -/
@[expose]
def withBadUpdate {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {m : Type v → Type w} [Functor m] {σ : Type v}
    (impl : QueryImpl spec (StateT σ m))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool) :
    QueryImpl spec (StateT (σ × Bool) m) := fun t =>
  StateT.mk fun | (s, b) => (fun (v, s') => (v, s', b || f t s v)) <$> (impl t).run s

/-- Run-shape of `withBadFlag`: the lifted implementation maps the underlying run by tagging
each `(value, state)` pair with the unchanged bad flag `b`. -/
@[simp, grind =] lemma withBadFlag_apply_run {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {m : Type v → Type w} [Functor m] {σ : Type v}
    (impl : QueryImpl spec (StateT σ m)) (t : spec.Domain) (s : σ) (b : Bool) :
    (impl.withBadFlag t).run (s, b) =
      (fun (vs : spec.Range t × σ) => (vs.1, vs.2, b)) <$> (impl t).run s := rfl

/-- Run-shape of `withBadUpdate`: the lifted implementation maps the underlying run by
appending the OR-updated bad flag `b || f t s vs.1`. -/
@[simp, grind =] lemma withBadUpdate_apply_run {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {m : Type v → Type w} [Functor m] {σ : Type v}
    (impl : QueryImpl spec (StateT σ m))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool)
    (t : spec.Domain) (s : σ) (b : Bool) :
    (impl.withBadUpdate f t).run (s, b) =
      (fun (vs : spec.Range t × σ) =>
        (vs.1, vs.2, b || f t s vs.1)) <$> (impl t).run s := rfl

end QueryImpl

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι} {m : Type u → Type v} [Monad m] {σ : Type u}

/-- Running a base-monad action lifted into `StateT σ m` threads the state `s` through
unchanged, pairing it with the produced value. -/
lemma liftM_run_StateT {α : Type u} (x : m α) (s : σ) :
    (liftM x : StateT σ m α).run s = x >>= fun a => pure (a, s) :=
  StateT.run_lift x s

variable [LawfulMonad m] (so : QueryImpl spec (StateT σ m))

/-- Simulating a query followed by a continuation, under a stateful handler, runs the handler
at that query and threads its output state into the simulation of the continuation.

This is the `StateT`-run form of `simulateQ_query_bind`: it is the step lemma that drives an
`OracleComp.inductionOn` over a computation simulated by a stateful oracle, which would
otherwise be re-derived per handler at the call site. -/
lemma run_simulateQ_query_bind {α : Type u} (t : spec.Domain)
    (oa : spec.Range t → OracleComp spec α) (s : σ) :
    (simulateQ so ((liftM (spec.query t) : OracleComp spec _) >>= oa)).run s =
      (so t).run s >>= fun us => (simulateQ so (oa us.1)).run us.2 := by
  simp [simulateQ_bind, simulateQ_query, StateT.run_bind, monad_norm,
    OracleQuery.cont_query, OracleQuery.input_query]

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma StateT_run_simulateQ_eq_map_run'_simulateQ {α} [Subsingleton σ]
    (oa : OracleComp spec α) (s s' : σ) :
    (simulateQ so oa).run s = (·, s') <$> (simulateQ so oa).run' s := by
  simp [show (fun x : α × σ => (x.1, s')) = id from
    funext fun x => Prod.ext rfl (Subsingleton.elim _ _)]

/-- If a `StateT` implementation passes every query through unchanged after discarding state
(`(so t).run' s = query t`), then simulating a computation and projecting out the final state
recovers the original computation. -/
lemma StateT_run'_simulateQ_eq_self {α} (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ t s, (so t).run' s = query t)
    (oa : OracleComp spec α) (s : σ) : (simulateQ so oa).run' s = oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [StateT.run'_eq] at ih
    simpa [ih] using congr_arg (· >>= oa) (h t s)

variable {τ : Type u}

/-- Running a computation under a flattened nested-state implementation is the
same as running the original nested computation and reassociating the final
states into a product. -/
theorem simulateQ_flattenStateT_run
    (impl : QueryImpl spec (StateT σ (StateT τ m)))
    {α : Type u} (oa : OracleComp spec α) (s : σ) (q : τ) :
    (simulateQ impl.flattenStateT oa).run (s, q) =
      (do
        let ((a, s'), q') ← (simulateQ impl oa).run s |>.run q
        pure (a, (s', q')) : m (α × (σ × τ))) := by
  induction oa using OracleComp.inductionOn generalizing s q <;>
    simp_all [QueryImpl.flattenStateT]

/-- Output-only corollary of `simulateQ_flattenStateT_run`. -/
theorem simulateQ_flattenStateT_run'
    (impl : QueryImpl spec (StateT σ (StateT τ m)))
    {α : Type u} (oa : OracleComp spec α) (s : σ) (q : τ) :
    (simulateQ impl.flattenStateT oa).run' (s, q) =
      (Prod.fst <$> (simulateQ impl oa).run s).run' q := by
  simp [simulateQ_flattenStateT_run]

/-- Running an adversary-side `StateT` handler under an outer stateful
interpreter produces the same distribution as the flattened product-state
handler, up to reassociating `((output, localState), outerState)` and
`(output, (localState, outerState))`. -/
theorem simulateQ_mapStateTBase_run_eq_map_flattenStateT
    {ι₀ ι₁ : Type _} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ τ : Type u}
    (outer : QueryImpl spec₁ (StateT τ m))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) (q : τ) :
    (simulateQ outer ((simulateQ inner oa).run s)).run q =
      (fun z : α × (σ × τ) => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (outer.mapStateTBase inner).flattenStateT oa).run (s, q) := by
  simp [QueryImpl.simulateQ_mapStateTBase_run, simulateQ_flattenStateT_run]

end OracleComp

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

section support_simulateQ_StateT

variable {α : Type w}
/-- Simulating an `OracleComp` through a stateful implementation in monad `m` can only shrink the
support: any output reachable after simulation was already reachable in the original computation
(where oracle queries may return any value). The statement needs no probability interpretation. -/
theorem support_simulateQ_run'_subset
    {n : Type w → Type _} [Monad n] [LawfulMonad n] [MonadAttach n] [ExactMonadAttach n]
    {σ : Type w}
    (impl : QueryImpl spec (StateT σ n))
    (oa : OracleComp spec α) (s : σ) :
    support ((simulateQ impl oa).run' s) ⊆ support oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
      MonadAttach.support_map,
      MonadAttach.support_bind, Set.mem_image, Set.mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨⟨a, s'⟩, ⟨⟨u, s''⟩, -, hsupp⟩, rfl⟩ := hx
    refine ⟨u, mem_support_query t u, ih u s'' ?_⟩
    rw [StateT.run'_eq, MonadAttach.support_map]
    exact Set.mem_image_of_mem _ hsupp

end support_simulateQ_StateT

end OracleComp

open OracleComp

/-- `run'`-level corollary of `simulateQ_bind_map_eq_of_body`: if the two bodies of a bind agree
under `simulateQ` up to a pure post-map `f`, then so do the `run'`s of the simulated binds from
any initial state. -/
lemma StateT.run'_simulateQ_bind_map_eq_of_body
    {ι : Type} {σ α β γ : Type} {spec : OracleSpec ι}
    {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl spec (StateT σ n))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β) (s : σ)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    (simulateQ impl (oa >>= body₁)).run' s =
      f <$> (simulateQ impl (oa >>= body₂)).run' s := by
  rw [← StateT.run'_map']
  exact congrArg (fun mx : StateT σ n β ↦ mx.run' s)
    (simulateQ_bind_map_eq_of_body impl oa body₁ body₂ f hBody)

/-- Properties of `Option`-valued outputs of an underlying `OracleComp` propagate to elements
in the support of the simulated, run, and `OptionT`-wrapped version. -/
lemma OptionT.aux_mem_support_simulateQ_run'
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∀ a, x = some a → P a)
    {x : α} (hx : x ∈ support (OptionT.mk ((simulateQ impl oa).run' s₀))) : P x := by
  rw [MonadAttach.mem_support, MonadAttach.OptionT.canReturn_iff] at hx
  exact h (some x) (support_simulateQ_run'_subset impl oa s₀ hx) x rfl
