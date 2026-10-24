/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.Bridges
public import VCVio.ProgramLogic.Library.T1.SimulateQ

/-!
# Whole-run triples for simulated programs

Core `Std.WP` triples for `simulateQ impl oa` with an arbitrary program `oa`, the form `vcgen`
needs for an opaque sub-program such as an adversary. Per-query facts about the handler lift to
the whole simulation without an induction on the program.

* `triple_simulateQ_inv`: an assertion preserved by every handler call is preserved by every
  simulation, in every `WPMonad` reading of the handler's monad.
* `triple_simulateQ_frame` and `triple_simulateQ_frame_of_inv`: the monotone frame, under the
  necessary reading (`open scoped OracleComp.Necessary`). If every call relates its initial and
  final states by a reflexive, transitive `R`, then a postcondition holding at every
  `R`-successor of the initial state holds after the run. The precondition
  `fun s ↦ ∀ a s', R s s' → post a s'` is the weakest precondition of an opaque run.
* `QueryImpl.MonotoneState impl R` records such an `R` for a handler; `R` is an output of
  instance search. With an instance in scope the frame is the `@[spec low]` rule
  `Spec.simulateQ_monotoneState`, so `vcgen` steps over opaque simulated programs unaided, while
  the structural rules of `VCVio.ProgramLogic.Library.T1.SimulateQ` take precedence on
  programs with visible structure. Sums of handlers inherit the instance.
* `triple_simulateQ_writerT_frame`, `triple_simulateQ_writerT_frame_append`: the frame for a
  writer handler whose written logs satisfy a predicate closed under the log operation.
* `triple_simulateQ_of_proj`: a triple for `impl₂` transfers to `impl₁` along a state projection
  that forward-simulates `impl₁` by `impl₂`, as for a handler carrying ghost state.

The hypotheses of the frames are per-query support facts, so these are not `@[spec]` rules; pass
them to `vcgen` explicitly, as `vcgen [triple_simulateQ_frame impl R hrefl htrans hstep oa]`.
State preconditions are written as `fun s ↦ …`: an eta-reduced precondition makes core `vcgen`
fail.
-/

public section

open OracleSpec OracleComp Std.WP

universe u u₁ u₂ u' u₂' v v' v₂' w z z'

/-! ## Invariants in every reading -/

namespace OracleComp.ProgramLogic

section generic

variable {ι : Type u} {spec : OracleSpec ι} {n : Type w → Type v} [Monad n]
  {Pred : Type z} {EPred : Type z'} [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]

/-- An assertion that every handler call preserves is preserved by the simulation of every
program, in every `WPMonad` reading of the handler's monad. -/
theorem triple_simulateQ_inv {impl : QueryImpl spec n} {I : Pred} {epost : EPred}
    (h : ∀ t, Triple (impl t) I (fun _ ↦ I) epost) {α : Type w} (oa : OracleComp spec α) :
    Triple (simulateQ impl oa) I (fun _ ↦ I) epost := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact Triple.pure a Lean.Order.PartialOrder.rel_refl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact Triple.bind _ _ _ (h t) ih

end generic

end OracleComp.ProgramLogic

/-! ## Monotone handlers -/

/-- `impl.MonotoneState R`: every call of the stateful handler `impl` relates its initial state
to each reachable final state by the reflexive, transitive relation `R`. The relation is an
output of instance search, so the frame `Spec.simulateQ_monotoneState` fires without naming it.
A preorder on the state (`MonotoneState.of_le`) and a preserved invariant `Inv`, as the relation
`fun s s' ↦ Inv s → Inv s'` (`MonotoneState.of_inv`), are the common instances. -/
class QueryImpl.MonotoneState {ι : Type u} {spec : OracleSpec ι} {σ : Type w}
    {m : Type w → Type v} [Monad m] [MonadAttach m] (impl : QueryImpl spec (StateT σ m))
    (R : outParam (σ → σ → Prop)) : Prop where
  /-- The relation is reflexive. -/
  refl : ∀ s, R s s
  /-- The relation is transitive. -/
  trans : ∀ s₁ s₂ s₃, R s₁ s₂ → R s₂ s₃ → R s₁ s₃
  /-- Every handler call relates its initial state to each reachable final state. -/
  step : ∀ t s, ∀ z ∈ support ((impl t).run s), R s z.2

namespace QueryImpl.MonotoneState

variable {ι : Type u} {spec : OracleSpec ι} {σ α : Type w} {m : Type w → Type v} [Monad m]
  [MonadAttach m] {R : σ → σ → Prop}

/-- A sum of handlers that are monotone for the same relation is monotone for it. -/
instance add {ι₁ : Type u₁} {ι₂ : Type u₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl₁ : QueryImpl spec₁ (StateT σ m)) (impl₂ : QueryImpl spec₂ (StateT σ m))
    [h₁ : impl₁.MonotoneState R] [h₂ : impl₂.MonotoneState R] :
    (impl₁ + impl₂).MonotoneState R where
  refl := h₁.refl
  trans := h₁.trans
  step
    | .inl t => h₁.step t
    | .inr t => h₂.step t

/-- A handler whose calls can only increase the state is monotone for the order. -/
theorem of_le [Preorder σ] {impl : QueryImpl spec (StateT σ m)}
    (hstep : ∀ t s, ∀ z ∈ support ((impl t).run s), s ≤ z.2) : impl.MonotoneState (· ≤ ·) where
  refl := le_refl
  trans _ _ _ := le_trans
  step := hstep

/-- A handler preserving a state invariant `Inv` is monotone for `fun s s' ↦ Inv s → Inv s'`, so
the frame passes `Inv` from the initial state to the final one. -/
theorem of_inv {impl : QueryImpl spec (StateT σ m)} {Inv : σ → Prop}
    (hstep : ∀ t s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2) :
    impl.MonotoneState fun s s' ↦ Inv s → Inv s' where
  refl _ := id
  trans _ _ _ h₁ h₂ := h₂ ∘ h₁
  step t s z hz hs := hstep t s hs z hz

/-- The run of every program simulated by a monotone handler relates the initial state to each
reachable final state. -/
theorem rel_of_mem_support [LawfulMonad m] [ExactMonadAttach m]
    {impl : QueryImpl spec (StateT σ m)} [h : impl.MonotoneState R]
    {oa : OracleComp spec α} {s : σ} {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run s)) : R s z.2 :=
  rel_of_mem_support_simulateQ_run R h.refl h.trans h.step hz

open scoped OracleComp.Necessary in
/-- A handler is monotone when a necessary triple from each state `s₀` establishes `R s₀` on the
final state of every call. -/
theorem of_triple {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} (hrefl : ∀ s, R s s)
    (htrans : ∀ s₁ s₂ s₃, R s₁ s₂ → R s₂ s₃ → R s₁ s₃)
    (h : ∀ t s₀, ⦃ fun s ↦ s = s₀ ⦄ impl t ⦃ fun _ s' ↦ R s₀ s' ⦄) : impl.MonotoneState R where
  refl := hrefl
  trans := htrans
  step t s z hz :=
    (ProgramLogic.triple_stateT_iff_forall_mem_support _ _ _ _).1 (h t s) s rfl z.1 z.2 hz

end QueryImpl.MonotoneState

/-! ## Frames under the necessary reading -/

namespace OracleComp.ProgramLogic

open scoped OracleComp.Necessary

variable {ι : Type u} {spec : OracleSpec ι} {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
  {σ α : Type w}

section frame

variable (impl : QueryImpl spec (StateT σ (OracleComp spec')))

/-- Invariant-gated monotone frame: if every call from a state satisfying `Inv` keeps `Inv` and
relates the states by a reflexive, transitive `R`, then a postcondition holding at every
`R`-successor satisfying `Inv` holds after the run of any program. -/
theorem triple_simulateQ_frame_of_inv {Inv : σ → Prop} (R : σ → σ → Prop) (hrefl : ∀ s, R s s)
    (htrans : ∀ s₁ s₂ s₃, R s₁ s₂ → R s₂ s₃ → R s₁ s₃)
    (hstep : ∀ t s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2 ∧ R s z.2)
    (oa : OracleComp spec α) {post : α → σ → Prop} {epost : EStack⟨⟩} :
    ⦃ fun s ↦ Inv s ∧ ∀ a s', Inv s' → R s s' → post a s' ⦄ simulateQ impl oa ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ ⟨hs, h⟩ a s' hz ↦
    let ⟨hs', hr⟩ := inv_rel_of_mem_support_simulateQ_run R hrefl htrans hstep hs hz
    h a s' hs' hr

/-- Monotone frame: if every call relates its initial and final states by a reflexive,
transitive `R`, then a postcondition holding at every `R`-successor of the initial state holds
after the run of any program. -/
theorem triple_simulateQ_frame (R : σ → σ → Prop) (hrefl : ∀ s, R s s)
    (htrans : ∀ s₁ s₂ s₃, R s₁ s₂ → R s₂ s₃ → R s₁ s₃)
    (hstep : ∀ t s, ∀ z ∈ support ((impl t).run s), R s z.2)
    (oa : OracleComp spec α) {post : α → σ → Prop} {epost : EStack⟨⟩} :
    ⦃ fun s ↦ ∀ a s', R s s' → post a s' ⦄ simulateQ impl oa ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h a s' hz ↦
    h a s' (rel_of_mem_support_simulateQ_run R hrefl htrans hstep hz)

/-- The monotone frame of a `QueryImpl.MonotoneState` handler, as a low-priority rule: `vcgen`
uses it for a simulated program without visible structure. -/
@[spec low]
theorem Spec.simulateQ_monotoneState {R : σ → σ → Prop} [h : impl.MonotoneState R]
    (oa : OracleComp spec α) {post : α → σ → Prop} {epost : EStack⟨⟩} :
    ⦃ fun s ↦ ∀ a s', R s s' → post a s' ⦄ simulateQ impl oa ⦃ post; epost ⦄ :=
  triple_simulateQ_frame impl R h.refl h.trans h.step oa

end frame

section writerT

variable {ω : Type w}

open scoped WriterT.MonoidWP in
/-- Frame of a monoid-log handler: if the log written by every call satisfies `P`, which holds
at `1` and is closed under multiplication, then a postcondition holding after every extension of
the incoming log by a `P`-log holds after the run of any program. -/
theorem triple_simulateQ_writerT_frame [Monoid ω]
    (impl : QueryImpl spec (WriterT ω (OracleComp spec'))) (P : ω → Prop) (h₁ : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hstep : ∀ t, ∀ z ∈ support (impl t).run, P z.2)
    (oa : OracleComp spec α) {post : α → ω → Prop} {epost : EStack⟨⟩} :
    ⦃ fun w ↦ ∀ a w', P w' → post a (w * w') ⦄ simulateQ impl oa ⦃ post; epost ⦄ :=
  (triple_writerT_iff_forall_mem_support _ _ _ _).2 fun _ h a w' hz ↦
    h a w' (prop_of_mem_support_simulateQ_writerT_run h₁ hmul hstep hz)

open scoped WriterT.AppendWP in
/-- Frame of an append-log handler: if the log written by every call satisfies `P`, which holds
at `∅` and is closed under `++`, then a postcondition holding after every extension of the
incoming log by a `P`-log holds after the run of any program. -/
theorem triple_simulateQ_writerT_frame_append [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (impl : QueryImpl spec (WriterT ω (OracleComp spec'))) (P : ω → Prop) (h₀ : P ∅)
    (happend : ∀ a b, P a → P b → P (a ++ b)) (hstep : ∀ t, ∀ z ∈ support (impl t).run, P z.2)
    (oa : OracleComp spec α) {post : α → ω → Prop} {epost : EStack⟨⟩} :
    ⦃ fun w ↦ ∀ a w', P w' → post a (w ++ w') ⦄ simulateQ impl oa ⦃ post; epost ⦄ :=
  (triple_writerT_iff_forall_mem_support_append _ _ _ _).2 fun _ h a w' hz ↦
    h a w' (prop_of_mem_support_simulateQ_writerT_run_append h₀ happend hstep hz)

end writerT

/-! ## Ghost state -/

/-- A triple for `impl₂` transfers to `impl₁` along a state projection `proj` when every call of
`impl₁` is matched by a call of `impl₂` from the projected state: the pre- and postconditions
are read through `proj`. -/
theorem triple_simulateQ_of_proj {ι₂' : Type u₂'} {spec₂' : OracleSpec.{u₂', v₂'} ι₂'}
    {σ₁ σ₂ : Type w} {impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec'))}
    {impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂'))} (proj : σ₁ → σ₂)
    (hstep : ∀ t s, ∀ z ∈ support ((impl₁ t).run s),
      (z.1, proj z.2) ∈ support ((impl₂ t).run (proj s)))
    {oa : OracleComp spec α} {P : σ₂ → Prop} {Q : α → σ₂ → Prop}
    (h : ⦃ fun s ↦ P s ⦄ simulateQ impl₂ oa ⦃ Q ⦄) :
    ⦃ fun s ↦ P (proj s) ⦄ simulateQ impl₁ oa ⦃ fun a s ↦ Q a (proj s) ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s hs a s' hz ↦
    (triple_stateT_iff_forall_mem_support _ _ _ _).1 h (proj s) hs a (proj s')
      (mem_support_simulateQ_run_of_proj proj hstep hz)

end OracleComp.ProgramLogic
