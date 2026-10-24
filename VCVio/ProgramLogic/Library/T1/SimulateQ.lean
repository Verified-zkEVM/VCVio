/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Std.WP
public import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# Structural specifications for `simulateQ`

Core `@[spec]` rules that let `vcgen` walk through a simulated program `simulateQ impl oa`: the
simulation of `pure`, `>>=`, `<$>`, `if`, `dite` and of a query is reduced to the weakest
precondition of the simulated pieces, and a query becomes the handler call `impl t`, where the
handler's own specification takes over.

The rules hold for every target monad `m` with a core `WPMonad` interpretation, so they apply
under every reading of the simulation: `StateT σ (OracleComp spec')` and `WriterT` handlers under
the necessary reading (`open scoped OracleComp.Necessary`) or the lower reading
(`open scoped OracleComp.Lower`), stateless handlers into `OracleComp spec'` or `ProbComp`, and
any other `WPMonad`. No universe is pinned: the oracle specification, the target monad and the
handler state are arbitrary.

The query rules cover the three spellings of a query: the primitive `liftM (spec.query t)`, the
direct-style `HasQuery.query t`, and a general lifted `OracleQuery` (at low priority, since its
precondition carries the `.input` and `.cont` of the query). For a sum handler `impl₁ + impl₂`, a
query or a computation lifted from a summand dispatches to that summand.

`Spec.monadLift_StateT_univ` is the universe-general rule for a base-monad computation lifted
into `StateT`, the step `vcgen` takes inside the body of a stateful handler.
-/

public section

open OracleSpec OracleComp Std.WP

universe u u₁ u₂ v w z z'

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι} {m : Type w → Type v} [Monad m]
  {Pred : Type z} {EPred : Type z'} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
  {α β : Type w}

/-! ## Structural rules -/

/-- The simulation of `pure a` meets `post` when `post a` holds. -/
@[spec]
theorem Spec.simulateQ_pure (impl : QueryImpl spec m) (a : α) {post : α → Pred}
    {epost : EPred} :
    Triple (simulateQ impl (pure a : OracleComp spec α)) (post a) post epost :=
  Triple.pure a Lean.Order.PartialOrder.rel_refl

/-- The simulation of a bind is the bind of the simulations: its precondition is the weakest
precondition of the simulated head for the weakest precondition of the simulated continuation. -/
@[spec]
theorem Spec.simulateQ_bind (impl : QueryImpl spec m) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) {post : β → Pred} {epost : EPred} :
    Triple (simulateQ impl (oa >>= f))
      (wp (simulateQ impl oa)
        (fun a ↦ binderNameHint a f (wp (simulateQ impl (f a)) post epost)) epost)
      post epost := by
  rw [_root_.simulateQ_bind]
  exact Triple.bind _ _ _ ⟨Lean.Order.PartialOrder.rel_refl⟩
    fun _ ↦ ⟨Lean.Order.PartialOrder.rel_refl⟩

/-- The simulation of a map is the map of the simulation. -/
@[spec]
theorem Spec.simulateQ_map (impl : QueryImpl spec m) (f : α → β) (oa : OracleComp spec α)
    {post : β → Pred} {epost : EPred} :
    Triple (simulateQ impl (f <$> oa)) (wp (simulateQ impl oa) (fun a ↦ post (f a)) epost)
      post epost := by
  rw [_root_.simulateQ_map]
  exact Triple.map f _ ⟨Lean.Order.PartialOrder.rel_refl⟩

/-- The simulation of an `if` is the `if` of the simulations, which `vcgen` splits. -/
@[spec]
theorem Spec.simulateQ_ite (impl : QueryImpl spec m) (c : Prop) [Decidable c]
    (oa ob : OracleComp spec α) {post : α → Pred} {epost : EPred} :
    Triple (simulateQ impl (if c then oa else ob))
      (wp (if c then simulateQ impl oa else simulateQ impl ob) post epost) post epost :=
  ⟨by rw [_root_.simulateQ_ite]⟩

/-- The simulation of a dependent `if` is the dependent `if` of the simulations. -/
@[spec]
theorem Spec.simulateQ_dite (impl : QueryImpl spec m) (c : Prop) [Decidable c]
    (oa : c → OracleComp spec α) (ob : ¬c → OracleComp spec α) {post : α → Pred}
    {epost : EPred} :
    Triple (simulateQ impl (if h : c then oa h else ob h))
      (wp (if h : c then simulateQ impl (oa h) else simulateQ impl (ob h)) post epost)
      post epost :=
  ⟨by rw [_root_.simulateQ_dite]⟩

/-! ## Queries -/

/-- A simulated primitive query runs the handler: its precondition is the weakest precondition
of `impl t`, where the handler's specification takes over. -/
@[spec high]
theorem Spec.simulateQ_spec_query (impl : QueryImpl spec m) (t : spec.Domain)
    {post : spec.Range t → Pred} {epost : EPred} :
    Triple (simulateQ impl (liftM (spec.query t) : OracleComp spec (spec.Range t)))
      (wp (impl t) post epost) post epost :=
  ⟨by rw [_root_.simulateQ_spec_query]⟩

/-- A simulated direct-style query `HasQuery.query t` runs the handler. -/
@[spec high]
theorem Spec.simulateQ_HasQuery_query (impl : QueryImpl spec m) (t : spec.Domain)
    {post : spec.Range t → Pred} {epost : EPred} :
    Triple (simulateQ impl (HasQuery.query (spec := spec) (m := OracleComp spec) t))
      (wp (impl t) post epost) post epost :=
  ⟨by rw [_root_.simulateQ_HasQuery_query]⟩

/-- A simulated lifted `OracleQuery` runs the handler at its input and continues with its
continuation. Lower priority than the primitive-query rules, which avoid `.input` and `.cont`. -/
@[spec low]
theorem Spec.simulateQ_query (impl : QueryImpl spec m) (q : OracleQuery spec α)
    {post : α → Pred} {epost : EPred} :
    Triple (simulateQ impl (liftM q : OracleComp spec α))
      (wp (impl q.input) (fun u ↦ post (q.cont u)) epost) post epost := by
  rw [_root_.simulateQ_query]
  exact Triple.map _ _ ⟨Lean.Order.PartialOrder.rel_refl⟩

/-! ## Sum handlers -/

section add

variable {ι₁ : Type u₁} {ι₂ : Type u₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)

/-- A query lifted from the left summand runs the left handler. -/
@[spec high]
theorem Spec.simulateQ_add_liftM_query_left (t : spec₁.Domain)
    {post : spec₁.Range t → Pred} {epost : EPred} :
    Triple (simulateQ (impl₁ + impl₂)
        (liftM (spec₁.query t) : OracleComp (spec₁ + spec₂) (spec₁.Range t)))
      (wp (impl₁ t) post epost) post epost :=
  ⟨by rw [QueryImpl.simulateQ_add_liftM_query_left]⟩

/-- A query lifted from the right summand runs the right handler. -/
@[spec high]
theorem Spec.simulateQ_add_liftM_query_right (t : spec₂.Domain)
    {post : spec₂.Range t → Pred} {epost : EPred} :
    Triple (simulateQ (impl₁ + impl₂)
        (liftM (spec₂.query t) : OracleComp (spec₁ + spec₂) (spec₂.Range t)))
      (wp (impl₂ t) post epost) post epost :=
  ⟨by rw [QueryImpl.simulateQ_add_liftM_query_right]⟩

/-- A computation lifted from the left summand is simulated by the left handler. -/
@[spec]
theorem Spec.simulateQ_add_liftM_left (oa : OracleComp spec₁ α) {post : α → Pred}
    {epost : EPred} :
    Triple (simulateQ (impl₁ + impl₂) (liftM oa : OracleComp (spec₁ + spec₂) α))
      (wp (simulateQ impl₁ oa) post epost) post epost :=
  ⟨by rw [QueryImpl.simulateQ_add_liftM_left]⟩

/-- A computation lifted from the right summand is simulated by the right handler. -/
@[spec]
theorem Spec.simulateQ_add_liftM_right (oa : OracleComp spec₂ α) {post : α → Pred}
    {epost : EPred} :
    Triple (simulateQ (impl₁ + impl₂) (liftM oa : OracleComp (spec₁ + spec₂) α))
      (wp (simulateQ impl₂ oa) post epost) post epost :=
  ⟨by rw [QueryImpl.simulateQ_add_liftM_right]⟩

end add

/-! ## Lifts into `StateT` -/

/-- A computation of the base monad lifted into `StateT` runs it and keeps the state. Core's
`Std.WP.Spec.monadLift_StateT` asks the assertions to live in the universe of the values, which
excludes `Prop`-valued readings of handlers on `Type w`; this rule has no such constraint, so
`vcgen` steps through the base-monad lifts of handler bodies at every universe. -/
@[spec]
theorem Spec.monadLift_StateT_univ {σ : Type w} (x : m α) {post : α → σ → Pred} {epost : EPred} :
    Triple (MonadLift.monadLift x : StateT σ m α) (fun s ↦ wp x (fun a ↦ post a s) epost) post
      epost := by
  refine ⟨fun s ↦ ?_⟩
  simp only [wp, MonadLift.monadLift]
  refine Lean.Order.PartialOrder.rel_trans ?_ (WPMonad.bind_le_wp_bind _ _ _ _)
  refine WP.wp_consequence _ _ _ _ fun a ↦ ?_
  simpa using WPMonad.pure_le_wp_pure (m := m) (a, s) (fun p ↦ post p.1 p.2) epost

end OracleComp.ProgramLogic
