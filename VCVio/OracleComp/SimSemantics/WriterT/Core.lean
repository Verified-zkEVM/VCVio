/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Control.WriterT

/-!
# Simulation through `WriterT` Handlers

Combinators and output-preservation lemmas for writer-instrumented query implementations.
The combinators here mirror the StateT/ReaderT versions in
`SimSemantics/StateT/Basic.lean` and `SimSemantics/ReaderT/Basic.lean`.
-/

public section

open OracleSpec Function Prod

universe u v w x

open scoped OracleSpec.PrimitiveQuery

namespace QueryImpl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of writer monads for
two different log monoids `ω₁` and `ω₂`, implement the combined set `spec₁ + spec₂` in terms
of the product monoid `ω₁ × ω₂`. Each side leaves the other component at the identity. -/
@[expose, simps] def parallelWriterT {ι₁ : Type u} {ι₂ : Type v}
    {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{v, w} ι₂}
    {m : Type w → Type x} [Functor m] {ω₁ ω₂ : Type w} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec₁ (WriterT ω₁ m))
    (impl₂ : QueryImpl spec₂ (WriterT ω₂ m)) :
    QueryImpl (spec₁ + spec₂) (WriterT (ω₁ × ω₂) m) where
  toFun
  | .inl t => WriterT.mk <| Prod.map id (·, (1 : ω₂)) <$> (impl₁ t).run
  | .inr t => WriterT.mk <| Prod.map id ((1 : ω₁), ·) <$> (impl₂ t).run

/-- Indexed version of `QueryImpl.parallelWriterT`. Each query for index `t` writes into the
`t`-th component of the pi-product `(t : τ) → ω t`, leaving every other component at the
identity. Note that `m` cannot vary with `t`. -/
@[expose, simps] def sigmaWriterT {τ : Type} [DecidableEq τ] {ι : τ → Type v}
    {spec : (t : τ) → OracleSpec.{v, w} (ι t)}
    {m : Type w → Type x} [Functor m] {ω : τ → Type w} [(t : τ) → Monoid (ω t)]
    (impl : (t : τ) → QueryImpl (spec t) (WriterT (ω t) m)) :
    QueryImpl (OracleSpec.sigma spec) (WriterT ((t : τ) → ω t) m) where
  toFun
  | ⟨t, q⟩ => WriterT.mk <| Prod.map id (Function.update (fun _ => 1) t) <$> (impl t q).run

/-- Reassociate a nested writer transformer into one product log.

The outer log is the first component of the product; the inner/base log is the second. This
is the writer-transformer analogue of `flattenStateT`. The resulting `WriterT (ω₁ × ω₂) m`
carries both logs as a product. -/
@[expose, simps] def flattenWriterT {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] {ω₁ ω₂ : Type u}
    (impl : QueryImpl spec (WriterT ω₁ (WriterT ω₂ m))) :
    QueryImpl spec (WriterT (ω₁ × ω₂) m) where
  toFun t :=
    WriterT.mk <| do
    let ((a, w₁), w₂) ← (impl t).run.run
    pure (a, (w₁, w₂))

/-- Read a handler over `StateT σ (WriterT ω m)` as a handler over the product state `σ × ω`:
each query appends the log it writes to the second component. This is the state-over-writer
analogue of `flattenStateT`. -/
@[expose, simps -isSimp] def flattenStateTWriterT {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Functor m] {σ ω : Type u} [Append ω]
    (impl : QueryImpl spec (StateT σ (WriterT ω m))) :
    QueryImpl spec (StateT (σ × ω) m) where
  toFun t :=
    StateT.mk fun p => (fun z => (z.1.1, (z.1.2, p.2 ++ z.2))) <$> ((impl t).run p.1).run

end QueryImpl

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u} {ω : Type u} [Monoid ω]

/-- Taking the first component of the WriterT output recovers the original computation,
when the query implementation preserves the underlying oracle behavior (hso). -/
lemma fst_map_writerT_run_simulateQ
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (hso : ∀ t, fst <$> (so t).run = liftM (query t))
    (oa : OracleComp spec α) : fst <$> (simulateQ so oa).run = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [WriterT.run_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, WriterT.run_bind, map_bind]
    refine (bind_congr fun ⟨a, w₁⟩ => ?_).trans (by rw [← bind_map_left, hso t])
    simpa [← LawfulFunctor.comp_map] using ih a

end OracleComp

/-! ## Append-logged simulations -/

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {ω : Type u}
  [EmptyCollection ω] [Append ω] [LawfulAppend ω]

/-- Simulating through a handler lifted into an append-logged `WriterT` logs nothing: the run is
the simulation through the handler, paired with the empty log. -/
lemma writerT_run_simulateQ_liftTarget {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) {α : Type u} (oa : OracleComp spec α) :
    (simulateQ (impl.liftTarget (WriterT ω m)) oa).run = (·, (∅ : ω)) <$> simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query,
      QueryImpl.liftTarget_apply, WriterT.run_monadLift', ih, map_bind, bind_map_left]
    simp

/-- Two-stage simulation through an append-logged `WriterT`: if a reduction
`red : QueryImpl spec₁ (WriterT ω (OracleComp spec₂))` followed by an inner `impl` agrees on
every query with a combined handler `game : QueryImpl spec₁ (WriterT ω n)`, then the agreement
extends to every computation. This is the append-log analogue of `simulateQ_StateT_compose`. -/
theorem simulateQ_WriterT_compose {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {n : Type u → Type v} [Monad n] [LawfulMonad n]
    (red : QueryImpl spec₁ (WriterT ω (OracleComp spec₂))) (impl : QueryImpl spec₂ n)
    (game : QueryImpl spec₁ (WriterT ω n))
    (bridge : ∀ q : spec₁.Domain, simulateQ impl (red q).run = (game q).run)
    {α : Type u} (oa : OracleComp spec₁ α) :
    simulateQ impl (simulateQ red oa).run = (simulateQ game oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query, bridge t, simulateQ_map]
    exact bind_congr fun p => by rw [ih p.1]

end OracleComp

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  {σ ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]

/-- Running a handler over `StateT σ (WriterT ω m)` under its flattened handler from `(s, w₀)` is
running it from `s` and appending its log to `w₀`. -/
theorem simulateQ_flattenStateTWriterT_run (impl : QueryImpl spec (StateT σ (WriterT ω m)))
    {α : Type u} (oa : OracleComp spec α) (s : σ) (w₀ : ω) :
    (simulateQ impl.flattenStateTWriterT oa).run (s, w₀) =
      (fun z : (α × σ) × ω => (z.1.1, (z.1.2, w₀ ++ z.2))) <$> ((simulateQ impl oa).run s).run := by
  induction oa using OracleComp.inductionOn generalizing s w₀ with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
      map_bind, QueryImpl.flattenStateTWriterT_apply, StateT.run_mk, bind_map_left]
    refine bind_congr fun z => ?_
    rw [ih z.1.1 z.1.2 (w₀ ++ z.2)]
    simp [Functor.map_map, LawfulAppend.append_assoc]

/-- The run of a handler over `StateT σ (WriterT ω m)` from the empty log, read off the run of its
flattened handler. -/
theorem run_simulateQ_eq_map_flattenStateTWriterT
    (impl : QueryImpl spec (StateT σ (WriterT ω m))) {α : Type u} (oa : OracleComp spec α)
    (s : σ) :
    ((simulateQ impl oa).run s).run =
      (fun w => ((w.1, w.2.1), w.2.2)) <$> (simulateQ impl.flattenStateTWriterT oa).run (s, ∅) := by
  rw [simulateQ_flattenStateTWriterT_run, Functor.map_map]
  simp

end OracleComp
