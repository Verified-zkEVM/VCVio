/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import VCVio.OracleComp.SimSemantics.WriterT.Core
public import PolyFun.Control.Trace
public import ToMathlib.Control.WriterT

/-!
# Trace instrumentation

Writer-valued instrumentation records query-dependent observations before a handler runs,
or response-dependent observations after a response returns. Projection recovers the original
computation for any lawful base monad.
-/

public section

open OracleSpec OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-! ### `withTraceBefore`: response-independent trace, recorded before handler -/

section withTraceBefore

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records `traceFn t` in
the writer `ω` *before* running the handler. The trace value depends only on
the query. Failure in the base monad can discard the entire writer result. -/
abbrev withTraceBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceBefore (P := spec.toPFunctor) so traceFn

@[grind =]
lemma withTraceBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (t : spec.Domain) :
    so.withTraceBefore traceFn t = (do tell (traceFn t); so t) := by
  exact PFunctor.Handler.withTraceBefore_apply (P := spec.toPFunctor) so traceFn t

lemma fst_map_run_withTraceBefore [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run = simulateQ so mx := by
  have h : so.withTraceBefore traceFn =
      so.preInsert (fun t => tell (traceFn t)) :=
    PFunctor.Handler.withTraceBefore_eq_preInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_preInsert so (fun t => tell (traceFn t))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure WriterT.fst_map_run_bind
    (fun t => by simp) mx

/-- When every query traces to the monoid identity `1`, `withTraceBefore` is a
no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTraceBefore_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTraceBefore (fun _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn <;> simp [*]

lemma support_fst_run_withTraceBefore [LawfulMonad m] [MonadAttach m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceBefore]

end withTraceBefore

/-! ### `withTrace`: response-dependent trace, recorded after handler -/

section withTrace

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`.
A handler failure skips the trace (the response never materialised). -/
abbrev withTrace (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTrace (P := spec.toPFunctor) so traceFn

@[grind =]
lemma withTrace_apply (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (t : spec.Domain) :
    so.withTrace traceFn t = (do let u ← so t; tell (traceFn t u); return u) := by
  exact PFunctor.Handler.withTrace_apply (P := spec.toPFunctor) so traceFn t

lemma fst_map_run_withTrace [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run = simulateQ so mx := by
  have h : so.withTrace traceFn =
      so.postInsert (fun t u => tell (traceFn t u)) :=
    PFunctor.Handler.withTrace_eq_postInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_postInsert so (fun t u => tell (traceFn t u))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure WriterT.fst_map_run_bind
    (fun t => by simp) mx

/-- When every query/response pair traces to the monoid identity `1`,
`withTrace` is a no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTrace_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTrace (fun _ _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn <;> simp [*]

lemma support_fst_run_withTrace [LawfulMonad m] [MonadAttach m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTrace]

end withTrace

/-! ### `withTraceAppendBefore`: response-independent trace, recorded before
handler, accumulating via `∅` / `++` -/

section withTraceAppendBefore

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTraceBefore`: each query records
`traceFn t` in the writer `ω` *before* running the handler, and `WriterT`
uses the `[EmptyCollection ω] [Append ω]` `Monad` instance (`tell` is a single
push, `bind` concatenates with `++`). The trace value depends only on the
query. Failure in the base monad can discard the entire writer result. -/
abbrev withTraceAppendBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceAppendBefore (P := spec.toPFunctor) so traceFn

@[grind =]
lemma withTraceAppendBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (t : spec.Domain) :
    so.withTraceAppendBefore traceFn t = (do tell (traceFn t); so t) := by
  exact PFunctor.Handler.withTraceAppendBefore_apply (P := spec.toPFunctor) so traceFn t

lemma fst_map_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run = simulateQ so mx := by
  have h : so.withTraceAppendBefore traceFn =
      so.preInsert (fun t => tell (traceFn t)) :=
    PFunctor.Handler.withTraceAppendBefore_eq_preInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_preInsert so (fun t => tell (traceFn t))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure' WriterT.fst_map_run_bind'
    (fun t => by simp [seqRight_eq_bind]) mx
lemma support_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadAttach m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppendBefore]

end withTraceAppendBefore

/-! ### `withTraceAppend`: response-dependent trace, recorded after handler,
accumulating via `∅` / `++` -/

section withTraceAppend

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTrace`: each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`,
using the `[EmptyCollection ω] [Append ω]` `Monad (WriterT ω m)` instance.
A handler failure skips the trace (the response never materialised). -/
abbrev withTraceAppend (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceAppend (P := spec.toPFunctor) so traceFn

@[grind =]
lemma withTraceAppend_apply (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (t : spec.Domain) :
    so.withTraceAppend traceFn t = (do let u ← so t; tell (traceFn t u); return u) := by
  exact PFunctor.Handler.withTraceAppend_apply (P := spec.toPFunctor) so traceFn t

lemma fst_map_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run = simulateQ so mx := by
  have h : so.withTraceAppend traceFn =
      so.postInsert (fun t u => tell (traceFn t u)) :=
    PFunctor.Handler.withTraceAppend_eq_postInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_postInsert so (fun t u => tell (traceFn t u))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure' WriterT.fst_map_run_bind'
    (fun t => by simp) mx
lemma support_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadAttach m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppend]

end withTraceAppend

end QueryImpl
