/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.PFunctor.Handler.Normalization
import VCVio.OracleComp.QueryTracking.CachingLoggingOracle
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Handler Normalization for Query Handlers

The `handler_simp` simp set extends PolyFun's generic `handler_nf` normal form
with VCVio query simulation, instrumentation, caching, and local WriterT
compatibility equations.

The goal is not to create a second proof mode; it is just the shared "open the
handler one step" surface that proof scripts can use before handing control
back to `mvcgen`, `vcstep`, `rvcstep`, or ordinary support reasoning.
-/

attribute [handler_simp]
  simulateQ_pure
  simulateQ_bind
  simulateQ_query
  simulateQ_spec_query
  simulateQ_query_bind
  OracleQuery.input_query
  OracleQuery.cont_query
  QueryImpl.withTraceBefore_apply
  QueryImpl.withTrace_apply
  QueryImpl.withTraceAppendBefore_apply
  QueryImpl.withTraceAppend_apply
  QueryImpl.withCaching_apply
  QueryImpl.withLogging_apply
  QueryImpl.appendInputLog_apply
  QueryImpl.withCost_apply
  QueryImpl.withCounting_apply
  QueryImpl.withPregen_apply
  QueryImpl.withCachingTraceAppend_apply
  QueryImpl.withCachingLogging_apply
  QueryImpl.extendState_apply
  QueryImpl.withBadFlag_apply_run
  QueryImpl.withBadUpdate_apply_run
  cachingOracle.apply_eq
  seededOracle.apply_eq
  cachingLoggingOracle.apply_eq
  WriterT.run_bind'
  WriterT.run_monadLift
  WriterT.run_monadLift'
  WriterT.run_pure'
