/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# The query log of a run with fixed answers

Answering every query of a free program with a fixed answer function `ans : QueryImpl spec Id`
(`evalWithAnswerFn ans oa`) follows one path through the program. `OracleComp.runLog ans oa` is
the list of the queries on that path, oldest first, each with its answer. It is the log that
`withQueryLog` records when run with the same answers (`OracleComp.evalWithAnswerFn_withQueryLog`).

* The log of a sequence concatenates the logs (`OracleComp.runLog_bind`), and a query logs itself
  (`OracleComp.runLog_query`). Logging a program makes the program's own queries
  (`OracleComp.runLog_withQueryLog`).
* The log of a simulation concatenates the logs of the handler's programs at the queries of the
  simulated run (`OracleComp.runLog_simulateQ`).
* Answer functions that agree at every logged query give the same run and the same log
  (`OracleComp.evalWithAnswerFn_eq_of_forall_mem_runLog`,
  `OracleComp.runLog_eq_of_forall_mem_runLog`).
* A run makes only queries the program may make
  (`OracleComp.forall_mem_runLog_of_allQueriesSatisfy`), so answer functions that agree on those
  queries give the same log (`OracleComp.runLog_eq_of_allQueriesSatisfy`).
* A program making at most `n` queries satisfying `p` logs at most `n` of them
  (`OracleComp.length_filterMap_runLog_le`).
-/

public section

open OracleSpec

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-- The queries of the run of `oa` with the answers `ans`, oldest first, each with its answer. -/
def runLog (ans : QueryImpl spec Id) (oa : OracleComp spec α) : QueryLog spec :=
  ((simulateQ ans.withLogging oa).run).2

/-- The logged run with fixed answers is the run paired with its log. -/
theorem run_simulateQ_withLogging_eq_runLog (ans : QueryImpl spec Id) (oa : OracleComp spec α) :
    (simulateQ ans.withLogging oa).run = (evalWithAnswerFn ans oa, runLog ans oa) :=
  Prod.ext (QueryImpl.fst_map_run_withLogging ans oa) rfl

@[simp] theorem runLog_pure (ans : QueryImpl spec Id) (a : α) :
    runLog ans (pure a : OracleComp spec α) = [] := by
  rw [runLog]
  rfl

theorem runLog_bind (ans : QueryImpl spec Id) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) :
    runLog ans (oa >>= f) = runLog ans oa ++ runLog ans (f (evalWithAnswerFn ans oa)) := by
  rw [runLog, simulateQ_bind, WriterT.run_bind', run_simulateQ_withLogging_eq_runLog]
  rfl

@[simp] theorem runLog_query (ans : QueryImpl spec Id) (t : spec.Domain) :
    runLog ans (liftM (spec.query t) : OracleComp spec _) = [⟨t, ans t⟩] := by
  rw [runLog, simulateQ_spec_query, QueryImpl.withLogging_apply]
  rfl

@[simp] theorem runLog_query_bind (ans : QueryImpl spec Id) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    runLog ans (liftM (spec.query t) >>= k) = ⟨t, ans t⟩ :: runLog ans (k (ans t)) := by
  rw [runLog_bind, runLog_query]
  rfl

@[simp] theorem runLog_map (ans : QueryImpl spec Id) (g : α → β) (oa : OracleComp spec α) :
    runLog ans (g <$> oa) = runLog ans oa := by
  rw [map_eq_bind_pure_comp, runLog_bind, Function.comp_apply, runLog_pure, List.append_nil]

/-- Logging a program and answering it with `ans` gives the run with `ans` and its log. -/
@[simp] theorem evalWithAnswerFn_withQueryLog (ans : QueryImpl spec Id) (oa : OracleComp spec α) :
    evalWithAnswerFn ans oa.withQueryLog = (evalWithAnswerFn ans oa, runLog ans oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [withQueryLog] at ih ⊢
    simp [WriterT.run_tell, -QueryImpl.ofLift_eq_id', ih]

/-- Logging a program makes the queries the program makes. -/
@[simp] theorem runLog_withQueryLog (ans : QueryImpl spec Id) (oa : OracleComp spec α) :
    runLog ans oa.withQueryLog = runLog ans oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [withQueryLog] at ih ⊢
    simp [WriterT.run_tell, -QueryImpl.ofLift_eq_id', ih]

/-! ## Simulation -/

/-- **The log of a simulation.** Running `simulateQ impl oa` with the answers `ans` makes, in
order, the queries of the handler's programs at the queries of the run of `oa`, whose answers are
those of the handler's programs run with `ans`. -/
theorem runLog_simulateQ {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} (ans : QueryImpl spec' Id)
    (impl : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α) :
    runLog ans (simulateQ impl oa) =
      (runLog (fun t => evalWithAnswerFn ans (impl t)) oa).flatMap
        fun e => runLog ans (impl e.1) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, runLog_bind, runLog_query_bind, ih,
      List.flatMap_cons]

/-- A query of the simulated run is a query of the handler's program at some query of the run of
the program. -/
theorem mem_runLog_simulateQ {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (ans : QueryImpl spec' Id) (impl : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) {e' : (t : spec'.Domain) × spec'.Range t} :
    e' ∈ runLog ans (simulateQ impl oa) ↔
      ∃ e ∈ runLog (fun t => evalWithAnswerFn ans (impl t)) oa, e' ∈ runLog ans (impl e.1) := by
  rw [runLog_simulateQ, List.mem_flatMap]

/-! ## Agreeing answers -/

/-- **Identical until bad, on one path.** Answer functions that agree with `ans` at every query of
the run with `ans` give the same run. -/
theorem evalWithAnswerFn_eq_of_forall_mem_runLog {ans ans' : QueryImpl spec Id}
    {oa : OracleComp spec α} (h : ∀ e ∈ runLog ans oa, ans e.1 = ans' e.1) :
    evalWithAnswerFn ans oa = evalWithAnswerFn ans' oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [runLog_query_bind] at h
    have ht : ans t = ans' t := h _ List.mem_cons_self
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_liftM_query, ih (ans t) fun e he => h e (List.mem_cons_of_mem _ he), ht]

/-- Answer functions that agree with `ans` at every query of the run with `ans` give the same
log. -/
theorem runLog_eq_of_forall_mem_runLog {ans ans' : QueryImpl spec Id}
    {oa : OracleComp spec α} (h : ∀ e ∈ runLog ans oa, ans e.1 = ans' e.1) :
    runLog ans oa = runLog ans' oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [runLog_query_bind] at h
    have ht : ans t = ans' t := h _ List.mem_cons_self
    rw [runLog_query_bind, runLog_query_bind,
      ih (ans t) fun e he => h e (List.mem_cons_of_mem _ he), ht]

/-! ## Query predicates and bounds -/

/-- A run makes only queries that the program may make. -/
theorem forall_mem_runLog_of_allQueriesSatisfy (ans : QueryImpl spec Id) {P : ι → Prop}
    {oa : OracleComp spec α} (h : oa.AllQueriesSatisfy P) : ∀ e ∈ runLog ans oa, P e.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    intro e he
    rw [runLog_query_bind, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact ih (ans t) (h.2 (ans t)) e he

/-- Answer functions that agree on every query satisfying `P` give the same log, for a program
whose queries all satisfy `P`. -/
theorem runLog_eq_of_allQueriesSatisfy {ans ans' : QueryImpl spec Id} {P : ι → Prop}
    (hans : ∀ t, P t → ans t = ans' t) {oa : OracleComp spec α} (h : oa.AllQueriesSatisfy P) :
    runLog ans oa = runLog ans' oa :=
  runLog_eq_of_forall_mem_runLog fun e he =>
    hans e.1 (forall_mem_runLog_of_allQueriesSatisfy ans h e he)

/-- **A query bound bounds a log.** If `oa` makes at most `n` queries satisfying `p` on every path,
the run with `ans` logs at most `n` entries that `f` keeps, when `f` keeps only queries satisfying
`p`. -/
theorem length_filterMap_runLog_le (ans : QueryImpl spec Id) {p : ι → Prop} [DecidablePred p]
    {X : Type*} (f : ((t : spec.Domain) × spec.Range t) → Option X)
    (hf : ∀ e, (f e).isSome → p e.1) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : ((runLog ans oa).filterMap f).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [runLog_query_bind, List.filterMap_cons]
    cases hfe : f ⟨t, ans t⟩ with
    | none =>
      refine (ih (ans t) (h.2 (ans t))).trans ?_
      split_ifs <;> omega
    | some x =>
      have hp : p t := hf ⟨t, ans t⟩ (by rw [hfe]; rfl)
      have hn : 0 < n := h.1.resolve_left (not_not.2 hp)
      have := ih (ans t) (h.2 (ans t))
      simp only [hp, ↓reduceIte] at this
      rw [List.length_cons]
      omega

end OracleComp
