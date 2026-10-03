/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.EvalDist.Expectation

/-!
# Logged runs of interleaved private sampling and a cached random oracle

The observed charge belongs to the actual cached execution: a key is charged once, on its
first query, even when later queries repeat it. The ordered oracle log and final cache remain
available for continuing the experiment. Independent uniform-sampling operations use the
separate `unifSpec` summand and never enter the random-oracle cache or log.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

variable {D α : Type} {R : D → Type}

/-- The distinct keys appearing in an ordered oracle query log. -/
@[expose] def freshKeysOfLog [DecidableEq D]
    (log : QueryLog (ofFn R)) : Finset D :=
  (log.map Sigma.fst).toFinset

@[simp] theorem freshKeysOfLog_nil [DecidableEq D] :
    freshKeysOfLog ([] : QueryLog (ofFn R)) = ∅ := rfl

@[simp] theorem freshKeysOfLog_cons [DecidableEq D]
    (q : (d : D) × R d) (log : QueryLog (ofFn R)) :
    freshKeysOfLog (q :: log) = insert q.1 (freshKeysOfLog log) := by
  simp [freshKeysOfLog]

@[simp] theorem mem_freshKeysOfLog [DecidableEq D]
    (log : QueryLog (ofFn R)) (t : D) :
    t ∈ freshKeysOfLog log ↔ ∃ q ∈ log, q.1 = t := by
  simp [freshKeysOfLog, List.mem_map]

/-- Distinct keys in a deterministic computation against a complete answer assignment. -/
@[expose] def tableFreshKeys [DecidableEq D]
    (oa : OracleComp (ofFn R) α) (g : ∀ d, R d) : Finset D :=
  freshKeysOfLog (tableQueryLog oa g)

@[simp] theorem tableFreshKeys_pure [DecidableEq D]
    (a : α) (g : ∀ d, R d) :
    tableFreshKeys (pure a : OracleComp (ofFn R) α) g = ∅ := by
  simp [tableFreshKeys]

@[simp] theorem tableFreshKeys_query_bind [DecidableEq D]
    (t : D) (k : R t → OracleComp (ofFn R) α) (g : ∀ d, R d) :
    tableFreshKeys (liftM ((ofFn R).query t) >>= k) g =
      insert t (tableFreshKeys (k (g t)) g) := by
  simp [tableFreshKeys]

/-- Whether a computation ever queries `t` is independent of the answer at `t`.
The returned value and all later queries are allowed to change. -/
theorem tableFreshKeys_mem_update [DecidableEq D]
    (oa : OracleComp (ofFn R) α) (g : ∀ d, R d)
    (t : D) (u : R t) :
    t ∈ tableFreshKeys oa (Function.update g t u) ↔
      t ∈ tableFreshKeys oa g := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
      by_cases hqt : q = t
      · subst q
        simp
      · have hval : Function.update g t u q = g q :=
          Function.update_of_ne hqt u g
        simp only [tableFreshKeys_query_bind, Finset.mem_insert, hval]
        simp only [Ne.symm hqt, false_or]
        exact ih (g q)

/-- The actual cached random-oracle experiment, with returned output, ordered hash-query log,
and final cache in one result. Private `unifSpec` draws are forwarded unchanged. An optional
failure belongs in `α`, so failed branches retain their log and cache. -/
@[expose] def randomOracleLoggedRun [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache := ∅) :
    ProbComp ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) :=
  ((simulateQ (unifSpec.passthrough + (ofFn R).randomOracle.withLogging) oa).run).run cache

/-- Execute the same interleaved program against a fixed complete RO answer assignment.
The cache and ordered log are still run and returned; only the fresh RO answers are fixed.
Private uniform draws remain independent sampling operations during the computation. -/
@[expose] def fixedTableLoggedRun [DecidableEq D]
    (oa : OracleComp (unifSpec + ofFn R) α) (g : ∀ d, R d)
    (cache : (ofFn R).QueryCache := ∅) :
    ProbComp ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) :=
  ((simulateQ (unifSpec.passthrough +
      (((QueryImpl.ofFn g).liftTarget ProbComp).withCaching).withLogging) oa).run).run cache

/-- The writer and cache handoff for a logged oracle interpreter. The continuation receives
the exact prefix cache, and its ordered log is appended after the prefix log. -/
private theorem loggedRun_bind [DecidableEq D]
    (impl : QueryImpl (unifSpec + ofFn R)
      (WriterT (QueryLog (ofFn R)) (StateT (ofFn R).QueryCache ProbComp)))
    (oa : OracleComp (unifSpec + ofFn R) α)
    {β : Type} (ob : α → OracleComp (unifSpec + ofFn R) β)
    (cache : (ofFn R).QueryCache) :
    ((simulateQ impl (oa >>= ob)).run).run cache =
      ((simulateQ impl oa).run).run cache >>= fun p =>
        (fun q => ((q.1.1, p.1.2 ++ q.1.2), q.2)) <$>
          ((simulateQ impl (ob p.1.1)).run).run p.2 := by
  simp [simulateQ_bind, WriterT.run_bind, StateT.run_bind]

/-- A fixed-table interleaved computation composes through its exact returned cache and ordered
log. This is the phase-handoff equation used by adaptive protocols. -/
theorem fixedTableLoggedRun_bind [DecidableEq D]
    (oa : OracleComp (unifSpec + ofFn R) α)
    {β : Type} (ob : α → OracleComp (unifSpec + ofFn R) β)
    (g : ∀ d, R d) (cache : (ofFn R).QueryCache) :
    fixedTableLoggedRun (oa >>= ob) g cache =
      fixedTableLoggedRun oa g cache >>= fun p =>
        (fun q => ((q.1.1, p.1.2 ++ q.1.2), q.2)) <$>
          fixedTableLoggedRun (ob p.1.1) g p.2 :=
  loggedRun_bind _ oa ob cache

/-- The actual logged random oracle uses the same cache and ordered-log handoff. -/
theorem randomOracleLoggedRun_bind [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    {β : Type} (ob : α → OracleComp (unifSpec + ofFn R) β)
    (cache : (ofFn R).QueryCache) :
    randomOracleLoggedRun (oa >>= ob) cache =
      randomOracleLoggedRun oa cache >>= fun p =>
        (fun q => ((q.1.1, p.1.2 ++ q.1.2), q.2)) <$>
          randomOracleLoggedRun (ob p.1.1) p.2 :=
  loggedRun_bind _ oa ob cache

@[simp] theorem randomOracleLoggedRun_uniformQuery [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (n : ℕ) (cache : (ofFn R).QueryCache) :
    randomOracleLoggedRun
        (liftM ((unifSpec + ofFn R).query (.inl n)) :
          OracleComp (unifSpec + ofFn R) (Fin (n + 1))) cache =
      (fun u => ((u, ([] : QueryLog (ofFn R))), cache)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := by
  simp [randomOracleLoggedRun, QueryImpl.passthrough_add,
    QueryImpl.add_apply_inl]
  have hfirst :
      ((unifSpec.passthrough : QueryImpl unifSpec
        (WriterT (QueryLog (ofFn R)) (StateT (ofFn R).QueryCache ProbComp))) n).run.run cache =
        (fun u => ((u, ([] : QueryLog (ofFn R))), cache)) <$>
          (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := rfl
  simp only [QueryImpl.liftTarget_apply, QueryImpl.id'_apply] at hfirst
  have hquery :
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) =
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl
  rw [hquery] at hfirst
  exact hfirst

@[simp] theorem fixedTableLoggedRun_uniformQuery [DecidableEq D]
    (n : ℕ) (g : ∀ d, R d) (cache : (ofFn R).QueryCache) :
    fixedTableLoggedRun
        (liftM ((unifSpec + ofFn R).query (.inl n)) :
          OracleComp (unifSpec + ofFn R) (Fin (n + 1))) g cache =
      (fun u => ((u, ([] : QueryLog (ofFn R))), cache)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := by
  simp [fixedTableLoggedRun, QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
  have hfirst :
      ((unifSpec.passthrough : QueryImpl unifSpec
        (WriterT (QueryLog (ofFn R)) (StateT (ofFn R).QueryCache ProbComp))) n).run.run cache =
        (fun u => ((u, ([] : QueryLog (ofFn R))), cache)) <$>
          (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := rfl
  have hquery :
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) =
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl
  rw [hquery] at hfirst
  simpa only [QueryImpl.liftTarget_apply, QueryImpl.id'_apply] using hfirst

theorem randomOracleLoggedRun_hashQuery [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (t : D) (cache : (ofFn R).QueryCache) :
    randomOracleLoggedRun
        (liftM ((unifSpec + ofFn R).query (.inr t)) :
          OracleComp (unifSpec + ofFn R) (R t)) cache =
      (fun p => ((p.1, [⟨t, p.1⟩]), p.2)) <$>
        ((ofFn R).randomOracle t).run cache := by
  simp [randomOracleLoggedRun, QueryImpl.passthrough_add,
    QueryImpl.add_apply_inr,
    StateT.run_bind]

theorem fixedTableLoggedRun_hashQuery [DecidableEq D]
    (t : D) (g : ∀ d, R d) (cache : (ofFn R).QueryCache) :
    fixedTableLoggedRun
        (liftM ((unifSpec + ofFn R).query (.inr t)) :
          OracleComp (unifSpec + ofFn R) (R t)) g cache =
      (fun p => ((p.1, [⟨t, p.1⟩]), p.2)) <$>
        ((((QueryImpl.ofFn g).liftTarget ProbComp).withCaching) t).run cache := by
  simp [fixedTableLoggedRun, QueryImpl.passthrough_add,
    QueryImpl.add_apply_inr,
    StateT.run_bind]

/-- The weighted distinct-query charge of an observed random-oracle log. -/
@[expose] noncomputable def freshQueryCharge [DecidableEq D]
    (error : D → ENNReal) (log : QueryLog (ofFn R)) : ENNReal :=
  ∑ t ∈ freshKeysOfLog log, error t

/-- Expected actual distinct-query charge, including all returned failure branches. -/
noncomputable def expectedFreshQueryCharge [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) (error : D → ENNReal) : ENNReal :=
  letI : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  ∫⁻ z, freshQueryCharge error z.1.2 ∂𝒟[randomOracleLoggedRun oa]

/-- Forgetting the ordered log recovers the existing random-oracle-model execution, including
its returned output and final cache. -/
theorem randomOracleLoggedRun_project [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache) :
    (fun z => (z.1.1, z.2)) <$> randomOracleLoggedRun oa cache =
      (simulateQ (ofFn R).romImpl oa).run cache := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      simp [randomOracleLoggedRun]
  | query_bind t k ih =>
      cases t with
      | inl n =>
          simp [randomOracleLoggedRun, simulateQ_bind, WriterT.run_bind,
            StateT.run_bind]
          have hfirst :
              ((unifSpec.passthrough : QueryImpl unifSpec
                (WriterT (QueryLog (ofFn R)) (StateT (ofFn R).QueryCache ProbComp))) n).run.run cache =
                (fun u => ((u, ([] : QueryLog (ofFn R))), cache)) <$>
                  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := rfl
          simp only [QueryImpl.liftTarget_apply, QueryImpl.id'_apply] at hfirst
          rw [hfirst]
          have hright :
              (unifFwdImpl (ofFn R) n).run cache =
                (fun u => (u, cache)) <$>
                  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := rfl
          rw [hright]
          simp only [bind_map_left]
          apply bind_congr
          intro u
          simpa only [randomOracleLoggedRun, QueryImpl.passthrough_add] using ih u cache
      | inr t =>
          simp [randomOracleLoggedRun, simulateQ_bind, WriterT.run_bind,
            StateT.run_bind]
          apply bind_congr
          intro p
          exact ih p.1 p.2

end OracleComp
