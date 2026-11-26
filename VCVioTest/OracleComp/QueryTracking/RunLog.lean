/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.QueryTracking.RunLog
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Run logs, handler bounds and unqueried cache entries

Concrete checks of `OracleComp.runLog` and of the query-bound, probability and cache lemmas around
it. Each bound comes with a case showing that it is attained or that its hypothesis is needed.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace VCVioTest.RunLog

/-- Query the point `true`, then query the answer. -/
@[expose] def twoQueries : OracleComp (Bool →ₒ Bool) Bool := do
  let b ← liftM ((Bool →ₒ Bool).query true)
  liftM ((Bool →ₒ Bool).query b)

/-- Query the point `true` once. -/
@[expose] def queryTrue : OracleComp (Bool →ₒ Bool) Bool := liftM ((Bool →ₒ Bool).query true)

/-- Answer every query `true`. -/
@[expose] def allTrue : QueryImpl (Bool →ₒ Bool) Id := fun _ => true

/-- Answer every query `false`. -/
@[expose] def allFalse : QueryImpl (Bool →ₒ Bool) Id := fun _ => false

/-- Answer every query with itself. -/
@[expose] def echo : QueryImpl (Bool →ₒ Bool) Id := fun b => b

/-- Answer a query by asking it twice and returning the second answer. -/
@[expose] def twice : QueryImpl (Bool →ₒ Bool) (OracleComp (Bool →ₒ Bool)) := fun t => do
  let _ ← liftM ((Bool →ₒ Bool).query t)
  liftM ((Bool →ₒ Bool).query t)

/-- Keep the log entries at the point `true`. -/
@[expose] def atTrue : ((t : (Bool →ₒ Bool).Domain) × (Bool →ₒ Bool).Range t) → Option Unit :=
  fun e => if e.1 = true then some () else none

/-! ## Logs -/

-- The log records each query with its answer, oldest first.
example : runLog allTrue twoQueries = [⟨true, true⟩, ⟨true, true⟩] := by
  simp [twoQueries, allTrue]

example : runLog allFalse twoQueries = [⟨true, false⟩, ⟨false, false⟩] := by
  simp [twoQueries, allFalse]

-- Logging and answering gives the run paired with its log, and logging adds no query.
example : evalWithAnswerFn allFalse twoQueries.withQueryLog =
    (false, [⟨true, false⟩, ⟨false, false⟩]) := by
  simp [twoQueries, allFalse]

example : runLog allTrue twoQueries.withQueryLog = runLog allTrue twoQueries :=
  runLog_withQueryLog _ _

-- The log of a simulation concatenates the handler's logs.
example : runLog allTrue (simulateQ twice queryTrue) = [⟨true, true⟩, ⟨true, true⟩] := by
  rw [runLog_simulateQ]
  simp [queryTrue, twice, allTrue]

/-! ## Agreeing answers -/

-- `allTrue` and `echo` agree at `true`, the only point the run with `allTrue` queries.
example : evalWithAnswerFn allTrue twoQueries = evalWithAnswerFn echo twoQueries :=
  evalWithAnswerFn_eq_of_forall_mem_runLog fun e he => by
    simp only [twoQueries, allTrue, runLog_query_bind, runLog_query, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl

example : runLog allTrue twoQueries = runLog echo twoQueries :=
  runLog_eq_of_forall_mem_runLog fun e he => by
    simp only [twoQueries, allTrue, runLog_query_bind, runLog_query, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl

-- Answers that differ at a queried point can change the run.
example : evalWithAnswerFn allTrue twoQueries ≠ evalWithAnswerFn allFalse twoQueries := by
  simp [twoQueries, allTrue, allFalse]

-- A program querying only `true` has the same run and log under answers agreeing at `true`.
example : evalWithAnswerFn allTrue queryTrue = evalWithAnswerFn echo queryTrue :=
  evalWithAnswerFn_eq_of_allQueriesSatisfy (P := (· = true)) (fun t ht => by subst ht; rfl)
    (by simp [queryTrue])

example : runLog allTrue queryTrue = runLog echo queryTrue :=
  runLog_eq_of_allQueriesSatisfy (P := (· = true)) (fun t ht => by subst ht; rfl)
    (by simp [queryTrue])

-- The same answers differ off `true`, so the program's predicate is needed.
example : evalWithAnswerFn allTrue (liftM ((Bool →ₒ Bool).query false)) ≠
    evalWithAnswerFn echo (liftM ((Bool →ₒ Bool).query false)) := by
  simp [allTrue, echo]

/-! ## Query bounds -/

/-- `twoQueries` makes at most two queries at `true`. -/
theorem twoQueries_bound : twoQueries.IsQueryBoundP (· = true) 2 := by
  simp only [twoQueries, isQueryBoundP_query_bind_iff, isQueryBoundP_query_iff]
  exact ⟨Or.inr (by decide), fun u => fun _ => by split_ifs <;> decide⟩

-- The run with `allTrue` attains the bound, so `twoQueries` makes two queries at `true`.
example : ((runLog allTrue twoQueries).filterMap atTrue).length = 2 := by
  simp [twoQueries, allTrue, atTrue]

example : ¬ twoQueries.IsQueryBoundP (· = true) 1 := fun h => by
  have := length_filterMap_runLog_le allTrue atTrue
    (fun e he => by simpa [atTrue] using he) h
  simp [twoQueries, allTrue, atTrue] at this

-- Sequencing with a weakened sum.
example : (queryTrue >>= fun _ => queryTrue).IsQueryBoundP (· = true) 3 :=
  isQueryBoundP_bind_le (n := 1) (m := 1) (by simp [queryTrue])
    (fun _ _ => by simp [queryTrue]) (by decide)

-- `twice` makes two queries at `true` for a query at `true`, and none for a query at `false`.
theorem twice_simulateQ_bound : (simulateQ twice queryTrue).IsQueryBoundP (· = true) 2 := by
  refine IsQueryBoundP.simulateQ_of_step_le (p := (· = true)) (n := 1) (cost := 2) ?_ ?_ ?_
  · simp [queryTrue]
  · rintro t rfl
    simp [twice]
  · rintro t ht
    simp only [Bool.not_eq_true] at ht
    subst ht
    simp [twice]

-- The multiplied bound is attained.
example : ¬ (simulateQ twice queryTrue).IsQueryBoundP (· = true) 1 := fun h => by
  have := length_filterMap_runLog_le allTrue atTrue
    (fun e he => by simpa [atTrue] using he) h
  rw [runLog_simulateQ] at this
  simp [queryTrue, twice, allTrue, atTrue] at this

-- Logging and mapping keep query bounds and query predicates.
example : twoQueries.withQueryLog.IsQueryBoundP (· = true) 2 :=
  (isQueryBoundP_withQueryLog_iff _ _ _).2 twoQueries_bound

example : (Prod.fst <$> queryTrue.withQueryLog).AllQueriesSatisfy (· = true) := by
  rw [allQueriesSatisfy_map_iff, allQueriesSatisfy_withQueryLog_iff]
  simp [queryTrue]

example : ¬ twoQueries.withQueryLog.AllQueriesSatisfy (· = true) := by
  rw [allQueriesSatisfy_withQueryLog_iff]
  simp [twoQueries]

/-! ## Fixed answers in a lawful monad -/

example : simulateQ (fun t => (pure (allFalse t) : Option Bool)) twoQueries =
    some (evalWithAnswerFn allFalse twoQueries) :=
  simulateQ_pure_eq_evalWithAnswerFn allFalse twoQueries

/-! ## Probability bounds -/

-- The union bound over a list counts a repeated event twice; the empty list bounds by zero.
example (mx : ProbComp Bool) (E : ℕ → Bool → Prop) :
    Pr{let b ← mx}[∃ i ∈ [0, 1, 1], E i b] ≤
      Pr{let b ← mx}[E 0 b] + (Pr{let b ← mx}[E 1 b] + (Pr{let b ← mx}[E 1 b] + 0)) :=
  prEvent_exists_list_le [0, 1, 1] mx E

example (mx : ProbComp Bool) (E : ℕ → Bool → Prop) :
    Pr{let b ← mx}[∃ i ∈ ([] : List ℕ), E i b] ≤ 0 :=
  prEvent_exists_list_le [] mx E

-- An event is bounded through an implication off a third event.
example (mx : ProbComp Bool) :
    Pr{let b ← mx}[b = true] ≤ Pr{let _ ← mx}[False] + Pr{let b ← mx}[b = true] :=
  prEvent_le_prEvent_add_prEvent_of_imp mx fun _ h hr => hr h

-- Without the implication the bound fails: a sure event is not bounded by two null ones.
example : ¬ Pr{let _ ← (pure () : ProbComp Unit)}[True] ≤
    Pr{let _ ← (pure () : ProbComp Unit)}[False] +
      Pr{let _ ← (pure () : ProbComp Unit)}[False] := by
  simp

-- The distance bound is attained: the third event carries the whole distance.
example : ENNReal.absDiff Pr{let _ ← (pure () : ProbComp Unit)}[True]
      Pr{let _ ← (pure () : ProbComp Unit)}[False] =
    ENNReal.absDiff Pr{let _ ← (pure () : ProbComp Unit)}[True ∧ ¬ True]
      Pr{let _ ← (pure () : ProbComp Unit)}[False ∧ ¬ True] +
      Pr{let _ ← (pure () : ProbComp Unit)}[True] := by
  simp

example (mx : ProbComp Bool) (p q r : Bool → Prop) :
    ENNReal.absDiff Pr{let b ← mx}[p b] Pr{let b ← mx}[q b] ≤
      ENNReal.absDiff Pr{let b ← mx}[p b ∧ ¬ r b] Pr{let b ← mx}[q b ∧ ¬ r b] +
        Pr{let b ← mx}[r b] :=
  absDiff_prEvent_le_absDiff_prEvent_and_not_add mx p q r

-- `simp` closes a two-step null event.
example : Pr{let _ ← $ᵗ Bool; let _ ← $ᵗ Bool}[False] = 0 := by simp

/-! ## Unqueried cache entries -/

/-- A cache answering `true` at the point `false`. -/
@[expose] def cacheT : (Bool →ₒ Bool).QueryCache :=
  (∅ : (Bool →ₒ Bool).QueryCache).cacheQuery false true

/-- A cache answering `false` at the point `false`; it differs from `cacheT` only there. -/
@[expose] def cacheF : (Bool →ₒ Bool).QueryCache :=
  (∅ : (Bool →ₒ Bool).QueryCache).cacheQuery false false

-- A cached run with fixed answers that never queries `false` ignores the cache there.
example : Prod.fst <$> (simulateQ allTrue.withCaching queryTrue).run cacheT =
    Prod.fst <$> (simulateQ allTrue.withCaching queryTrue).run cacheF :=
  QueryImpl.fst_map_run_simulateQ_withCaching_eq_of_allQueriesSatisfy allTrue
    (P := (· = true)) (by simp [queryTrue])
    (fun t ht => by subst ht; simp [cacheT, cacheF])

-- A run that queries `false` reads the cache there.
example : Prod.fst <$> (simulateQ allTrue.withCaching (liftM ((Bool →ₒ Bool).query false))).run
      cacheT ≠
    Prod.fst <$> (simulateQ allTrue.withCaching (liftM ((Bool →ₒ Bool).query false))).run
      cacheF := by
  simp [cacheT, cacheF]

/-- Hash the point `true` in the random oracle model. -/
@[expose] def hashTrue : OracleComp (unifSpec + (Bool →ₒ Bool)) Bool :=
  liftM ((unifSpec + (Bool →ₒ Bool)).query (.inr true))

/-- Hash the point `false` in the random oracle model. -/
@[expose] def hashFalse : OracleComp (unifSpec + (Bool →ₒ Bool)) Bool :=
  liftM ((unifSpec + (Bool →ₒ Bool)).query (.inr false))

-- The random oracle's answer at a point the program never hashes does not matter.
example : Prod.fst <$> (simulateQ (Bool →ₒ Bool).romImpl hashTrue).run cacheT =
    Prod.fst <$> (simulateQ (Bool →ₒ Bool).romImpl hashTrue).run cacheF :=
  fst_map_run_simulateQ_romImpl_eq_of_allQueriesSatisfy (P := (· = true))
    (by simp [hashTrue]) (fun t ht => by subst ht; simp [cacheT, cacheF])

-- At a point the program hashes, it does.
example : Prod.fst <$> (simulateQ (Bool →ₒ Bool).romImpl hashFalse).run cacheT ≠
    Prod.fst <$> (simulateQ (Bool →ₒ Bool).romImpl hashFalse).run cacheF := by
  simp [hashFalse, cacheT, cacheF]

end VCVioTest.RunLog
