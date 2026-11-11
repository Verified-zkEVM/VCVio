/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.Structures

/-!
# Checking query logs

A query log `log : QueryLog spec` lists query-answer pairs. This file defines three checks of a
log against an oracle:

* `QueryLog.Consistent log`: any two entries with the same query are equal, so no query is logged
  with two different answers;
* `QueryLog.agreesWith cache log`: every logged answer is the answer stored in the partial table
  `cache`; a logged query with no cached answer rejects;
* `QueryLog.recheck log`: the oracle computation that queries every logged input again, in order,
  and accepts when every answer is the logged one. Every query is made, with no short-circuit.

Against a fixed answer function `H`, `recheck log` accepts exactly when every logged answer is the
value of `H` at its query (`QueryLog.evalWithAnswerFn_recheck`), which is `agreesWith` against the
total table of `H` (`QueryLog.agreesWith_ofFn_some`). Removing duplicate entries preserves
`agreesWith` and the acceptance of `recheck` against a fixed answer function
(`QueryLog.agreesWith_dedup`, `QueryLog.evalWithAnswerFn_recheck_dedup`).
-/

public section

open OracleComp

universe u v

namespace OracleSpec.QueryLog

variable {ι : Type u}

/-! ## Consistent logs -/

section Consistent

variable {spec : OracleSpec.{u, v} ι}

/-- A query log is consistent when any two entries with the same query are equal: no query is
logged with two different answers. -/
@[expose]
def Consistent (log : QueryLog spec) : Prop :=
  ∀ p ∈ log, ∀ q ∈ log, p.1 = q.1 → p = q

/-- The empty log is consistent. -/
@[simp]
theorem consistent_nil : Consistent ([] : QueryLog spec) := by
  simp [Consistent]

/-- A log with one entry is consistent. -/
@[simp]
theorem consistent_singleton (p : (t : spec.Domain) × spec.Range t) : Consistent [p] := by
  intro q hq r hr _
  rw [List.mem_singleton.mp hq, List.mem_singleton.mp hr]

/-- For a single function oracle, a log is consistent when entries with the same input have the
same output. -/
theorem consistent_iff {X : Type u} {Y : Type v} {log : QueryLog (X →ₒ Y)} :
    log.Consistent ↔ ∀ p ∈ log, ∀ q ∈ log, p.1 = q.1 → p.2 = q.2 := by
  refine forall₂_congr fun p _ ↦ forall₂_congr fun q _ ↦ imp_congr_right fun h ↦ ?_
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  obtain rfl : x = x' := h
  simp

end Consistent

/-! ## Agreement with a partial table -/

section agreesWith

variable {spec : OracleSpec.{u, v} ι} [∀ t, DecidableEq (spec.Range t)]

/-- Check a log against a partial answer table: accept when every logged answer is the answer
stored in `cache` at its query; a query with no cached answer rejects (the paper's `CheckIO^D`,
ePrint 2025/2166, p. 53). -/
@[expose]
def agreesWith (cache : QueryCache spec) (log : QueryLog spec) : Bool :=
  log.all fun p ↦ decide (cache p.1 = some p.2)

/-- `agreesWith` accepts exactly when every logged entry is in the table. -/
theorem agreesWith_eq_true_iff (cache : QueryCache spec) (log : QueryLog spec) :
    agreesWith cache log = true ↔ ∀ p ∈ log, cache p.1 = some p.2 := by
  simp [agreesWith]

/-- Repeating a check is idempotent: removing duplicate entries does not change acceptance. -/
theorem agreesWith_dedup [DecidableEq ι] (cache : QueryCache spec) (log : QueryLog spec) :
    agreesWith cache log.dedup = agreesWith cache log := by
  rw [Bool.eq_iff_iff, agreesWith_eq_true_iff, agreesWith_eq_true_iff]
  simp [List.mem_dedup]

end agreesWith

/-! ## Querying the logged inputs again -/

section recheck

variable {spec : OracleSpec.{u, 0} ι} [∀ t, DecidableEq (spec.Range t)]

/-- One step of `recheck`: query `p.1`, compare the answer with `p.2`, and conjoin the result
with the running verdict `acc`. -/
@[expose]
def recheckStep (acc : Bool) (p : (t : spec.Domain) × spec.Range t) : OracleComp spec Bool := do
  let u : spec.Range p.1 ← spec.query p.1
  pure (acc && decide (u = p.2))

/-- Query every logged input and compare the answer with the logged one (the paper's
`CheckIO^f`, ePrint 2025/2166, Def 8.1, p. 52). Every query is made, with no short-circuit. -/
@[expose]
def recheck (log : QueryLog spec) : OracleComp spec Bool :=
  log.foldlM recheckStep true

/-- One step of `recheck` against a fixed function compares the answer with the logged one. -/
@[simp]
theorem evalWithAnswerFn_recheckStep (H : (t : spec.Domain) → spec.Range t) (acc : Bool)
    (p : (t : spec.Domain) × spec.Range t) :
    evalWithAnswerFn (QueryImpl.ofFn H) (recheckStep acc p) = (acc && decide (H p.1 = p.2)) :=
  rfl

private theorem evalWithAnswerFn_foldlM_recheckStep (H : (t : spec.Domain) → spec.Range t)
    (log : QueryLog spec) (acc : Bool) :
    evalWithAnswerFn (QueryImpl.ofFn H) (log.foldlM recheckStep acc) =
      (acc && log.all fun p ↦ decide (H p.1 = p.2)) := by
  induction log generalizing acc with
  | nil => simp
  | cons p log ih =>
      rw [List.foldlM_cons, evalWithAnswerFn_bind, ih, evalWithAnswerFn_recheckStep]
      simp [Bool.and_assoc]

/-- Against a fixed function `H`, `recheck log` accepts exactly when every logged answer is the
value of `H` at its query. -/
theorem evalWithAnswerFn_recheck (H : (t : spec.Domain) → spec.Range t) (log : QueryLog spec) :
    evalWithAnswerFn (QueryImpl.ofFn H) (recheck log) = log.all fun p ↦ decide (H p.1 = p.2) := by
  rw [recheck, evalWithAnswerFn_foldlM_recheckStep, Bool.true_and]

/-- Against a total table, `agreesWith` is `recheck` evaluated at the tabulated function. -/
theorem agreesWith_ofFn_some (H : (t : spec.Domain) → spec.Range t) (log : QueryLog spec) :
    agreesWith (QueryCache.ofFn fun t ↦ some (H t)) log =
      evalWithAnswerFn (QueryImpl.ofFn H) (recheck log) := by
  simp [agreesWith, evalWithAnswerFn_recheck]

/-- Removing duplicate entries does not change the acceptance of `recheck` against any fixed
function. -/
theorem evalWithAnswerFn_recheck_dedup [DecidableEq ι] (H : (t : spec.Domain) → spec.Range t)
    (log : QueryLog spec) :
    evalWithAnswerFn (QueryImpl.ofFn H) (recheck log.dedup) =
      evalWithAnswerFn (QueryImpl.ofFn H) (recheck log) := by
  rw [← agreesWith_ofFn_some, ← agreesWith_ofFn_some, agreesWith_dedup]

end recheck

end OracleSpec.QueryLog
