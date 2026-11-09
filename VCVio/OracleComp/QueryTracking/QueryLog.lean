/-
Copyright (c) 2024 ArkLib Contributors,
  2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.OracleComp.Coercions.SubSpec.Routing
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Lookup in query logs and logs of routed sum interfaces

- `QueryLog.lookup?` — first-match lookup of a query's logged answer, the occurrence `0` of
  `QueryLog.getQueryValue?`, with `cons`/`append` evaluation lemmas.
- Logs of the slot-routing handlers `swapRight`, `insertMiddle` and `mergeRight`, and of
  computations lifted into either summand.
-/

public section

universe u

namespace OracleSpec

namespace QueryLog

section lookup

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq ι]

/-- First-match lookup of the answer to a query `t` in a query log, if any: the occurrence `0`
of `getQueryValue?`.

Note that a log may answer the same query several times (e.g. when it records a randomness
oracle rather than a function); `lookup?` returns the *earliest* entry. When the log is
function-like (at most one entry per query, as for the canonical transcript-derivation log),
this is the unique answer. -/
@[expose] def lookup? (log : QueryLog spec) (t : spec.Domain) : Option (spec.Range t) :=
  log.getQueryValue? t 0

lemma lookup?_eq_getQueryValue? (log : QueryLog spec) (t : spec.Domain) :
    log.lookup? t = log.getQueryValue? t 0 := rfl

@[simp]
lemma lookup?_nil (t : spec.Domain) : lookup? ([] : QueryLog spec) t = none := by
  simp [lookup?, getQueryValue?]

lemma lookup?_cons (t' : spec.Domain) (u : spec.Range t') (rest : QueryLog spec)
    (t : spec.Domain) :
    lookup? (⟨t', u⟩ :: rest) t
      = if ht : t' = t then some (ht ▸ u) else lookup? rest t := by
  by_cases ht : t' = t <;> simp [lookup?, getQueryValue?, ht]

/-- `lookup?` scans left-to-right through an append: the second log answers only the
queries the first leaves unanswered. -/
lemma lookup?_append (l₁ l₂ : QueryLog spec) (t : spec.Domain) :
    lookup? (l₁ ++ l₂) t
      = ((lookup? l₁ t).rec (lookup? l₂ t) (fun u => some u) : Option (spec.Range t)) := by
  induction l₁ with
  | nil => rfl
  | cons e rest ihe =>
    obtain ⟨t', u⟩ := e
    rw [show (⟨t', u⟩ :: rest) ++ l₂ = ⟨t', u⟩ :: (rest ++ l₂) from rfl,
      lookup?_cons, lookup?_cons]
    by_cases ht : t' = t
    · rw [dite_eq_left ht, dite_eq_left ht]
    · rw [dite_eq_right ht, dite_eq_right ht, ihe]

end lookup

end QueryLog

end OracleSpec

/-! ## Routing and projecting sum-interface logs -/

namespace OracleSpec.QueryLog

variable {ι κ ν : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}

/-- Exchange the last two oracle slots in a logged query-answer pair. -/
@[expose] def swapRightEntry : Sigma ((a + b) + c) → Sigma ((a + c) + b)
  | ⟨.inl (.inl q), r⟩ => ⟨.inl (.inl q), r⟩
  | ⟨.inl (.inr q), r⟩ => ⟨.inr q, r⟩
  | ⟨.inr q, r⟩ => ⟨.inl (.inr q), r⟩

/-- Relabel a logged query-answer pair of two oracle slots for the interface with a middle slot
inserted. -/
@[expose] def insertMiddleEntry : Sigma (a + b) → Sigma ((a + c) + b)
  | ⟨.inl q, r⟩ => ⟨.inl (.inl q), r⟩
  | ⟨.inr q, r⟩ => ⟨.inr q, r⟩

/-- Relabel a log of two oracle slots for the interface with a middle slot inserted. The middle
slot stays unused. -/
@[expose] def insertMiddle (log : QueryLog (a + b)) : QueryLog ((a + c) + b) :=
  log.map insertMiddleEntry

/-- Relabel a log by exchanging its last two oracle slots. -/
@[expose] def swapRight (log : QueryLog ((a + b) + c)) : QueryLog ((a + c) + b) :=
  log.map swapRightEntry

/-- Remove the middle oracle slot, preserving all other entries and their order. -/
@[expose] def eraseMiddle (log : QueryLog ((a + c) + b)) : QueryLog (a + b) :=
  log.swapRight.fst

/-- Deleting the moved private slot leaves precisely the original public log. -/
@[simp] theorem eraseMiddle_swapRight (log : QueryLog ((a + b) + c)) :
    log.swapRight.eraseMiddle = log.fst := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    rcases e with ⟨(q | q) | q, r⟩ <;>
      simp only [eraseMiddle, swapRight, swapRightEntry,
        QueryLog.fst, List.map_cons, List.filterMap_cons] at *
    all_goals first | exact ih | exact congrArg (List.cons _) ih

/-- Deleting a middle slot does not change the final oracle's log. -/
@[simp] theorem snd_eraseMiddle (log : QueryLog ((a + c) + b)) :
    log.eraseMiddle.snd = log.snd := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    rcases e with ⟨(q | q) | q, r⟩ <;>
      simp only [eraseMiddle, swapRight, swapRightEntry,
        QueryLog.fst, QueryLog.snd, List.map_cons, List.filterMap_cons] at *
    all_goals first | exact ih | exact congrArg (List.cons _) ih

/-- The first log after deleting the middle slot is the original first-slot log. -/
@[simp] theorem fst_eraseMiddle (log : QueryLog ((a + c) + b)) :
    log.eraseMiddle.fst = log.fst.fst := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    rcases e with ⟨(q | q) | q, r⟩ <;>
      simp only [eraseMiddle, swapRight, swapRightEntry,
        QueryLog.fst, List.map_cons, List.filterMap_cons] at *
    all_goals first | exact ih | exact congrArg (List.cons _) ih

end OracleSpec.QueryLog

namespace OracleComp

open OracleSpec

variable {ι κ ν α : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}

/-- Logging commutes with this relabeling of oracle slots. -/
theorem withQueryLog_swapRight (p : OracleComp ((a + b) + c) α) :
    p.swapRight.withQueryLog = (fun z => (z.1, z.2.swapRight)) <$> p.withQueryLog.swapRight := by
  apply withQueryLog_simulateQ_of_query QueryImpl.swapRight QueryLog.swapRightEntry
  intro q
  rcases q with (q | q) | q <;>
    simp [QueryImpl.swapRight, QueryLog.swapRightEntry, withQueryLog_query]

/-- Embedding a logged computation preserves its log, with the corresponding query labels. -/
theorem withQueryLog_insertMiddle (p : OracleComp (a + b) α) :
    (p.insertMiddle (c := c)).withQueryLog =
      (fun z => (z.1, z.2.insertMiddle)) <$> p.withQueryLog.insertMiddle := by
  apply withQueryLog_simulateQ_of_query QueryImpl.insertMiddle QueryLog.insertMiddleEntry
  intro q
  cases q <;> simp [QueryImpl.insertMiddle, QueryLog.insertMiddleEntry, withQueryLog_query]

/-- Projecting away both merged slots preserves the retained query log. -/
theorem fst_withQueryLog_mergeRight
    (p : OracleComp (((a + c) + b) + c) α) :
    (fun z => (z.1, z.2.fst)) <$> p.mergeRight.withQueryLog =
      ((fun z => (z.1, z.2.fst.eraseMiddle)) <$> p.withQueryLog).mergeRight := by
  apply withQueryLog_simulateQ_project QueryImpl.mergeRight
    (fun tr => tr.fst.eraseMiddle) QueryLog.fst rfl rfl
    (by intros; simp [QueryLog.eraseMiddle, QueryLog.swapRight]) QueryLog.fst_append
  intro q
  rcases q with ((q | q) | q) | q <;>
    simp [QueryImpl.mergeRight, withQueryLog_query, QueryLog.eraseMiddle,
      QueryLog.swapRight, QueryLog.swapRightEntry, QueryLog.fst]

end OracleComp

namespace OracleComp

open OracleSpec

/-- Logging a lift to the left-hand oracle records the same answers with left-tagged queries. -/
theorem withQueryLog_liftComp_left {ι κ α : Type} {a : OracleSpec ι} {b : OracleSpec κ}
    (p : OracleComp a α) :
    (liftComp p (a + b)).withQueryLog =
      (fun z => (z.1, QueryLog.inl z.2)) <$> liftComp p.withQueryLog (a + b) := by
  simpa only [withQueryLog, loggingOracle, QueryImpl.ofLift_eq_id',
    map_eq_bind_pure_comp, Function.comp_def] using
    withQueryLog_liftComp_left_of_query (oSpec := a) (spec₂ := b) (fun _ => rfl) p

/-- A computation using only the right-hand oracle leaves the left-hand log empty. -/
theorem fst_withQueryLog_liftComp_right {ι κ α : Type}
    {publicSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    (p : OracleComp privateSpec α) :
    (fun r => (r.1, r.2.fst)) <$> (liftComp p (publicSpec + privateSpec)).withQueryLog =
      (fun x => (x, ([] : QueryLog publicSpec))) <$> liftComp p (publicSpec + privateSpec) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [QueryLog.fst]
  | query_bind q next ih =>
    rw [liftComp_bind]
    change (fun r => (r.1, r.2.fst)) <$>
      ((liftM ((publicSpec + privateSpec).query (.inr q)) >>=
        fun u => liftComp (next u) (publicSpec + privateSpec))).withQueryLog = _
    rw [withQueryLog_bind]
    simp only [withQueryLog_query, bind_assoc, map_bind, pure_bind]
    refine bind_congr fun u => ?_
    simpa [QueryLog.fst] using ih u

end OracleComp
