/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# An invariant of a logged run that needs the allowed-query restriction

The ambient oracle has two queries: `false` leaves a counter unchanged and `true` increments it.
The logged inner handler answers each of its queries with one `true` query. The invariant "the
counter is its initial value plus the length of the log" is preserved by the logged handler and by
the ambient `false` query, so `QueryImpl.inv_of_mem_support_run_add_withLogging` gives it at the
end of every run of a program that makes only ambient `false` queries. A program making the
ambient `true` query ends with the counter one above the length of its empty log, so the
restriction to allowed ambient queries cannot be dropped.
-/

public section

namespace VCVioTest.LoggedRunInvariant

open OracleComp OracleSpec

/-- Two ambient queries with no answer. -/
abbrev ambSpec : OracleSpec Bool := fun _ ↦ Unit

/-- The logged oracle: one query with no answer. -/
abbrev logSpec : OracleSpec Unit := Unit →ₒ Unit

/-- The ambient query `true` increments the counter; `false` leaves it unchanged. -/
def counter : QueryImpl ambSpec (StateT ℕ ProbComp) :=
  fun t ↦ StateT.mk fun n ↦ pure ((), if t then n + 1 else n)

/-- The logged handler answers by the ambient query `true`. -/
def inner : QueryImpl logSpec (OracleComp ambSpec) := fun _ ↦ ambSpec.query true

/-- The run of a program through the logged handler under the counter. -/
def loggedRun {α : Type} (oa : OracleComp (ambSpec + logSpec) α) (n : ℕ) :
    ProbComp ((α × QueryLog logSpec) × ℕ) :=
  (simulateQ counter ((simulateQ
    ((HasQuery.toQueryImpl (spec := ambSpec) (m := OracleComp ambSpec)).liftTarget
      (WriterT (QueryLog logSpec) (OracleComp ambSpec)) + inner.withLogging) oa).run)).run n

/-- A program making only ambient `false` queries ends with the counter at its initial value
plus the length of the log. -/
theorem eq_add_length_of_mem_support_loggedRun {α : Type} {oa : OracleComp (ambSpec + logSpec) α}
    (hoa : AllQueriesSatisfy oa (Sum.elim (· = false) fun _ ↦ True)) {n₀ : ℕ}
    {z : (α × QueryLog logSpec) × ℕ} (hz : z ∈ support (loggedRun oa n₀)) :
    z.2 = n₀ + z.1.2.length := by
  simpa using QueryImpl.inv_of_mem_support_run_add_withLogging counter inner
    (fun log n ↦ n = n₀ + log.length)
    (fun t ht log n hn w hw ↦ by
      subst ht
      simp only [counter, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      simpa using hn)
    (fun t log n hn w hw ↦ by
      simp only [inner, simulateQ_spec_query, counter, StateT.run_mk, support_pure,
        Set.mem_singleton_iff, ↓reduceIte] at hw
      subst hw
      simp [hn, Nat.add_assoc])
    hoa (log₀ := []) (s₀ := n₀) (by simp) hz

/-- A program making the ambient `true` query ends with the counter one above its empty log. -/
example : (((), []), 1) ∈
    support (loggedRun (ambSpec + logSpec |>.query (.inl true)) 0) := by
  simp [loggedRun, counter]

/-- The program of the previous example breaks the invariant. -/
example : ¬ ∀ z ∈ support (loggedRun (ambSpec + logSpec |>.query (.inl true)) 0),
    z.2 = 0 + z.1.2.length := by
  intro h
  simpa using h (((), []), 1) (by simp [loggedRun, counter])

end VCVioTest.LoggedRunInvariant
