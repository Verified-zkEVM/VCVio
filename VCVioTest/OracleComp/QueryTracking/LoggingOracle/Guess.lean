/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Guess
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Checks for guessing a logged query

`OracleComp.prEvent_exists_mem_withQueryLog_le_mul_prEvent_getD` at two coin flips, at a
computation without queries, where it forces the event to have probability `0`, and without its
query bound, where it fails.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace VCVioTest.GuessLoggedQuery

/-- One coin flip. -/
def coin : ProbComp (Fin 2) := unifSpec.query 1

/-- Two coin flips, guessed at with a uniform index of `Fin 2`. -/
example (S : ((t : ℕ) × unifSpec.Range t) → Prop) (d : (t : ℕ) × unifSpec.Range t) :
    Pr{let z ← (coin >>= fun _ => coin).withQueryLog}[∃ e ∈ z.2, S e] ≤
      (2 : ℕ) * Pr{let z ← (coin >>= fun _ => coin).withQueryLog; let i ← $ᵗ Fin (max 2 1)}[
        S (z.2.getD i d)] :=
  prEvent_exists_mem_withQueryLog_le_mul_prEvent_getD _
    (by
      rw [coin, isTotalQueryBound_query_bind_iff]
      refine ⟨by decide, fun _ => ?_⟩
      rw [← bind_pure (liftM (OracleSpec.query 1)), isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => trivial⟩) _ EvalDistEq.rfl S d

/-- A computation that makes no query has no logged query satisfying anything. -/
example (S : ((t : ℕ) × unifSpec.Range t) → Prop) (d : (t : ℕ) × unifSpec.Range t) :
    Pr{let z ← (pure 0 : ProbComp ℕ).withQueryLog}[∃ e ∈ z.2, S e] = 0 :=
  nonpos_iff_eq_zero.1 <| (prEvent_exists_mem_withQueryLog_le_mul_prEvent_getD (q := 0)
    (pure 0 : ProbComp ℕ) trivial _ EvalDistEq.rfl S d).trans_eq (by simp)

/-- The query bound is needed: one coin flip logs a query, so with `q = 0` the bound would be
`1 ≤ 0`. -/
example : ¬ Pr{let z ← coin.withQueryLog}[∃ e ∈ z.2, e.1 = 1] ≤
    (0 : ℕ) * Pr{let z ← coin.withQueryLog; let i ← $ᵗ Fin (max 0 1)}[
      (z.2.getD i ⟨1, (0 : Fin 2)⟩).1 = 1] := by
  simp [coin, withQueryLog_query]

end VCVioTest.GuessLoggedQuery
