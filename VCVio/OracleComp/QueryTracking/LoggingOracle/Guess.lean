/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.Constructions.SampleableType.GuessIndex

/-!
# Guessing a logged query

A computation making at most `q` queries logs at most `q` of them
(`OracleComp.log_length_le_of_mem_support_run_simulateQ`), so the index guess of
`prEvent_exists_mem_le_mul_prEvent_getD_of_evalDistEq` applies to its query log: the probability
that some logged query satisfies `S` is at most `q` times the probability that the query at an
index guessed uniformly from `Fin (max q 1)` satisfies `S`
(`OracleComp.prEvent_exists_mem_withQueryLog_le_mul_prEvent_getD`). This is the step of a
reduction that guesses which oracle query is the bad one and answers it differently.
-/

public section

open OracleSpec

namespace OracleComp

/-- **Guessing a logged query.** If `oa` makes at most `q` queries and `mi` is distributed as a
uniform index of `Fin (max q 1)`, the probability that some query in the log of `oa` satisfies
`S` is at most `q` times the probability that the logged query at the index drawn by `mi`
satisfies `S`, the default `d` standing in past the end of the log. -/
theorem prEvent_exists_mem_withQueryLog_le_mul_prEvent_getD {ι : Type} {spec : OracleSpec ι}
    [AnswerMeasure spec] {α : Type} {q : ℕ} (oa : OracleComp spec α)
    (hq : IsTotalQueryBound oa q) (mi : OracleComp spec (Fin (max q 1)))
    (hmi : mi =ᵈ ($ᵗ Fin (max q 1) : ProbComp (Fin (max q 1))))
    (S : ((t : ι) × spec.Range t) → Prop) (d : (t : ι) × spec.Range t) :
    Pr{let z ← oa.withQueryLog}[∃ e ∈ z.2, S e] ≤
      q * Pr{let z ← oa.withQueryLog; let i ← mi}[S (z.2.getD i d)] := by
  have h := prEvent_exists_mem_le_mul_prEvent_getD_of_evalDistEq (Prod.snd <$> oa.withQueryLog)
    (fun l hl ↦ by
      rw [support_map] at hl
      obtain ⟨z, hz, rfl⟩ := hl
      exact log_length_le_of_mem_support_run_simulateQ hq hz) mi hmi S d
  simpa only [Functor.map_map, bind_map_left] using h

end OracleComp
