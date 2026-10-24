/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.SimulateQ
public import VCVio.ProgramLogic.Library.T2.Caching
public import VCVio.ProgramLogic.Library.T2.Logging

/-!
# Tests for the logging handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T2.Logging`: exact logs of query
sequences, the frame of an opaque logged program, query bounds read off the log, and logging over
a caching handler.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T2Logging

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary WriterT.AppendWP

set_option experimental.vcgen true

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Two logged queries append both entries, in order. -/
example (t₁ t₂ : spec.Domain) (log₀ : QueryLog spec) :
    ⦃ fun log => log = log₀ ⦄
      (do let a ← spec.loggingOracle t₁; let b ← spec.loggingOracle t₂; return (a, b) :
        WriterT (QueryLog spec) (OracleComp spec) _)
    ⦃ fun p log => log = log₀ ++ [⟨t₁, p.1⟩, ⟨t₂, p.2⟩] ⦄ := by
  vcgen
  simp_all

/-- A simulated program is logged through the structural `simulateQ` rules. -/
example (t : spec.Domain) :
    ⦃ fun log => log = [] ⦄
      (simulateQ spec.loggingOracle (spec.query t : OracleComp spec _))
    ⦃ fun v log => log = [⟨t, v⟩] ⦄ := by
  vcgen
  simp_all

/-- For any program, a logged run returns a possible result of the program. -/
example {α : Type} (oa : OracleComp spec α) (S : Set α) (hS : ∀ a ∈ support oa, a ∈ S) :
    ⦃ fun _ => True ⦄ (simulateQ spec.loggingOracle oa) ⦃ fun a _ => a ∈ S ⦄ := by
  vcgen
  grind

/-- An opaque program with a budget of `n` queries in `P`, then one more query in `P`: the log
holds at most `n + 1` entries in `P`, and its last entry is the final query. -/
example {α : Type} (P : ι → Prop) [DecidablePred P] (n : ℕ) (oa : OracleComp spec α)
    (h : IsQueryBoundP oa P n) (t : spec.Domain) (ht : P t) :
    ⦃ fun log => log = [] ⦄
      (do let _ ← simulateQ spec.loggingOracle oa; spec.loggingOracle t :
        WriterT (QueryLog spec) (OracleComp spec) _)
    ⦃ fun v (log : QueryLog spec) => log.countQ P ≤ n + 1 ∧ log.getLast? = some ⟨t, v⟩ ⦄ := by
  vcgen [simulateQ_loggingOracle_wp_of_isQueryBoundP h]
  simp_all

/-- A total query bound bounds the length of every reachable log. -/
example {α : Type} {oa : OracleComp spec α} {n : ℕ} (h : IsQueryBoundP oa (fun _ => True) n)
    {z : α × QueryLog spec} (hz : z ∈ support (simulateQ spec.loggingOracle oa).run) :
    z.2.length ≤ n := by
  simpa [QueryLog.countQ, QueryLog.getQ] using countQ_le_of_mem_support_run_simulateQ h hz

variable [DecidableEq ι]

/-- Logging a caching handler: the log records the query and the cache stores the answer. -/
example (t : spec.Domain) :
    ⦃ fun log _ => log = [] ⦄
      (spec.cachingOracle.withLogging t :
        WriterT (QueryLog spec) (StateT spec.QueryCache (OracleComp spec)) _)
    ⦃ fun v log c => log = [⟨t, v⟩] ∧ c t = some v ⦄ := by
  vcgen
  simp_all

end VCVioTest.ProgramLogic.Library.T2Logging
