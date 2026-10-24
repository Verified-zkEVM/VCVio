/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T2.CachingLogging
public import VCVio.ProgramLogic.Library.T2.Programming

/-!
# Tests for the caching-and-logging and programming specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T2.CachingLogging` and
`VCVio.ProgramLogic.Library.T2.Programming`: consistent repeated answers with an exact log,
cache-log coherence of whole runs, frames of opaque runs, and programmed answers.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T2CachingLogging

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}

/-- Two queries at the same input agree, and both are logged. -/
example (t : spec.Domain) :
    ⦃ fun s => s.2 = [] ⦄
      (do let a ← spec.cachingLoggingOracle t; let b ← spec.cachingLoggingOracle t; return (a, b))
    ⦃ fun p s => p.1 = p.2 ∧ s.2 = [⟨t, p.1⟩, ⟨t, p.2⟩] ∧ s.1 t = some p.1 ⦄ := by
  vcgen
  grind

/-- An opaque run followed by a query keeps every earlier cache entry and log prefix. -/
example {α : Type} (oa : OracleComp spec α) (t t' : spec.Domain) (u : spec.Range t')
    (log₀ : QueryLog spec) :
    ⦃ fun s => s.1 t' = some u ∧ s.2 = log₀ ⦄
      (do let _ ← simulateQ spec.cachingLoggingOracle oa; spec.cachingLoggingOracle t)
    ⦃ fun v s => s.1 t' = some u ∧ log₀ <+: s.2 ∧ s.2.getLast? = some ⟨t, v⟩ ⦄ := by
  vcgen
  simp_all
  exact ⟨by grind, (‹_ ∧ log₀ <+: _›).2.trans (List.prefix_append _ _)⟩

/-- From the empty state, every logged answer of a run is the cached one. -/
example {α : Type} (oa : OracleComp spec α) {z : α × spec.QueryCache × QueryLog spec}
    (hz : z ∈ support ((simulateQ spec.cachingLoggingOracle oa).run (∅, []))) :
    ∀ e ∈ z.2.2, z.2.1 e.1 = some e.2 :=
  (cachingLoggingOracle.log_cached_and_cache_logged_of_mem_support hz).1

/-- A programmed fresh point is answered by the policy and raises the flag; an unprogrammed one
keeps the flag. -/
example (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (t t' : spec.Domain) (u : spec.Range t) (hp : policy t = some u) (hp' : policy t' = none) :
    ⦃ fun s => s.1 t = none ∧ s.1 t' = none ∧ s.2 = false ⦄
      (do let _ ← so.withProgramming policy t'; so.withProgramming policy t)
    ⦃ fun v s => v = u ∧ s.2 = true ∧ s.1 t = some u ⦄ := by
  have hne : t ≠ t' := by rintro rfl; simp_all
  vcgen
  simp_all

/-- An opaque programmed run never lowers the flag and only grows the cache. -/
example {α : Type} (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (c₀ : spec.QueryCache) :
    ⦃ fun s => c₀ ≤ s.1 ∧ s.2 = true ⦄ (simulateQ (so.withProgramming policy) oa)
      ⦃ fun _ s => c₀ ≤ s.1 ∧ s.2 = true ⦄ := by
  vcgen
  grind

end VCVioTest.ProgramLogic.Library.T2CachingLogging
