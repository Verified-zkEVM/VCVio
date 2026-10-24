/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T2.Caching

/-!
# Tests for the caching handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T2.Caching`: repeated queries agree,
an exact final cache, the monotone frame of an opaque simulated program, and support facts.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T2Caching

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

set_option experimental.vcgen true

universe u

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- Two queries at the same input agree, at any universe. -/
example (t : spec.Domain) :
    ⦃ fun _ => True ⦄
      (do let a ← spec.cachingOracle t; let b ← spec.cachingOracle t; return (a, b) :
        StateT spec.QueryCache (OracleComp spec) _)
    ⦃ fun p _ => p.1 = p.2 ⦄ := by
  vcgen
  grind

/-- A stored answer is returned and survives later queries. -/
example (t t' : spec.Domain) (u : spec.Range t) :
    ⦃ fun c => c t = some u ⦄
      (do let _ ← spec.cachingOracle t'; spec.cachingOracle t :
        StateT spec.QueryCache (OracleComp spec) _)
    ⦃ fun v c => v = u ∧ c t = some u ⦄ := by
  vcgen
  grind

/-- The exact rule computes the final cache of two queries at the same input. -/
example (t : spec.Domain) (c₀ : spec.QueryCache) :
    ⦃ fun c => c = c₀ ⦄
      (do let a ← spec.cachingOracle t; let b ← spec.cachingOracle t; return (a, b) :
        StateT spec.QueryCache (OracleComp spec) _)
    ⦃ fun p c => p.1 = p.2 ∧ c = c₀.cacheQuery t p.1 ⦄ := by
  vcgen [cachingOracle_wp_cacheQuery]
  grind

/-- For any program, every final cache of a caching run extends the initial one. -/
example {α : Type u} (oa : OracleComp spec α) (c : spec.QueryCache) :
    ∀ z ∈ support ((simulateQ spec.cachingOracle oa).run c), c ≤ z.2 :=
  QueryImpl.simulateQ_withCaching_cache_le _ oa c

/-- The same frame by `vcgen`, read back against the support. -/
example {α : Type u} (oa : OracleComp spec α) (c₀ : spec.QueryCache) :
    ⦃ fun c => c₀ ≤ c ∧ True ⦄
      (simulateQ spec.cachingOracle oa : StateT spec.QueryCache (OracleComp spec) α)
    ⦃ fun _ c => c₀ ≤ c ⦄ := by
  vcgen
  grind

/-- An opaque caching run followed by a query: an upward-closed invariant survives, and the
answer is cached. -/
example {α : Type u} (oa : OracleComp spec α) (t : spec.Domain)
    (P : spec.QueryCache → Prop) (hP : ∀ c c', c ≤ c' → P c → P c') :
    ⦃ fun c => P c ∧ True ⦄
      (do let _ ← simulateQ spec.cachingOracle oa; spec.cachingOracle t :
        StateT spec.QueryCache (OracleComp spec) _)
    ⦃ fun v c => P c ∧ c t = some v ⦄ := by
  vcgen
  grind

/-- Support destructuring of one query: a fresh query caches its answer. -/
example (t : spec.Domain) (c c' : spec.QueryCache) (v : spec.Range t) (h : c t = none)
    (hz : (v, c') ∈ support ((spec.cachingOracle t).run c)) : c' = c.cacheQuery t v := by
  rcases cachingOracle.mem_support_run_iff.1 hz with ⟨hc, -⟩ | ⟨-, rfl⟩
  · simp [h] at hc
  · rfl

/-- `simulateQ_nf` runs a simulated query and splits its support into a hit and a miss. -/
example (t : spec.Domain) (c c' : spec.QueryCache) (v : spec.Range t)
    (hz : (v, c') ∈
      support ((simulateQ spec.cachingOracle (spec.query t : OracleComp spec _)).run c)) :
    c' = c.cacheQuery t v := by
  simp only [simulateQ_nf] at hz
  rcases hz with ⟨hc, rfl⟩ | ⟨-, rfl⟩
  · exact (QueryCache.cacheQuery_eq_self_of_eq_some hc).symm
  · rfl

/-- A generic caching handler over `OracleComp`: the frame rule applies to any `so`. -/
example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} (so : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) :
    ⦃ fun _ => True ⦄
      (do let a ← so.withCaching t; let b ← so.withCaching t; return (a, b) :
        StateT spec.QueryCache (OracleComp spec') _)
    ⦃ fun p _ => p.1 = p.2 ⦄ := by
  vcgen
  grind

end VCVioTest.ProgramLogic.Library.T2Caching
