/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.ReplayEq

/-!
# Erasing a warm query and retaining a cold query

The cold control uses a deterministic sampler that always returns the candidate value.
The final cache distinguishes the two programs even in that case.
-/

public section

open OracleComp OracleSpec OracleSpec.QueryCache

namespace VCVioTest.CacheReplay

/-- A single address suffices to observe whether a query populated the cache. -/
abbrev Spec := Unit →ₒ Bool

/-- A known answer selects the same continuation from every extension of the cache. -/
theorem warm {cache : QueryCache Spec} (warm : cache () = some true)
    (next : Bool → OracleComp Spec Nat) :
    ReplayEq cache (Spec.query () >>= next) (next true) := by
  apply ReplayEq.bind_known _ _ _ (.refl _ _)
  simpa only [Resolves, simulateQ_spec_query, toPartialImpl_apply] using warm

/-- A cold query changes the joint result even when the fresh answer is deterministic. -/
theorem cold : ¬ ReplayEq (∅ : QueryCache Spec) (Spec.query ()) (pure true) := by
  intro shared
  let constant : QueryImpl Spec ProbComp := fun _ => pure true
  have equal := (shared constant ∅ le_rfl).prEvent_eq (fun z => z.2 () = some true)
  rw [simulateQ_spec_query, QueryImpl.withCaching_run_none constant (by rfl),
    simulateQ_pure, StateT.run_pure] at equal
  simp [constant, prEvent_norm] at equal

end VCVioTest.CacheReplay
