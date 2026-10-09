/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import Mathlib.Data.Option.Basic

/-!
# Cache observations and instance isolation

Ordinary optional functions keep their pointwise order. Cache extension requires exact
agreement on recorded answers, including for different response types at different indices.
The caching handler must reuse a hit without running the underlying stateful handler again.
-/

public section

open OracleSpec OracleComp

namespace VCVioTest.ModuleAPI.Cache

example : (fun _ : Bool => some (0 : Nat)) ≤ (fun _ => some 1) := by
  intro _
  exact Option.some_le_some.mpr (by decide)

/-- A cache with genuinely different answer fibers. -/
abbrev signature : OracleSpec Bool
  | false => Bool
  | true => Nat

example : ((∅ : QueryCache signature).cacheQuery false true) false = some true := by simp

example : ((∅ : QueryCache signature).cacheQuery false true) true = none := by simp

example :
    (((∅ : QueryCache signature).cacheQuery false true).cacheQuery true 7) false = some true := by
  simp

example :
    (((∅ : QueryCache signature).cacheQuery true 7).cacheQuery true 9) true = some 9 := by
  simp

example : ¬ ((∅ : QueryCache signature).cacheQuery true 7 ≤
    (∅ : QueryCache signature).cacheQuery true 9) := by
  intro h
  have := (QueryCache.le_def.mp h) (QueryCache.cacheQuery_self _ true 7)
  simp at this

universe u v

example {ι : Type u} {spec : OracleSpec.{u, v} ι} (cache : QueryCache spec) :
    QueryCache.ofFn cache.toFn = cache := by simp

example {ι : Type u} {spec : OracleSpec.{u, v} ι}
    (f : (t : spec.Domain) → Option (spec.Range t)) : (QueryCache.ofFn f).toFn = f := by simp

/-- A handler returning its call counter before incrementing it. -/
def fresh : QueryImpl (Unit →ₒ Nat) (StateT Nat Id) :=
  fun _ => StateT.mk fun n => pure (n, n + 1)

/-- Asking for the same cached query twice. -/
def twice : OracleComp (Unit →ₒ Nat) (Nat × Nat) := do
  let x ← query (spec := Unit →ₒ Nat) ()
  let y ← query (spec := Unit →ₒ Nat) ()
  pure (x, y)

example :
    (((simulateQ fresh.withCaching twice).run ∅).run 5).run.1.1 = (5, 5) := by
  simp [twice, QueryImpl.withCaching_apply, fresh]

example : (((simulateQ fresh.withCaching twice).run ∅).run 5).run.2 = 6 := by
  simp [twice, QueryImpl.withCaching_apply, fresh]

end VCVioTest.ModuleAPI.Cache
