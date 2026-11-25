/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
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

namespace VCVioTest.ModuleAPI.Cache

/-! ## Settled computations frame the full cache and sampler state -/

/-- Two response coordinates make discarding part of a cached answer observable. -/
private abbrev fullSpec : OracleSpec Nat := Nat →ₒ (Nat × Nat)

/-- A miss returns the old counter in both coordinates, then advances it once. -/
private def missCounter : QueryImpl fullSpec (StateT Nat Id) :=
  fun _ => StateT.mk fun n => pure ((n, n + 100), n + 1)

/-- Two physical requests for one key retain both complete replies. -/
private def repeated : OracleComp fullSpec ((Nat × Nat) × (Nat × Nat)) := do
  let x ← query (spec := fullSpec) 0
  let y ← query (spec := fullSpec) 0
  pure (x, y)

/-- The settled key fixes both response coordinates. -/
private def known : QueryCache fullSpec := (∅ : QueryCache fullSpec).cacheQuery 0 (7, 70)

/-- The live cache also contains a row the computation never reads. -/
private def live : QueryCache fullSpec := known.cacheQuery 99 (9, 90)

/-- Repeated warm requests settle under the smaller known cache. -/
private theorem repeated_settled :
    simulateQ known.toPartialImpl repeated = some ((7, 70), (7, 70)) := by
  simp [repeated, known, QueryCache.toPartialImpl_apply]

/-- A cache extension retains the known complete response. -/
private theorem known_le_live : known ≤ live := by
  exact QueryCache.le_cacheQuery (cache := known) (t := 99) (u := (9, 90)) (by
    simp [known])

/-- Settlement in a smaller cache preserves the entire larger cache and the miss counter. -/
private theorem warm_joint_frame :
    ((simulateQ missCounter.withCaching repeated).run live).run 5 =
      pure ((((7, 70), (7, 70)), live), 5) := by
  have h := QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl
    missCounter repeated (QueryCache.simulateQ_toPartialImpl_mono known_le_live repeated
      repeated_settled)
  exact congrArg (fun f => f.run 5) h

/-- The unrelated live row, including its second coordinate, survives both warm requests. -/
private theorem unrelated_row_retained :
    (((simulateQ missCounter.withCaching repeated).run live).run 5).run.1.2 99 =
      some (9, 90) := by
  rw [warm_joint_frame]
  simp [live]

/-- Without the settled row the partial oracle cannot replay the requests. -/
private theorem missing_settlement :
    simulateQ (∅ : QueryCache fullSpec).toPartialImpl repeated = none := by
  simp [repeated, QueryCache.toPartialImpl_apply]

/-- A cold repeated request samples once and reuses the complete sampled response. -/
private theorem cold_repeated_response :
    (((simulateQ missCounter.withCaching repeated).run ∅).run 5).run.1.1 =
      ((5, 105), (5, 105)) := by
  simp [repeated, missCounter, QueryImpl.withCaching_apply]

/-- The missing-settlement case really changes sampler state, so a warm frame is unavailable. -/
private theorem cold_counter_advanced :
    (((simulateQ missCounter.withCaching repeated).run ∅).run 5).run.2 = 6 := by
  simp [repeated, missCounter, QueryImpl.withCaching_apply]

/-- The general frame law needs no decidable equality on function-valued query indices. -/
example {spec : OracleSpec (Nat → Nat)} {m : Type → Type} [Monad m] [LawfulMonad m]
    {σ α : Type} (impl : QueryImpl spec (StateT σ m)) (cache : spec.QueryCache) (s : σ)
    (oa : OracleComp spec α) (a : α)
    (hframe : ∀ t answer, cache t = some answer → (impl t).run s = pure (answer, s))
    (ha : simulateQ cache.toPartialImpl oa = some a) :
    (simulateQ impl oa).run s = pure (a, s) :=
  QueryImpl.run_simulateQ_eq_pure_of_toPartialImpl_frame impl cache s oa hframe ha

end VCVioTest.ModuleAPI.Cache
