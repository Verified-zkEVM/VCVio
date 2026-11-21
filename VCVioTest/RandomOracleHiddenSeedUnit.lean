/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed.Unit

/-!
# Retained private reads with full caches and ordinary failure data

Two private reads become two literal tick queries.
Ordinary private uniform draws keep distinct primitive occurrences.
The state projection keeps every original public entry and the warm original private word.
-/

public section

open OracleComp OracleSpec SecretEncoding

namespace HiddenSeedUnitToy

/-- Ordinary public calls return one bit at an arbitrary natural input. -/
abbrev Pub := Nat →ₒ Bool
/-- The original program has fresh uniforms, ordinary public calls, and one private cell. -/
abbrev Source := Pub.withDerivations Unit Bool
/-- The paid target retains uniforms and adds the independent Unit-returning tick oracle. -/
abbrev Target := unifSpec + (Pub + UnitTick)

/-- A private read keeps a literal paid query on every occurrence. -/
theorem two_reads_are_two_ticks (word : Bool) :
    simulateQ (paidInlineUnitDerivations Pub word)
      (do
        let first ← liftM (Source.query (.inr ()))
        let second ← liftM (Source.query (.inr ()))
        pure (first, second)) =
      (do
        let _ ← liftM (Target.query (.inr (.inr ())))
        let _ ← liftM (Target.query (.inr (.inr ())))
        pure (word, word) : OracleComp Target (Bool × Bool)) := by
  simp [simulateQ_bind, paidInlineUnitDerivations_derive, bind_map_left]

/-- Repeated ordinary uniforms remain two fresh primitive queries. -/
theorem two_uniforms_stay_fresh (word : Bool) :
    simulateQ (paidInlineUnitDerivations Pub word)
      (do
        let first ← liftM (Source.query (.inl (.inl 1)))
        let second ← liftM (Source.query (.inl (.inl 1)))
        pure (first, second)) =
      (do
        let first ← liftM (Target.query (.inl 1))
        let second ← liftM (Target.query (.inl 1))
        pure (first, second) : OracleComp Target (Fin 2 × Fin 2)) := by
  simp

/-- An unreached head leaves the original private table empty. -/
theorem unreached_private_cell (raw : Pub.QueryCache) :
    (simulateQ (idealImpl Pub Unit Bool) (pure (none : Option Bool))).run (raw, ∅) =
      pure (none, (raw, ∅)) := by
  simp

/-- A warm cell differs from that empty state for either full private word. -/
theorem warm_cell_ne_empty (word : Bool) :
    unitCache word ≠ (∅ : (Unit →ₒ Bool).QueryCache) := by
  intro h
  have lookup := congrArg (fun cache : (Unit →ₒ Bool).QueryCache => cache ()) h
  simp at lookup

/-- Presampling retains the same head, adaptive continuation, and every public entry. -/
theorem retained_head (next : Bool → OracleComp Source (Except Unit Bool))
    (raw : Pub.QueryCache) :
    (simulateQ (idealImpl Pub Unit Bool)
      (liftM (Source.query (.inr ())) >>= next)).run (raw, ∅) =
      (do
        let word ← $ᵗ Bool
        (simulateQ (idealImpl Pub Unit Bool)
          (liftM (Source.query (.inr ())) >>= next)).run (raw, unitCache word)) := by
  simpa only [empty_cacheQuery_unit] using
    idealImpl_run_presample_first_derive Pub () next (raw, ∅) (by simp)

/-- Every possible cold tick endpoint inserts its reply while preserving the entire public cache. -/
theorem cold_tick_caches_reply (raw : Pub.QueryCache)
    (z : Unit × (Pub + UnitTick).QueryCache)
    (supported : z ∈ support (((Pub + UnitTick).randomOracle (.inr ())).run
      (QueryCache.addEquiv Pub UnitTick (raw, ∅)))) :
    z = ((), QueryCache.addEquiv Pub UnitTick (raw, unitCache ())) := by
  rw [randomOracle.run_eq, QueryCache.addEquiv_apply_inr] at supported
  simp only [QueryCache.empty_apply, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨value, _, rfl⟩ := supported
  cases value
  rw [← QueryCache.addEquiv_cacheQuery_inr, empty_cacheQuery_unit]

/-- A warm auxiliary tick returns its existing reply and retains the full target cache. -/
theorem warm_tick_replays (raw : Pub.QueryCache) :
    ((Pub + UnitTick).randomOracle (.inr ())).run
        (QueryCache.addEquiv Pub UnitTick (raw, QueryCache.ofFn (fun _ => some ()))) =
      pure ((), QueryCache.addEquiv Pub UnitTick (raw, QueryCache.ofFn (fun _ => some ()))) := by
  simp

/-- The full original state is preserved for every program, starting with a cold tick cache. -/
theorem cold_tick_full_state {α : Type} (word : Bool) (body : OracleComp Source α)
    (raw : Pub.QueryCache) :
    Prod.map id (paidUnitReadback Pub word) <$>
        (simulateQ (Pub + UnitTick).romImpl
          (simulateQ (paidInlineUnitDerivations Pub word) body)).run
            (QueryCache.addEquiv Pub UnitTick (raw, ∅)) =ᵈ
      (simulateQ (idealImpl Pub Unit Bool) body).run (raw, unitCache word) := by
  simpa only [paidUnitReadback_addEquiv] using
    map_run_simulateQ_paidInlineUnitDerivations Pub word body
      (QueryCache.addEquiv Pub UnitTick (raw, ∅))

/-- A warm tick cache obeys the same full-state frame, including normal error and stop data. -/
theorem warm_tick_failure_data (word : Bool)
    (body : OracleComp Source (Option (Except Unit Bool))) (raw : Pub.QueryCache) :
    Prod.map id (paidUnitReadback Pub word) <$>
        (simulateQ (Pub + UnitTick).romImpl
          (simulateQ (paidInlineUnitDerivations Pub word) body)).run
            (QueryCache.addEquiv Pub UnitTick (raw, QueryCache.ofFn (fun _ => some ()))) =ᵈ
      (simulateQ (idealImpl Pub Unit Bool) body).run (raw, unitCache word) := by
  simpa only [paidUnitReadback_addEquiv] using
    map_run_simulateQ_paidInlineUnitDerivations Pub word body
      (QueryCache.addEquiv Pub UnitTick (raw, QueryCache.ofFn (fun _ => some ())))

/-- A normal error remains data while a later private read still pays its primitive tick. -/
theorem error_data_keeps_later_tick (word : Bool) :
    simulateQ (paidInlineUnitDerivations Pub word)
      (do
        let result : Except Unit Bool ← pure (.error ())
        let _ ← liftM (Source.query (.inr ()))
        pure result) =
      ((fun _ : Unit => Except.error ()) <$>
        (liftM (Target.query (.inr (.inr ()))) : OracleComp Target Unit) :
          OracleComp Target (Except Unit Bool)) := by
  simp

/-- Readback retains every original public entry, independent of the auxiliary tick cache. -/
theorem full_public_cache_readback (word : Bool) (raw : Pub.QueryCache)
    (ticks : UnitTick.QueryCache) :
    (paidUnitReadback Pub word (QueryCache.addEquiv Pub UnitTick (raw, ticks))).1 = raw := by
  rw [paidUnitReadback_addEquiv]

end HiddenSeedUnitToy
