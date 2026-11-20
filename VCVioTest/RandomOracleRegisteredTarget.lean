/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.MarkedReplies.Registration
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! # Registering the answer to a previous query -/

public section

open OracleSpec OracleComp
open scoped ENNReal
open randomOracle.Targets

namespace VCVioTest.RandomOracleRegisteredTarget

/-- A Boolean random oracle with infinitely many addresses. -/
abbrev H := Nat →ₒ Bool
/-- A notice selects a Boolean target for the shared key. -/
abbrev Q := Queries H (Unit × Bool)

/-- The latest notice sets the target for all addresses. -/
def register : Register H (Unit × Bool) Unit Bool :=
  fun n _ old => Function.update old n.1 (some n.2)

/-- Begin with an empty cache and no active target. -/
def initial : State H Unit Bool := ⟨∅, fun _ => none, 0, false⟩

/-- Querying a cell, registering its actual answer, and repeating the same query costs zero
and cannot fire a retroactive match. -/
theorem register_previous (t : Nat) :
    ∀ z ∈ support ((simulateQ (impl register (fun _ : Nat => some ()) (fun _ b => b)) (do
      let w ← query (spec := Q) (.inl (.inr t))
      let _ ← query (spec := Q) (.inr ((), w))
      query (spec := Q) (.inl (.inr t)))).run initial),
      z.2.paid = 0 ∧ z.2.hit = false ∧ z.2.cache t = some z.1 := by
  intro z hz
  simp only [simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, b, hb, last⟩ := hz
  change a ∈ support ((fun w => _) <$> (H.randomOracle t).run ∅) at ha
  rw [QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _), support_map] at ha
  obtain ⟨w, hw, rfl⟩ := ha
  change b ∈ support (pure _) at hb
  rw [mem_support_pure_iff] at hb
  subst b
  simp only [uniformSampleImpl, support_map] at hw
  obtain ⟨v, _, rfl⟩ := hw
  change z ∈ support ((impl register (fun _ : Nat => some ()) (fun _ b => b) (.inl (.inr t))).run
    (⟨(∅ : H.QueryCache).cacheQuery t v, Function.update (fun _ => none) () (some v),
      0, false⟩ : State H Unit Bool)) at last
  rw [public_run, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ t v),
    map_pure, mem_support_pure_iff] at last
  subst z
  simp [update]

/-- A cold Boolean cell pays once and hits its registered target with probability one half. -/
theorem registered_cold (t : Nat) :
    Pr{let z ← (simulateQ (impl register (fun _ : Nat => some ()) (fun _ b => b)) (do
      let _ ← query (spec := Q) (.inr ((), true))
      query (spec := Q) (.inl (.inr t)))).run initial}[
        z.2.hit = true ∧ z.2.paid = 1] = (2 : ℝ≥0∞)⁻¹ := by
  simp only [simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind]
  change Pr{let z ← pure ((), _) >>= _}[ _ ] = _
  rw [pure_bind, public_run]
  dsimp only [initial, Prod.snd]
  rw [QueryImpl.withCaching_run_none (t := t) _ (QueryCache.empty_apply _)]
  suffices h : Pr{let b ← $ᵗ Bool}[b = true] = (2 : ℝ≥0∞)⁻¹ by
    simpa [uniformSampleImpl, update, register, -SampleableType.prEvent_uniformSample] using h
  simp [-SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample_eq_singleton_natCard,
    Nat.card_eq_fintype_card]

end VCVioTest.RandomOracleRegisteredTarget
