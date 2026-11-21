/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Presampling a private cell and retaining its paid Unit queries

A reached first private query can be presampled while retaining that same query and full state.
A warm private Unit cell can be read through a dedicated Unit-returning random-oracle query.
Each such read issues one tick, including replays.
The tick cache is retained in the target state and discarded only by an explicit readback.
Ordinary public queries and fresh uniform draws keep their own ports.
-/

public section

open OracleComp OracleSpec

namespace SecretEncoding

variable {ι R : Type} (pub : OracleSpec ι)

/-- The private Unit table stores this full value at its only input. -/
@[expose] def unitCache (r : R) : (Unit →ₒ R).QueryCache := .ofFn fun _ => some r

/-- Every Unit lookup returns the full stored value. -/
@[simp] theorem unitCache_apply (r : R) (u : Unit) : unitCache r u = some r := rfl

/-- The first fill of an empty Unit table produces the constant replay table. -/
@[simp] theorem empty_cacheQuery_unit (r : R) :
    (∅ : (Unit →ₒ R).QueryCache).cacheQuery () r = unitCache r := by
  apply QueryCache.ext
  rintro ⟨⟩
  simp

/-- The auxiliary oracle records each private read as one Unit-returning query. -/
abbrev UnitTick := Unit →ₒ Unit

/-- Forward uniform/public queries and replace each private read by one tick with a fixed reply. -/
@[expose] def paidInlineUnitDerivations (r : R) :
    QueryImpl (pub.withDerivations Unit R) (OracleComp (unifSpec + (pub + UnitTick))) := fun
  | .inl (.inl n) => liftM ((unifSpec + (pub + UnitTick)).query (.inl n))
  | .inl (.inr t) => liftM ((unifSpec + (pub + UnitTick)).query (.inr (.inl t)))
  | .inr _ => (fun _ : Unit => r) <$>
      (liftM ((unifSpec + (pub + UnitTick)).query (.inr (.inr ()))) :
        OracleComp (unifSpec + (pub + UnitTick)) Unit)

/-- Ordinary private sampling is forwarded afresh rather than stored in the Unit table. -/
@[simp] theorem paidInlineUnitDerivations_uniform (r : R) (n : Nat) :
    paidInlineUnitDerivations pub r (.inl (.inl n)) =
      liftM ((unifSpec + (pub + UnitTick)).query (.inl n)) := rfl

/-- An ordinary public query retains its original input and dependent reply. -/
@[simp] theorem paidInlineUnitDerivations_public (r : R) (t : ι) :
    paidInlineUnitDerivations pub r (.inl (.inr t)) =
      liftM ((unifSpec + (pub + UnitTick)).query (.inr (.inl t))) := rfl

/-- Every private read, including a replay, still contains its literal primitive tick query. -/
@[simp] theorem paidInlineUnitDerivations_derive (r : R) (u : Unit) :
    paidInlineUnitDerivations pub r (.inr u) =
      (fun _ : Unit => r) <$>
        (liftM ((unifSpec + (pub + UnitTick)).query (.inr (.inr ()))) :
          OracleComp (unifSpec + (pub + UnitTick)) Unit) := rfl

/-- Preserve the entire public cache and restore the original warm private Unit table. -/
@[expose] def paidUnitReadback (r : R) (cache : (pub + UnitTick).QueryCache) :
    SplitCache pub Unit R :=
  (((QueryCache.addEquiv pub UnitTick).symm cache).1, unitCache r)

/-- Readback drops only the auxiliary tick cache. -/
@[simp] theorem paidUnitReadback_addEquiv (r : R) (raw : pub.QueryCache)
    (ticks : UnitTick.QueryCache) :
    paidUnitReadback pub r (QueryCache.addEquiv pub UnitTick (raw, ticks)) =
      (raw, unitCache r) := by
  simp [paidUnitReadback]

section Interpretation

variable [DecidableEq ι] [∀ t : pub.Domain, SampleableType (pub.Range t)] [SampleableType R]

/-- Presample a missing cell while keeping the same reached head query and continuation.

Every other private cell, the full public cache, and the complete final endpoint are retained.
This statement requires the private query as the actual program head.
-/
theorem idealImpl_run_presample_first_derive {X α : Type} [DecidableEq X]
    (x : X) (next : R → OracleComp (pub.withDerivations X R) α)
    (initial : SplitCache pub X R) (missing : initial.2 x = none) :
    (simulateQ (idealImpl pub X R)
      (liftM ((pub.withDerivations X R).query (.inr x)) >>= next)).run initial =
      (do
        let value ← $ᵗ R
        (simulateQ (idealImpl pub X R)
          (liftM ((pub.withDerivations X R).query (.inr x)) >>= next)).run
            (initial.1, initial.2.cacheQuery x value)) := by
  -- Expose the reached cold query and its single canonical sampler.
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    idealImpl_run_derive_none missing, bind_map_left]
  apply bind_congr
  intro value
  -- The same head query now replays that sampled cell before the same continuation.
  rw [StateT.run_bind, idealImpl_run_derive_some (v := value) (by simp), pure_bind]

omit [SampleableType R] in
private theorem paidUnit_tick_step (r : R) (raw : pub.QueryCache)
    (ticks : UnitTick.QueryCache) :
    (fun z : Unit × (pub + UnitTick).QueryCache => (r, paidUnitReadback pub r z.2)) <$>
        ((pub + UnitTick).randomOracle (.inr ())).run
          (QueryCache.addEquiv pub UnitTick (raw, ticks)) =ᵈ
      (pure (r, (raw, unitCache r)) : ProbComp (R × SplitCache pub Unit R)) := by
  rw [randomOracle.run_eq, QueryCache.addEquiv_apply_inr]
  cases ht : ticks () with
  | some value =>
    simp [paidUnitReadback_addEquiv]
  | none =>
    simp only [map_bind, map_pure,
      ← QueryCache.addEquiv_cacheQuery_inr, paidUnitReadback_addEquiv]
    -- Use the actual lossless sampler; no equality of singleton sampler implementations is needed.
    exact OracleComp.EvalDistEq.bind_const _ _

/-- One paid query projects to the same warm private-cell step, keeping its entire endpoint. -/
theorem map_run_paidInlineUnitDerivations (r : R)
    (q : (pub.withDerivations Unit R).Domain) (cache : (pub + UnitTick).QueryCache) :
    Prod.map id (paidUnitReadback pub r) <$>
        (((pub + UnitTick).romImpl ∘ₛ paidInlineUnitDerivations pub r) q).run cache =ᵈ
      (idealImpl pub Unit R q).run (paidUnitReadback pub r cache) := by
  obtain ⟨⟨raw, ticks⟩, rfl⟩ := (QueryCache.addEquiv pub UnitTick).surjective cache
  rcases q with (n | t) | u
  · simp [QueryImpl.apply_compose, paidInlineUnitDerivations, idealImpl, unifFwdImpl,
      paidUnitReadback_addEquiv, Functor.map_map, Prod.map]
  · cases ht : raw t <;>
      simp [QueryImpl.apply_compose, paidInlineUnitDerivations, idealImpl,
        ht, paidUnitReadback_addEquiv,
        ← QueryCache.addEquiv_cacheQuery_inl, Functor.map_map, Prod.map]
  · cases u
    simpa [QueryImpl.apply_compose, paidInlineUnitDerivations, idealImpl,
      paidUnitReadback_addEquiv, Functor.map_map, Prod.map] using
      paidUnit_tick_step pub r raw ticks

private theorem paidUnit_intertwines (r : R) :
    QueryImpl.Intertwines (fun cache => pure (paidUnitReadback pub r cache))
      ((pub + UnitTick).romImpl ∘ₛ paidInlineUnitDerivations pub r)
      (idealImpl pub Unit R) := by
  intro q cache γ _ f
  have h := (map_run_paidInlineUnitDerivations pub r q cache).bind_left
    (fun z => f z.1 z.2)
  simpa only [pure_bind, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq] using h.evalDist_eq

/-- Paid Unit inlining preserves the complete original result and public/private state jointly.

The target retains its auxiliary tick cache throughout execution.
Only the explicit final readback drops that cache and reconstructs the warm original table.
The statement allows every initial public cache and either a cold or warm tick cache.
-/
theorem map_run_simulateQ_paidInlineUnitDerivations {α : Type}
    (r : R) (body : OracleComp (pub.withDerivations Unit R) α)
    (cache : (pub + UnitTick).QueryCache) :
    Prod.map id (paidUnitReadback pub r) <$>
        (simulateQ (pub + UnitTick).romImpl
          (simulateQ (paidInlineUnitDerivations pub r) body)).run cache =ᵈ
      (simulateQ (idealImpl pub Unit R) body).run (paidUnitReadback pub r cache) := by
  rw [← QueryImpl.simulateQ_compose]
  let : MeasurableSpace (α × SplitCache pub Unit R) := ⊤
  apply _root_.EvalDistEq.of_evalDist_eq
  have h := (paidUnit_intertwines pub r).evalDist_simulateQ_run body cache
    (fun value state => pure (value, state))
  simpa only [pure_bind, Prod.mk.eta, bind_pure, map_eq_bind_pure_comp,
    Function.comp_def, Prod.map_apply', id_eq] using h

end Interpretation

end SecretEncoding
