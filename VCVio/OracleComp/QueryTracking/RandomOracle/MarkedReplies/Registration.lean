/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.MarkedReplies
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Charging matches against targets registered during an adaptive computation

A caller can update its targets between any two random-oracle queries.
Each address can select a target key.
A cold query is charged when its key has an active target.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace randomOracle.Targets

variable {ι K V Notice : Type} {pub : OracleSpec ι}

/-- Private sampling and ordinary hash calls, with notices that update the active targets. -/
abbrev Queries (pub : OracleSpec ι) (Notice : Type) := (unifSpec + pub) + (Notice →ₒ Unit)

/-- The ordinary cache, current targets, number of charged fresh queries and record of a match. -/
structure State (pub : OracleSpec ι) (K V : Type) where
  /-- The public table used by the random oracle. -/
  cache : pub.QueryCache
  /-- The latest target registered for each key. -/
  target : K → Option V
  /-- The number of cold queries at keys with an active target. -/
  paid : Nat
  /-- Whether one of those queries matched its active target. -/
  hit : Bool

/-- A registration can use the caller's notice, existing cache and earlier targets. -/
abbrev Register (pub : OracleSpec ι) (Notice K V : Type) :=
  Notice → pub.QueryCache → (K → Option V) → K → Option V

variable [DecidableEq ι] [DecidableEq V]
  [∀ t : pub.Domain, SampleableType (pub.Range t)]

/-- Record a fresh reply under the target in force before this query. -/
@[expose] def update (role : ι → Option K) (project : ∀ t, pub.Range t → V)
    (s : State pub K V) (t : ι) (w : pub.Range t) (next : pub.QueryCache) : State pub K V :=
  if (s.cache t).isSome then { s with cache := next }
  else match (role t).bind s.target with
    | none => { s with cache := next }
    | some v =>
      { s with cache := next, paid := s.paid + 1, hit := s.hit || decide (project t w = v) }

/-- Serve every ordinary hash from the same lazy table and record fresh target matches. -/
@[expose] noncomputable def impl (register : Register pub Notice K V)
    (role : ι → Option K) (project : ∀ t, pub.Range t → V) :
    QueryImpl (Queries pub Notice) (StateT (State pub K V) ProbComp) :=
  fun input => match input with
  | .inl (.inl i) => fun s => (fun w => (w, s)) <$> liftM (unifSpec.query i)
  | .inl (.inr t) => fun s =>
    (fun z => (z.1, update role project s t z.1 z.2)) <$> (pub.randomOracle t).run s.cache
  | .inr n => fun s => pure ((), { s with target := register n s.cache s.target })

/-- A public operation returns the actual random-oracle answer and updates the watch once. -/
theorem public_run (register : Register pub Notice K V)
    (role : ι → Option K) (project : ∀ t, pub.Range t → V)
    (s : State pub K V) (t : ι) :
    (impl register role project (.inl (.inr t))).run s =
      (fun z => (z.1, update role project s t z.1 z.2)) <$> (pub.randomOracle t).run s.cache := rfl

/-- Forgetting registrations leaves ordinary queries and private samples intact. -/
@[expose] noncomputable def erase :
    QueryImpl (Queries pub Notice) (StateT pub.QueryCache ProbComp) :=
  fun input => match input with
  | .inl h => (unifFwdImpl pub + pub.randomOracle) h
  | .inr _ => pure ()

/-- Erasing the watch state preserves both the caller's result and its entire public cache. -/
theorem erase_run (register : Register pub Notice K V) (role : ι → Option K)
    (project : ∀ t, pub.Range t → V) {α : Type}
    (caller : OracleComp (Queries pub Notice) α) (s : State pub K V) :
    (fun z => (z.1, z.2.cache)) <$> (simulateQ (impl register role project) caller).run s =
      (simulateQ erase caller).run s.cache := by
  apply map_run_simulateQ_eq_of_query_map_eq
  rintro ((i | t) | n) s
  · change _ = ((unifFwdImpl pub + pub.randomOracle) (.inl i)).run s.cache
    rw [roSim.run_apply_inl]
    simp [impl, StateT.run, Functor.map_map]
  · change _ = (pub.randomOracle t).run s.cache
    simp only [public_run, Functor.map_map]
    have idMap : (fun z : pub.Range t × pub.QueryCache =>
        (z.1, (update role project s t z.1 z.2).cache)) = id := by
      funext z
      unfold update
      split
      · rfl
      · split <;> rfl
    change (fun z : pub.Range t × pub.QueryCache => (z.1, (update role project s t z.1 z.2).cache))
      <$> (pub.randomOracle t).run s.cache = _
    rw [idMap, id_map]
  · rfl

/-- One cold query pays at most its singleton match probability, even across target changes. -/
theorem charged (register : Register pub Notice K V)
    (role : ι → Option K) (project : ∀ t, pub.Range t → V)
    (ε : ℝ≥0∞) (rate : ∀ t k, role t = some k → ∀ v,
      Pr{let w ← $ᵗ (pub.Range t)}[project t w = v] ≤ ε) :
    IsPotentialStep (impl register role project) (fun s => s.hit = true)
      (fun s => (s.paid : ℝ≥0∞) * ε) := by
  constructor
  · rintro ((i | t) | n) s z hz
    · change z ∈ support ((fun w => (w, s)) <$> _) at hz
      rw [support_map] at hz
      obtain ⟨_, _, rfl⟩ := hz
      rfl
    · rw [public_run, support_map] at hz
      obtain ⟨w, _, rfl⟩ := hz
      unfold update
      split
      · exact le_rfl
      · split
        · exact le_rfl
        · gcongr
          exact Nat.le_succ _
    · change z ∈ support (pure _) at hz
      rw [mem_support_pure_iff] at hz
      subst z
      exact le_rfl
  · rintro ((i | t) | n) s good
    · exact Or.inr ⟨liftM (unifSpec.query i), fun _ => s, 0, rfl, by simp [good], fun _ => by simp⟩
    · simp only [public_run]
      cases cached : s.cache t with
      | some w =>
        refine Or.inl ⟨w, s, ?_, good⟩
        rw [QueryImpl.withCaching_run_some _ cached]
        simp [update, cached]
      | none =>
        cases active : (role t).bind s.target with
        | none =>
          refine Or.inr ⟨$ᵗ pub.Range t, fun w => {s with cache := s.cache.cacheQuery t w}, 0,
            ?_, by simp [good], fun _ => by simp⟩
          rw [QueryImpl.withCaching_run_none _ cached]
          simp [uniformSampleImpl, Functor.map_map, update, cached, active]
        | some v =>
          refine Or.inr ⟨$ᵗ pub.Range t, fun w =>
            {s with cache := s.cache.cacheQuery t w, paid := s.paid + 1,
                    hit := s.hit || decide (project t w = v)}, ε, ?_, ?_, ?_⟩
          · rw [QueryImpl.withCaching_run_none _ cached]
            simp [uniformSampleImpl, Functor.map_map, update, cached, active]
          · obtain ⟨k, hk, _⟩ := Option.bind_eq_some_iff.mp active
            apply (prEvent_mono _ _ (fun w : pub.Range t => project t w = v) ?_).trans
              (rate t k hk v)
            intro w matched
            simpa only [Bool.or_eq_true, good, Bool.false_eq_true, false_or, decide_eq_true_eq]
              using matched
          · intro w
            simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
            rw [add_comm]
    · exact Or.inl ⟨(), _, rfl, good⟩

/-- An interleaved caller pays according to its observed number of cold queries with a target. -/
theorem prEvent_hit_and_paid {α : Type} (register : Register pub Notice K V)
    (role : ι → Option K) (project : ∀ t, pub.Range t → V)
    (ε : ℝ≥0∞) (finite : ε ≠ ⊤) (rate : ∀ t k, role t = some k → ∀ v,
      Pr{let w ← $ᵗ (pub.Range t)}[project t w = v] ≤ ε)
    (caller : OracleComp (Queries pub Notice) α) (s : State pub K V) (clean : s.hit = false)
    (q : Nat) :
    Pr{let z ← (simulateQ (impl register role project) caller).run s}[
      z.2.hit = true ∧ z.2.paid ≤ q] ≤ (q : ℝ≥0∞) * ε := by
  have step := charged register role project ε rate
  apply (prEvent_mono _ _ _ ?_).trans
    ((prEvent_and_le_of_potential _ _ _ step.mono step.step caller (q * ε) (by finiteness) s
      (by simp [clean])).trans tsub_le_self)
  rintro z ⟨found, count⟩
  refine ⟨found, ?_⟩
  gcongr

end randomOracle.Targets
