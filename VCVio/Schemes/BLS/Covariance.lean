/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Oracle

/-! # Changing the sampled representation of BLS hash answers

Mapping the indexed cache commutes with an adaptive execution whenever the mapped fresh
answer distributions agree. This transports uniform scalar sampling to uniform group
sampling in the Boneh–Lynn–Shacham security game.
-/

public section

open OracleComp OracleSpec

namespace BLS

private theorem map_insert {V W M : Type} [DecidableEq M] (f : V → W)
    (s : OracleState V M) (j : Option ℕ) (msg : M) (v : V) :
    (s.insert j msg v).map f = (s.map f).insert j msg (f v) := by
  apply OracleState.ext
  · apply QueryCache.ext
    intro n
    by_cases hn : n = msg
    · subst n
      simp [OracleState.map, OracleState.insert]
    · simp [OracleState.map, OracleState.insert, hn]
  · rfl
  · rfl
  · by_cases hj : j = some s.count <;> simp [OracleState.map, OracleState.insert, hj]
  · rfl

private theorem map_recordSign {V W M : Type} (f : V → W)
    (s : OracleState V M) (j : Option ℕ) (msg : M) (i : ℕ) :
    (s.recordSign j msg i).map f = (s.map f).recordSign j msg i := rfl

/-- Mapping the value in a cache lookup and its post-state changes only the fresh-draw
representation, provided the mapped fresh-draw distributions agree. -/
theorem indexedEntry_map_evalDistEq {V W M : Type} [DecidableEq M]
    (f : V → W) (draw : ℕ → ProbComp V) (draw' : ℕ → ProbComp W)
    (hdraw : ∀ n, f <$> draw n =ᵈ draw' n)
    (j : Option ℕ) (msg : M) (s : OracleState V M) :
    ((fun z => ((f z.1.1, z.1.2), z.2.map f)) <$>
      (indexedEntry draw j msg).run s) =ᵈ
      (indexedEntry draw' j msg).run (s.map f) := by
  cases hc : s.cache msg with
  | some vi =>
    obtain ⟨v, i⟩ := vi
    simp [indexedEntry, StateT.run, OracleState.map, hc]
  | none =>
    have hcache : (s.map f).cache msg = none := by simp [OracleState.map, hc]
    have hcount : (s.map f).count = s.count := rfl
    simp only [indexedEntry, StateT.run, hc, hcache, hcount, Functor.map_map]
    simpa only [Functor.map_map, Function.comp_def, map_insert] using
      (hdraw s.count).map (fun v => ((v, s.count), (s.map f).insert j msg v))

/-- Changing the cached representation intertwines the combined hash and signing handlers. -/
theorem indexedOracle_map_intertwines {V W M G : Type} [DecidableEq M]
    (f : V → W) (draw : ℕ → ProbComp V) (draw' : ℕ → ProbComp W)
    (hdraw : ∀ n, f <$> draw n =ᵈ draw' n)
    (hash sign : W → G) (j : Option ℕ) :
    QueryImpl.Intertwines (fun s : OracleState V M => pure (s.map f))
      (indexedOracle draw (hash ∘ f) (sign ∘ f) j)
      (indexedOracle draw' hash sign j) := by
  intro t s γ _ k
  rcases t with (t | msg) | msg
  · change 𝒟[((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) >>=
      fun z => pure (z.2.map f) >>= k z.1] = _
    simp only [bind_map_left, pure_bind]
    rfl
  · simp only [indexedOracle_run_hash, bind_map_left, pure_bind]
    have h := (indexedEntry_map_evalDistEq f draw draw' hdraw j msg s).bind_left
      (fun z => k (hash z.1.1) z.2)
    simpa only [bind_map_left, Function.comp_def] using h.evalDist_eq
  · simp only [indexedOracle_run_sign, bind_map_left, pure_bind]
    have h := (indexedEntry_map_evalDistEq f draw draw' hdraw j msg s).bind_left
      (fun z => k (sign z.1.1) (z.2.recordSign j msg z.1.2))
    simpa only [bind_map_left, Function.comp_def, map_recordSign] using h.evalDist_eq

/-- The whole adaptive execution commutes in distribution with changing the cached
representation; no query bound is needed for this transport. -/
theorem simulateQ_indexedOracle_map_evalDistEq {V W M G α : Type} [DecidableEq M]
    (f : V → W) (draw : ℕ → ProbComp V) (draw' : ℕ → ProbComp W)
    (hdraw : ∀ n, f <$> draw n =ᵈ draw' n)
    (hash sign : W → G) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α) (s : OracleState V M) :
    ((fun z => (z.1, z.2.map f)) <$>
      (simulateQ (indexedOracle draw (hash ∘ f) (sign ∘ f) j) oa).run s) =ᵈ
      (simulateQ (indexedOracle draw' hash sign j) oa).run (s.map f) := by
  let : MeasurableSpace (α × OracleState W M) := ⊤
  apply EvalDistEq.of_evalDist_eq
  have hi := indexedOracle_map_intertwines (M := M) f draw draw' hdraw hash sign j
  have h := hi.evalDist_simulateQ_run oa s (fun a st => pure (a, st))
  simpa only [pure_bind, bind_pure_comp, bind_pure, Prod.eta, id_map, map_pure] using h

end BLS
