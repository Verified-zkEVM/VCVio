/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Association-list representation of an oracle cache

The first binding of each key is its cached response. On a miss the handler draws
one answer and prepends it; a hit reuses the first binding without running the draw.
Decoding preserves the full response and state of any adaptive client, for arbitrary
initial lists including shadowed duplicate keys.
-/

public section

universe u v

open OracleComp OracleSpec

namespace QueryImpl.ListCache

variable {D R : Type u} [DecidableEq D]

/-- Interpret the first bindings of an association list as a query cache. -/
@[expose]
def decode (cache : List (D × R)) : (D →ₒ R).QueryCache := fun q => cache.lookup q

@[simp] theorem decode_nil : decode ([] : List (D × R)) = ∅ := by
  funext q
  simp only [decode, List.lookup_nil, QueryCache.empty_apply]

@[simp] theorem decode_cons (cache : List (D × R)) (d : D) (r : R) :
    decode ((d, r) :: cache) = (decode cache).cacheQuery d r := by
  funext q
  by_cases h : q = d
  · subst q; simp [decode]
  · simp [decode, List.lookup_cons, beq_eq_false_iff_ne.mpr h, h, QueryCache.cacheQuery_of_ne]

/-- Reuse the first cached answer or draw and prepend a new binding on a miss. -/
@[expose]
def handler {m : Type u → Type v} [Monad m]
    (draw : QueryImpl (D →ₒ R) m) : QueryImpl (D →ₒ R) (StateT (List (D × R)) m) :=
  fun d cache => match cache.lookup d with
    | some r => pure (r, cache)
    | none => (fun r => (r, (d, r) :: cache)) <$> draw d

/-- Decoding commutes with one cached query, including its retained state. -/
theorem local_projection {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (D →ₒ R) m) (d : D) (cache : List (D × R)) :
    Prod.map id decode <$> handler draw d cache =
      draw.withCaching d (decode cache) := by
  change _ = (draw.withCaching d).run (decode cache)
  cases h : cache.lookup d with
  | none =>
      erw [QueryImpl.withCaching_run_none draw h]
      simp only [handler, h, Functor.map_map, Prod.map_apply, id_eq, decode_cons]
  | some r =>
      erw [QueryImpl.withCaching_run_some draw h]
      simp only [handler, h, map_pure]
      rfl

/-- Decoding commutes with the whole run of any adaptive oracle client. -/
theorem adaptive_projection {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (D →ₒ R) m) {A : Type u}
    (program : OracleComp (D →ₒ R) A) (cache : List (D × R)) :
    Prod.map id decode <$> (simulateQ (handler draw) program).run cache =
      (simulateQ draw.withCaching program).run (decode cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ decode (local_projection draw) program cache

end QueryImpl.ListCache
