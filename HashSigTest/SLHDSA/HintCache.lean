/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import HashSig.SLHDSA.Security.HintCache
public import HashSig.SLHDSA.Security.CacheDecomposition

/-!
# Adaptive cache replay checks

The first answer supplies the second query. Two incomparable caches contain one answer each.
A cache extending both settles that adaptive read. Two different answers at the same query
prevent a common cache.
-/

public section

namespace HashSigTest.HintCache

open OracleSpec

/-- Each Boolean request expects a Boolean response. -/
abbrev spec := Bool →ₒ Bool

/-- Each history answers its own query with the other Boolean. -/
def history (t : Bool) : spec.QueryCache := QueryCache.ofFn fun q =>
  if q = t then some (!t) else none

/-- Use the first answer as the next request. -/
def adaptive : OracleComp spec Bool := do
  let next ← liftM (spec.query false)
  liftM (spec.query next)

/-- Each input cache misses one of the two reads. -/
theorem adaptive_misses (t : Bool) : simulateQ (history t).toPartialImpl adaptive = none := by
  cases t <;> rfl

/-- The cache-order criterion supplies one shared upper bound for the two incomparable histories. -/
theorem one_label_upperBound : ∃ replay : Unit → spec.QueryCache, ∀ t, history t ≤ replay () := by
  apply (QueryCache.exists_hint_upperBound_iff history (fun _ => ())).2
  intro t t' _ q b b' hb hb'
  cases t <;> cases t' <;> cases q <;> simp_all [history]

/-- The two stored answers force a successful adaptive read in every common upper bound. -/
theorem adaptive_hit_of_upperBound (c : spec.QueryCache) (extendsCache : ∀ t, history t ≤ c) :
    simulateQ c.toPartialImpl adaptive = some false := by
  have first := (QueryCache.le_def.mp (extendsCache false))
    (show history false false = some true from rfl)
  simp only [adaptive, simulateQ_bind, simulateQ_spec_query, QueryCache.toPartialImpl_apply,
    first]
  exact (QueryCache.le_def.mp (extendsCache true)) (show history true true = some false from rfl)

/-- One cache cannot preserve both the hits and the misses of these two histories. -/
theorem no_one_label_exact :
    ¬ ∃ c : spec.QueryCache, ∀ t (oa : OracleComp spec Bool),
      simulateQ (history t).toPartialImpl oa = simulateQ c.toPartialImpl oa := by
  rintro ⟨c, agrees⟩
  let read : OracleComp spec Bool := liftM (spec.query false)
  have collision := (agrees false read).trans (agrees true read).symm
  exact Option.some_ne_none true collision

/-- Disagreement between two present answers prevents even settled replay with one label. -/
theorem conflict_rejects_one_label :
    ¬ ∃ replay : Unit → spec.QueryCache, ∀ t : Bool,
      (QueryCache.ofFn (spec := spec) (fun _ => some t)) ≤ replay () := by
  intro agreed
  have consistent := (QueryCache.exists_hint_upperBound_iff
    (fun t => QueryCache.ofFn (spec := spec) (fun _ => some t)) (fun _ => ())).1 agreed
  have : false = true := consistent false true rfl false false true rfl rfl
  contradiction

open SLHDSA SLHDSA.Security

/-- Two actual WOTS+ hash entries suffice for the replayed two-step chain. The input of the
second hash is the answer to the first. -/
theorem two_hash_reads_replayed {p : Params} {core : CorePrimitives p} {T H : Type*}
    {cache : T → PublicHash.Cache core} {hint : T → H} {replay : H → PublicHash.Cache core}
    (extendsCache : ∀ t, cache t ≤ replay (hint t))
    (t : T) (pk : core.PkSeed) (adrs : Adrs) (x first last : core.Y) (i : ℕ)
    (entry₁ : cache t (.thash pk (core.adrsToKey (adrs.setHashAddress i)) [x]) = some first)
    (entry₂ : cache t (.thash pk (core.adrsToKey (adrs.setHashAddress (i + 1))) [first]) =
      some last) :
    chain? core (replay (hint t)) pk adrs x i 2 = some last := by
  apply chain?_eq_some_of_hint extendsCache t
  apply (chain?_succ_eq_some_iff core (cache t) pk adrs x i 1).2
  refine ⟨first, ?_, entry₂⟩
  exact (chain?_succ_eq_some_iff core (cache t) pk adrs x i 0).2 ⟨x, rfl, entry₁⟩

end HashSigTest.HintCache
