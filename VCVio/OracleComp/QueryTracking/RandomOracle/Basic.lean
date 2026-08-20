/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Lazy Random Oracle

The (lazy) random oracle samples a fresh uniform value on first query and caches the result
for future consistency. Same input always yields same output. State: `QueryCache`.
This is `uniformSampleImpl.withCaching`.
-/

@[expose] public section

open OracleComp OracleSpec

/-- The (lazy) random oracle: uniform sampling with caching. -/
@[inline, reducible] def OracleSpec.randomOracle {ι} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] :
    QueryImpl spec (StateT spec.QueryCache ProbComp) :=
  uniformSampleImpl.withCaching

namespace randomOracle

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

lemma apply_eq (t : spec₀.Domain) :
    spec₀.randomOracle t = (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← $ᵗ spec₀.Range t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

/-- Running one random-oracle query returns a cached answer when present, or samples and caches a
fresh answer otherwise. This is the proof-facing cache-step law for `randomOracle`. -/
lemma run_eq (t : spec₀.Domain) (cache : spec₀.QueryCache) :
    (spec₀.randomOracle t).run cache =
      match cache t with
      | some u => pure (u, cache)
      | none => ($ᵗ spec₀.Range t) >>= fun u => pure (u, cache.cacheQuery t u) := by
  cases h : cache t with
  | none =>
    rw [QueryImpl.withCaching_run_none uniformSampleImpl h, map_eq_bind_pure_comp]
    rw [uniformSampleImpl_apply]
    exact bind_congr fun _ => Eq.refl _
  | some u => rw [QueryImpl.withCaching_run_some uniformSampleImpl h]

end randomOracle
