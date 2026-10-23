/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Lazy Random Oracle

The (lazy) random oracle samples a fresh uniform value on first query and caches the result
for future consistency. Same input always yields same output. State: `QueryCache`.
This is `uniformSampleImpl.withCaching`.

Two lazy random oracles run side by side on a product cache take the same steps as one lazy
random oracle on the sum signature, with the two caches paired by `OracleSpec.QueryCache.addEquiv`
(`QueryImpl.run_parallelStateT_randomOracle_map_eq`).
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

namespace QueryImpl

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}
  [DecidableEq ι₁] [DecidableEq ι₂]
  [∀ t : spec₁.Domain, SampleableType (spec₁.Range t)]
  [∀ t : spec₂.Domain, SampleableType (spec₂.Range t)]

/-- One step of the two independent lazy random oracles on a product cache is one step of the
lazy random oracle on the sum signature, transported along `OracleSpec.QueryCache.addEquiv`. -/
lemma run_parallelStateT_randomOracle_map_eq (t : (spec₁ + spec₂).Domain)
    (p : spec₁.QueryCache × spec₂.QueryCache) :
    Prod.map id (QueryCache.addEquiv spec₁ spec₂) <$>
        ((QueryImpl.parallelStateT spec₁.randomOracle spec₂.randomOracle) t).run p =
      ((spec₁ + spec₂).randomOracle t).run (QueryCache.addEquiv spec₁ spec₂ p) := by
  obtain ⟨c₁, c₂⟩ := p
  cases t with
  | inl t =>
      rcases h : c₁ t with _ | u <;>
        simp [QueryImpl.parallelStateT, h, QueryCache.addEquiv_cacheQuery_inl, Prod.map]
  | inr t =>
      rcases h : c₂ t with _ | u <;>
        simp [QueryImpl.parallelStateT, h, QueryCache.addEquiv_cacheQuery_inr, Prod.map]

end QueryImpl
