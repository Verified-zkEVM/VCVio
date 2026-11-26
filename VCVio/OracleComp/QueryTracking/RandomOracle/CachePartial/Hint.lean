/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
import PolyFun.PFunctor.Handler.Hint

/-!
# A common cache for histories with the same hint

A decoder can choose a cache that extends every history sharing a hint exactly when
the histories agree wherever two of them have an answer to the same query.
-/

public section

namespace OracleSpec.QueryCache

variable {ι T H : Type*} {spec : OracleSpec ι}

/-- A hint selects one upper bound in the cache order for each fiber of pairwise compatible
histories. Empty fibers can use the empty cache. -/
theorem exists_hint_upperBound_iff (cache : T → spec.QueryCache) (hint : T → H) :
    (∃ replay : H → spec.QueryCache, ∀ t, cache t ≤ replay (hint t)) ↔
      ∀ t t', hint t = hint t' → ∀ q b b', cache t q = some b →
        cache t' q = some b' → b = b' := by
  refine Iff.trans ?_ (PFunctor.Handler.Hint.exists_preservesSettled_iff
    (P := spec.toPFunctor) (fun t => (cache t).toPartialImpl.toHandler) hint)
  constructor
  · rintro ⟨replay, extendsCache⟩
    exact ⟨fun s => (replay s).toPartialImpl.toHandler, fun t _ _ hb => extendsCache t hb⟩
  · rintro ⟨d, hd⟩
    exact ⟨fun s => ofFn (d s), fun t q b hb => hd t q b hb⟩

end OracleSpec.QueryCache
