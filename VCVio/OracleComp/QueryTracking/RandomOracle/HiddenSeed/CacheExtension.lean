/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed

/-!
# Full cache extension in the ideal hidden-seed handler

Every supported ideal step preserves each recorded public answer and private derivation value.
The same extension law holds for every supported complete run, from any initial pair of caches.
Uniform queries are forwarded separately and leave both caches unchanged.
-/

public section

namespace SecretEncoding

open OracleComp OracleSpec

variable {ι X R : Type} {pub : OracleSpec ι} [DecidableEq ι] [DecidableEq X]
  [∀ t, SampleableType (pub.Range t)] [SampleableType R]

/-- Every supported ideal query extends both caches without changing recorded full values. -/
theorem idealImpl_cache_le (input : (pub.withDerivations X R).Domain)
    (initial : SplitCache pub X R) (z : (pub.withDerivations X R).Range input × SplitCache pub X R)
    (supported : z ∈ support ((idealImpl pub X R input).run initial)) : initial ≤ z.2 := by
  rcases input with (draw | backend) | label
  · simp only [idealImpl, StateT.run_mk, support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact le_rfl
  · simp only [idealImpl, StateT.run_mk, support_map, Set.mem_image] at supported
    obtain ⟨result, reached, rfl⟩ := supported
    exact ⟨QueryImpl.withCaching_cache_le _ _ _ _ reached, le_rfl⟩
  · simp only [idealImpl, StateT.run_mk, support_map, Set.mem_image] at supported
    obtain ⟨result, reached, rfl⟩ := supported
    exact ⟨le_rfl, QueryImpl.withCaching_cache_le _ _ _ _ reached⟩

/-- A supported whole ideal execution retains every full value from its initial caches. -/
theorem simulateQ_idealImpl_cache_le {α : Type} (body : OracleComp (pub.withDerivations X R) α)
    (initial : SplitCache pub X R) (z : α × SplitCache pub X R)
    (supported : z ∈ support ((simulateQ (idealImpl pub X R) body).run initial)) :
    initial ≤ z.2 :=
  simulateQ_run_preservesInv (idealImpl pub X R) (initial ≤ ·)
    (fun input current before result reached => before.trans
      (idealImpl_cache_le input current result reached)) body initial le_rfl z supported

end SecretEncoding
