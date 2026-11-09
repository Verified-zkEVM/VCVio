/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed.CacheExtension

/-!
# Full-value ideal-cache extension controls

Warm public and private cells retain their full answers in the same terminal state.
Repeated uniform queries remain two forwarded draws and never become a cached row.
The whole-run law also covers returned `none` and arbitrary adaptive continuations.
-/

public section

namespace HiddenSeedCacheExtensionTest

open OracleComp OracleSpec SecretEncoding

variable {ι X R : Type} {pub : OracleSpec ι} [DecidableEq ι] [DecidableEq X]
  [∀ t, SampleableType (pub.Range t)] [SampleableType R]

/-- A warm public answer and private value survive one whole optional-output endpoint together. -/
theorem warm_values {α : Type} (body : OracleComp (pub.withDerivations X R) (Option α))
    (initial : SplitCache pub X R) (z : Option α × SplitCache pub X R)
    (reached : z ∈ support ((simulateQ (idealImpl pub X R) body).run initial))
    (t : pub.Domain) (answer : pub.Range t) (publicWarm : initial.1 t = some answer)
    (x : X) (value : R) (privateWarm : initial.2 x = some value) :
    z.2.1 t = some answer ∧ z.2.2 x = some value := by
  have extension := simulateQ_idealImpl_cache_le body initial z reached
  exact ⟨extension.1 publicWarm, extension.2 privateWarm⟩

/-- Returning `none` does not erase either table below the optional result. -/
theorem none_keeps_values {α : Type} (body : OracleComp (pub.withDerivations X R) (Option α))
    (initial final : SplitCache pub X R)
    (reached : (none, final) ∈ support ((simulateQ (idealImpl pub X R) body).run initial)) :
    initial.1 ≤ final.1 ∧ initial.2 ≤ final.2 :=
  simulateQ_idealImpl_cache_le body initial (none, final) reached

/-- A response-dependent continuation retains every full initial cell in its actual endpoint. -/
theorem adaptive_continuation {α β : Type} (body : OracleComp (pub.withDerivations X R) α)
    (next : α → OracleComp (pub.withDerivations X R) β) (initial : SplitCache pub X R)
    (z : β × SplitCache pub X R)
    (reached : z ∈ support ((simulateQ (idealImpl pub X R) (body >>= next)).run initial)) :
    initial ≤ z.2 :=
  simulateQ_idealImpl_cache_le (body >>= next) initial z reached

/-- Two occurrences of the same uniform query are two independent forwarded draws. -/
theorem two_uniforms (n : Nat) (initial : SplitCache pub X R) :
    (simulateQ (idealImpl pub X R) (do
      let first ← liftM ((pub.withDerivations X R).query (.inl (.inl n)))
      let second ← liftM ((pub.withDerivations X R).query (.inl (.inl n)))
      pure (first, second))).run initial = (do
        let first ← (unifSpec.query n : ProbComp (Fin (n + 1)))
        let second ← (unifSpec.query n : ProbComp (Fin (n + 1)))
        pure ((first, second), initial)) := by
  simp [simulateQ_bind, idealImpl, StateT.run_bind]

/-- A missing private label stores its whole sampled value beside the original public table. -/
theorem missing_private (x : X) (initial : SplitCache pub X R) (missing : initial.2 x = none) :
    (idealImpl pub X R (.inr x)).run initial =
      (fun value => (value, (initial.1, initial.2.cacheQuery x value))) <$> ($ᵗ R) :=
  idealImpl_run_derive_none missing

end HiddenSeedCacheExtensionTest
