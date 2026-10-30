/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The budgeted fresh-answer bound at the 256-bit scale

A public random oracle with `N` outputs on bit-string inputs, beside private coins. The bad
predicate is that some cached answer equals a fixed target `y₀`. A fresh answer hits `y₀` with
probability `N⁻¹` whatever the not-yet-firing cache (`fresh_hit_le`), so a computation making at
most `q` public-hash queries and any number of private-coin queries caches `y₀` with probability
at most `q * N⁻¹` (`preimage_hit_le`). At `N = 2 ^ 256` and `q = 2 ^ 64` every hypothesis is
discharged and the bound is below one (`preimage_hit_lt_one`). The bound is attained: at `N = 2`
a single public query caches `y₀` with probability exactly `2⁻¹ = q * N⁻¹` at `q = 1`
(`single_query_hit_eq`).
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace FreshAnswerTest

variable (N : ℕ) [NeZero N]

/-- A public hash with `N` outputs on bit-string inputs. -/
abbrev hashSpecN : OracleSpec (List Bool) := List Bool →ₒ Fin N

/-- A fresh answer of the `N`-valued oracle makes a cache that does not yet hold `y₀` hold it
with probability at most `N⁻¹`. -/
theorem fresh_hit_le (y₀ : Fin N) (t : (hashSpecN N).Domain)
    (c : (hashSpecN N).QueryCache) (hc : ¬ ∃ t', c t' = some y₀) (ht : c t = none) :
    Pr{let u ← ($ᵗ (hashSpecN N).Range t : ProbComp _)}[∃ t', c.cacheQuery t u t' = some y₀] ≤
      (N : ℝ≥0∞)⁻¹ := by
  have hset : ∀ u : Fin N, (∃ t', c.cacheQuery t u t' = some y₀) ↔ u = y₀ := by
    intro u
    constructor
    · rintro ⟨t', ht'⟩
      by_cases h : t' = t
      · subst h; simpa using ht'
      · exact absurd ⟨t', by simpa [QueryCache.cacheQuery_of_ne _ _ h] using ht'⟩ hc
    · rintro rfl; exact ⟨t, by simp⟩
  simp only [hset]
  rw [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample_singleton]
  simp

/-- A computation with private coins making at most `q` queries to an `N`-valued random oracle
caches a fixed output with probability at most `q * N⁻¹`. -/
theorem preimage_hit_le {α : Type} (y₀ : Fin N) (oa : OracleComp (unifSpec + hashSpecN N) α)
    {q : ℕ} (h : IsQueryBoundP oa (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (unifFwdImpl (hashSpecN N) + (hashSpecN N).randomOracle) oa).run ∅}[
      ∃ t, z.2 t = some y₀] ≤ (q : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ :=
  prEvent_run_le_of_fresh_bound_of_isQueryBoundP (fun c => ∃ t, c t = some y₀) (by simp)
    _ (by simp [NeZero.ne N]) (fun t c hc ht => fresh_hit_le N y₀ t c hc ht) oa h

/-- `2 ^ 64 * (2 ^ 256)⁻¹ < 1`. -/
theorem preimage_bound_lt_one :
    ((2 ^ 64 : ℕ) : ℝ≥0∞) * ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ < 1 := by
  rw [← div_eq_mul_inv, ENNReal.div_lt_iff (by simp) (by simp), one_mul]
  exact_mod_cast Nat.pow_lt_pow_right (by norm_num) (by norm_num)

/-- A computation with private coins making at most `2 ^ 64` queries to a `2 ^ 256`-valued
random oracle caches a fixed output with probability below one. -/
theorem preimage_hit_lt_one {α : Type} (y₀ : Fin (2 ^ 256))
    (oa : OracleComp (unifSpec + hashSpecN (2 ^ 256)) α)
    (h : IsQueryBoundP oa (fun t => t.isRight = true) (2 ^ 64)) :
    Pr{let z ← (simulateQ (unifFwdImpl (hashSpecN (2 ^ 256)) +
      (hashSpecN (2 ^ 256)).randomOracle) oa).run ∅}[∃ t, z.2 t = some y₀] < 1 :=
  (preimage_hit_le (2 ^ 256) y₀ oa h).trans_lt preimage_bound_lt_one

/-- A single public query to a `2`-valued random oracle caches a fixed output with probability
exactly `2⁻¹`, the bound `q * N⁻¹` at `q = 1` and `N = 2`. -/
theorem single_query_hit_eq (y₀ : Fin 2) :
    Pr{let z ← (simulateQ (unifFwdImpl (hashSpecN 2) + (hashSpecN 2).randomOracle)
        (liftM ((unifSpec + hashSpecN 2).query (Sum.inr [])) :
          OracleComp (unifSpec + hashSpecN 2) (Fin 2))).run ∅}[∃ t, z.2 t = some y₀] = 2⁻¹ := by
  have hrun : ((unifFwdImpl (hashSpecN 2) + (hashSpecN 2).randomOracle) (Sum.inr [])).run ∅ =
      (fun u => (u, (∅ : (hashSpecN 2).QueryCache).cacheQuery [] u)) <$>
        ($ᵗ (hashSpecN 2).Range []) :=
    QueryImpl.withCaching_run_none _ rfl
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [hrun, prEvent_map]
  have hset : ∀ u : Fin 2,
      (∃ t, ((∅ : (hashSpecN 2).QueryCache).cacheQuery [] u) t = some y₀) ↔ u = y₀ := by
    intro u
    constructor
    · rintro ⟨t', ht'⟩
      by_cases h : t' = []
      · subst h; simpa using ht'
      · simp [QueryCache.cacheQuery_of_ne _ _ h] at ht'
    · rintro rfl; exact ⟨[], by simp⟩
  simp only [hset]
  rw [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample_singleton]
  simp

end FreshAnswerTest
