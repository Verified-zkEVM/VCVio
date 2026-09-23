/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Fischlin.ExpectedSigningCost
public import VCVioTest.FiatShamirKnowledgeExtraction

/-!
# Expected Fischlin queries with fresh and cached challenges

The actual counter distinguishes empty searches, fresh zero-stopping searches, and repeated
cached queries. Whole-program equations retain the chosen response and the final cache.
-/

public section

open OracleComp OracleSpec Fischlin FiatShamirKnowledgeExtractionTest MeasureTheory
open scoped ENNReal

namespace FischlinExpectedCostTest

/-- A fixed oracle input for a repeated cached challenge. -/
@[expose]
def input : FischlinROInput Unit Bool Bool Unit 1 Unit :=
  ⟨(), (), [false], 0, true, ()⟩

/-- A nonzero cached answer forces both occurrences of the challenge to be inspected. -/
@[expose]
def cache : (fischlinROSpec Unit Bool Bool Unit 1 1 Unit).QueryCache :=
  (∅ : (fischlinROSpec Unit Bool Bool Unit 1 1 Unit).QueryCache).cacheQuery input 1

example : searchQueryCount protocol 1 1 Unit () () () () [false] 0 [] none ∅ = pure 0 := by
  simp [searchQueryCount, searchCostRun_nil]

example : searchExpectedQueries protocol 1 0 Unit () () () () [false] 0
    [false, true] none ∅ = 1 := by
  rw [searchExpectedQueries_eq_sum protocol 1 0 Unit () () () () [false] 0
    [false, true] (by decide) none ∅ (by simp)]
  norm_num [Finset.sum_range_succ]

example : searchExpectedQueries protocol 1 1 Unit () () () () [false] 0
    [false, true] none ∅ = 1 + (2 : ENNReal)⁻¹ := by
  rw [searchExpectedQueries_eq_sum protocol 1 1 Unit () () () () [false] 0
    [false, true] (by decide) none ∅ (by simp)]
  norm_num [Finset.sum_range_succ]

-- The full execution retains its selected candidate and unchanged cache, as well as two calls.
example : searchCostRun protocol 1 1 Unit () () () () [false] 0 [true, true] none cache =
    pure ((some (true, ()), Multiplicative.ofAdd 2), cache) := by
  have hresp (c : Bool) : protocol.respond () () () c = pure () := rfl
  have hcache (r : Unit) : cache ⟨(), (), [false], 0, true, r⟩ = some (1 : Fin 2) := by
    cases r
    exact QueryCache.cacheQuery_self _ _ _
  rw [searchCostRun_cons_cached protocol 1 1 Unit () () () () [false] 0 true [true]
    none cache (fun _ => 1) hcache]
  simp only [hresp, pure_bind]
  norm_num
  rw [searchCostRun_cons_cached protocol 1 1 Unit () () () () [false] 0 true []
    (some (true, (), 1)) cache (fun _ => 1) hcache]
  simp [protocol, searchCostRun_nil]
  rfl

example (ρ b : ℕ) :
    ∫⁻ q, (q : ENNReal) ∂𝒟[signingQueryCount protocol ρ b Unit relation 0 () () ()] =
      ρ * (2 ^ b : ENNReal) * (1 - (1 - (2 ^ b : ENNReal)⁻¹) ^ 2) := by
  simpa only [show FinEnum.card Bool = 2 from rfl] using
    sign_expectedQueries_eq_geometric protocol ρ b Unit relation 0 () () ()

example : ∫⁻ q, (q : ENNReal) ∂𝒟[signingQueryCount protocol 0 1 Unit relation 0 () () ()] =
    0 := by
  rw [sign_expectedQueries_eq_sum]
  simp only [Nat.cast_zero, zero_mul]

example (ρ : ℕ) :
    ∫⁻ q, (q : ENNReal) ∂𝒟[signingQueryCount protocol ρ 0 Unit relation 0 () () ()] = ρ := by
  rw [sign_expectedQueries_eq_sum]
  norm_num [Finset.sum_range_succ, show FinEnum.card Bool = 2 from rfl]

end FischlinExpectedCostTest
