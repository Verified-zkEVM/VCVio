/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.NewPartner
import Mathlib.Tactic.NormNum

/-!
# Selecting the new address of a matching pair

A fresh bit at address zero can match the cached true bit at address one.
Scanning zero first selects the new partner half the time. Scanning one first always stops there.
-/

public section

open OracleComp OracleSpec AcceptedScan
open scoped ENNReal

namespace VCVioTest.RandomOracleScanPartners

/-- Both addresses use the same signing key. -/
def key (_ : Nat) := ()
/-- Only true is a valid digest. -/
def decode (b : Bool) : Option Unit := if b then some () else none
/-- Address one already contains the valid bit. -/
def cache : QueryCache (Nat →ₒ Bool) :=
  QueryCache.ofFn fun i => if i = 1 then some true else none

private theorem partners (v : Bool) :
    randomOracle.Partners.Partner key decode (cache.cacheQuery 0 v) 0 ↔ v = true := by
  rw [randomOracle.Partners.at_probe_iff]
  cases v
  · simp [decode]
  · exact iff_of_true ⟨(), rfl, 1, by decide, rfl, true, rfl, rfl⟩ rfl

/-- The first trial is selected with a partner on exactly one of the two fresh words. -/
theorem first_trial :
    (∑' v, Pr{let u ← $ᵗ Bool}[u = v] *
      Pr{let z ← (simulateQ randomOracle (scan {true} id [0, 1])).run (cache.cacheQuery 0 v)}[
        z.1 = some 0 ∧ randomOracle.Partners.Partner key decode (cache.cacheQuery 0 v) 0]) =
      (1 : ℝ≥0∞) / 2 := by
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [partners, Bool.false_eq_true, and_false, prEvent_false, mul_zero, and_true,
    add_zero]
  rw [probability_eq_fold ({true} : Finset Bool) id [0, 1] (by decide)]
  simp [QueryCache.cacheQuery_self, -SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card]

/-- The older valid trial runs first. A new match at address zero can never be selected. -/
theorem hidden_behind_hit :
    (∑' v, Pr{let u ← $ᵗ Bool}[u = v] *
      Pr{let z ← (simulateQ randomOracle (scan {true} id [1, 0])).run (cache.cacheQuery 0 v)}[
        z.1 = some 0 ∧ randomOracle.Partners.Partner key decode (cache.cacheQuery 0 v) 0]) = 0 := by
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [partners, Bool.false_eq_true, and_false, prEvent_false, mul_zero, and_true,
    add_zero]
  rw [probability_eq_fold ({true} : Finset Bool) id [1, 0] (by decide)]
  simp [cache, QueryCache.ofFn_apply]

end VCVioTest.RandomOracleScanPartners
