/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# First-accepted queries with warm cache entries
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace VCVioTest.RandomOracleAcceptedScan

/-- A cached rejection consumes the first trial and the second trial uses a fresh bit. -/
theorem warm_reject_then_cold :
    let cache : QueryCache (Nat →ₒ Bool) :=
      QueryCache.ofFn fun i => if i = 0 then some false else none
    Pr{let z ← (simulateQ randomOracle (AcceptedScan.scan {true} id [0, 1])).run cache}[
      z.1 = some 1] = (1 : ℝ≥0∞) / 2 := by
  intro cache
  rw [AcceptedScan.probability_eq_fold ({true} : Finset Bool) id [0, 1] (by decide) cache 1]
  simp only [List.foldr_cons, List.foldr_nil, cache, QueryCache.ofFn_apply, id_eq]
  rw [AcceptedScan.acceptanceProbability_eq_card]
  norm_num

/-- A single cold trial always accepts, but its retained answer is true only half the time. -/
theorem retained_bit :
    Pr{let z ← (simulateQ randomOracle
      (AcceptedScan.scanWithAnswer (Finset.univ : Finset Bool) id [0])).run ∅}[
        z.1 = some (0, true)] = (1 : ℝ≥0∞) / 2 := by
  rw [AcceptedScan.prEvent_scanWithAnswer (Finset.univ : Finset Bool) id [0] (by decide) ∅
    (fun r => r = some (0, true))]
  simp [AcceptedScan.answerProbability, -SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card]

/-- A uniform cyclic start selects the first cached valid position with probability three quarters.
Starts zero, two and three select zero; start one selects one.
-/
theorem warm_cache_bias :
    let accepted : Finset (Fin 3) := {0, 1}
    let cache : QueryCache (Fin 4 →ₒ Fin 3) := QueryCache.ofFn fun a =>
      some (if a = 0 then 0 else if a = 1 then 1 else 2)
    let schedule (start : Fin 4) := List.ofFn fun offset : Fin 4 =>
      (⟨(start.val + offset.val) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)
    Pr{let start ← $ᵗ Fin 4
       let z ← (simulateQ randomOracle (AcceptedScan.scan accepted id (schedule start))).run
         cache}[z.1 = some 0] = (3 : ℝ≥0∞) / 4 := by
  let accepted : Finset (Fin 3) := {0, 1}
  let cache : QueryCache (Fin 4 →ₒ Fin 3) := QueryCache.ofFn fun a =>
    some (if a = 0 then 0 else if a = 1 then 1 else 2)
  let schedule (start : Fin 4) := List.ofFn fun offset : Fin 4 =>
    (⟨(start.val + offset.val) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)
  change Pr{let z ← ($ᵗ Fin 4) >>= fun start =>
    (simulateQ randomOracle (AcceptedScan.scan accepted id (schedule start))).run cache}[
      z.1 = some 0] = _
  have distinct (start : Fin 4) : ((schedule start).map id).Nodup := by
    fin_cases start <;> decide
  have each (start : Fin 4) :
      Pr{let z ← (simulateQ randomOracle (AcceptedScan.scan accepted id (schedule start))).run
          cache}[z.1 = some (0 : Fin 4)] =
      (schedule start).foldr (fun x tail => match cache x with
        | some y => if y ∈ accepted then (if x = 0 then 1 else 0) else tail
        | none => (Pr{let y ← $ᵗ Fin 3}[y ∈ accepted]) * (if x = 0 then 1 else 0) +
            (1 - (Pr{let y ← $ᵗ Fin 3}[y ∈ accepted])) * tail) 0 :=
    AcceptedScan.probability_eq_fold accepted id (schedule start) (distinct start) cache 0
  rw [prEvent_bind_eq_sum_fintype]
  simp_rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard, each]
  norm_num [Fin.sum_univ_succ, schedule, cache, QueryCache.ofFn_apply, accepted,
    List.ofFn_succ, ENNReal.div_eq_inv_mul]
  rw [show (3 : ℝ≥0∞) = 1 + 1 + 1 by norm_num]
  simp only [mul_add, mul_one, add_assoc]

end VCVioTest.RandomOracleAcceptedScan
