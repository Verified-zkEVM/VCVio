/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan

/-!
# How a probe changes the probability of selecting a cached position

A search uses an occupied word only to decide whether to stop.
At an address other than the target, an accepted word can only decrease its chance of selection.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace OracleComp.AcceptedScan

variable {A X Y : Type} [DecidableEq A] [DecidableEq Y] [SampleableType Y]

/-- Recording any accepted word at a different address cannot increase the mass on the target.
The schedule may contain other cached hits and cached rejections. -/
theorem select_le_of_probe_accepted (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (cache : QueryCache (A →ₒ Y)) (target : X) (a : A)
    (other : a ≠ encode target) (v : Y) (valid : v ∈ accepted) :
    Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run (cache.cacheQuery a v)}[
      z.1 = some target] ≤
    Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run cache}[
      z.1 = some target] := by
  classical
  rw [probability_eq_fold _ _ _ distinct, probability_eq_fold _ _ _ distinct]
  clear distinct
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    by_cases probe : encode x = a
    · have ne : x ≠ target := fun eq => other (probe.symm.trans (congrArg encode eq))
      rw [show (cache.cacheQuery a v) (encode x) = some v by rw [probe, QueryCache.cacheQuery_self]]
      simp only [valid, ne, ite_true, ite_false]
      exact zero_le
    · rw [QueryCache.cacheQuery_of_ne _ _ probe]
      cases cache (encode x) with
      | some w =>
        by_cases found : w ∈ accepted
        · simp only [found, ite_true, le_refl]
        · simpa only [found, ite_false] using ih
      | none =>
        dsimp only
        gcongr

/-- A fixed target has the same selection probability under any two accepted words at one probe. -/
theorem select_eq_of_probe_accepted (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (cache : QueryCache (A →ₒ Y)) (target : X) (a : A)
    (v w : Y) (hv : v ∈ accepted) (hw : w ∈ accepted) :
    Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run (cache.cacheQuery a v)}[
      z.1 = some target] =
    Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run (cache.cacheQuery a w)}[
      z.1 = some target] := by
  classical
  rw [probability_eq_fold _ _ _ distinct, probability_eq_fold _ _ _ distinct]
  clear distinct
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [ih]
    by_cases probe : encode x = a
    · rw [show (cache.cacheQuery a v) (encode x) = some v by rw [probe, QueryCache.cacheQuery_self],
        show (cache.cacheQuery a w) (encode x) = some w by rw [probe, QueryCache.cacheQuery_self]]
      simp only [hv, hw, ite_true]
    · rw [QueryCache.cacheQuery_of_ne _ _ probe, QueryCache.cacheQuery_of_ne _ _ probe]

end OracleComp.AcceptedScan
