/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan

/-!
# Selection of an initially occupied valid trial

Placing an accepted word in the cache can stop a search earlier.
If it does, the new stopping point is itself an occupied valid trial.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace OracleComp.AcceptedScan

variable {A X Y : Type} [DecidableEq A] [DecidableEq Y] [SampleableType Y]

/-- The selected position already held an accepted word in the given cache. -/
@[expose] def cachedSelection (accepted : Finset Y) (encode : X → A) (c : QueryCache (A →ₒ Y)) :
    Option (X × Y) → Prop
  | none => False
  | some (x, _) => ∃ y ∈ accepted, c (encode x) = some y

/-- Filling a cache entry with an accepted word can only increase the probability of selecting
an initially occupied position. Each scan uses its own starting cache to test occupancy. -/
theorem cachedSelection_le_of_accepted (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : QueryCache (A →ₒ Y)) (a : A) (v : Y)
    (good : v ∈ accepted) :
    Pr{let z ← (simulateQ randomOracle (scanWithAnswer accepted encode xs)).run c}[
      cachedSelection accepted encode c z.1] ≤
    Pr{let z ← (simulateQ randomOracle (scanWithAnswer accepted encode xs)).run (c.cacheQuery a v)}[
      cachedSelection accepted encode (c.cacheQuery a v) z.1] := by
  classical
  rw [prEvent_scanWithAnswer _ _ _ distinct, prEvent_scanWithAnswer _ _ _ distinct]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases probe : encode x = a
    · have bound : Pr{let z ←
            (simulateQ randomOracle (scanWithAnswer accepted encode (x :: xs))).run c}[
          cachedSelection accepted encode c z.1] ≤ 1 := prEvent_le_one _
      rw [prEvent_scanWithAnswer _ _ _ distinct] at bound
      refine bound.trans_eq ?_
      have filled : (c.cacheQuery a v) (encode x) = some v := by
        rw [probe, QueryCache.cacheQuery_self]
      have stopped : cachedSelection accepted encode (c.cacheQuery a v) (some (x, v)) :=
        ⟨v, good, filled⟩
      simp [answerProbability, filled, good, stopped]
    · have tail := ih (List.nodup_cons.mp distinct).2
      simp only [answerProbability, List.foldr_cons] at tail ⊢
      rw [QueryCache.cacheQuery_of_ne _ _ probe]
      have same (w : Y) : cachedSelection accepted encode (c.cacheQuery a v) (some (x, w)) =
          cachedSelection accepted encode c (some (x, w)) := by
        simp only [cachedSelection, QueryCache.cacheQuery_of_ne _ _ probe]
      cases c (encode x) with
      | some w =>
        by_cases ok : w ∈ accepted
        · simp only [same, ok, reduceIte, le_refl]
        · simpa only [ok, reduceIte] using tail
      | none =>
        simp only [same]
        gcongr

end OracleComp.AcceptedScan
