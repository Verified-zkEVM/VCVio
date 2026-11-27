/-
Copyright (c) 2026 leanEthereum and VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: leanEthereum, VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Sum

/-!
# A cache-aware first-accepted scan

The program tests an ordered list of positions through one lazy random oracle.
An occupied address returns its stored answer. A fresh address returns a uniform answer.
The recurrence gives the probability of any event on the returned position and full answer.

The law requires distinct encoded positions in this scan.
The event can also observe exhaustion of the schedule.
The proof follows the scan argument in leanerVM's `lean_xmss/XmssSecurity/Scan/Selection.lean`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp.AcceptedScan

variable {A X Y : Type} [DecidableEq Y]

/-- Return the first accepted position and its answer without issuing a second query. -/
@[expose] def scanWithAnswer (accepted : Finset Y) (encode : X → A) :
    List X → OracleComp (A →ₒ Y) (Option (X × Y))
  | [] => pure none
  | x :: xs => do
    let y ← liftM ((A →ₒ Y).query (encode x))
    if y ∈ accepted then pure (some (x, y)) else scanWithAnswer accepted encode xs

/-- Observe only the selected position of the same free-oracle program. -/
@[expose] def scan (accepted : Finset Y) (encode : X → A) (xs : List X) :
    OracleComp (A →ₒ Y) (Option X) :=
  Option.map Prod.fst <$> scanWithAnswer accepted encode xs

/-- An empty schedule returns no selection. -/
@[simp] theorem scan_nil (accepted : Finset Y) (encode : X → A) :
    scan accepted encode [] = pure none := by simp [scan, scanWithAnswer]

/-- The position view retains the canonical scan's query and stopping order. -/
theorem scan_cons (accepted : Finset Y) (encode : X → A) (x : X) (xs : List X) :
    scan accepted encode (x :: xs) = (do
      let y ← liftM ((A →ₒ Y).query (encode x))
      if y ∈ accepted then pure (some x) else scan accepted encode xs) := by
  simp only [scan, scanWithAnswer, map_bind]
  apply bind_congr
  intro y
  by_cases hy : y ∈ accepted <;> simp [hy]

variable [SampleableType Y]

omit [DecidableEq Y] in
/-- Uniform acceptance is the accepted fraction of the answer alphabet. -/
theorem acceptanceProbability_eq_card [Fintype Y] (accepted : Finset Y) :
    Pr{let y ← $ᵗ Y}[y ∈ accepted] = accepted.card / (Fintype.card Y : ℝ≥0∞) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have h : Finset.univ.filter (fun y : Y => y ∈ accepted) = accepted := by ext; simp
  rw [h]

open scoped Classical in
/-- Evaluate an event on the returned position and full answer using the initial table. -/
@[expose] noncomputable def answerProbability (accepted : Finset Y) (encode : X → A)
    (cache : QueryCache (A →ₒ Y)) (event : Option (X × Y) → Prop) (xs : List X) : ℝ≥0∞ :=
  xs.foldr (fun x tail => match cache (encode x) with
    | some y => if y ∈ accepted then (if event (some (x, y)) then 1 else 0) else tail
    | none => Pr{let y ← $ᵗ Y}[y ∈ accepted ∧ event (some (x, y))] +
        Pr{let y ← $ᵗ Y}[y ∉ accepted] * tail) (if event none then 1 else 0)

private theorem answerProbability_congr (accepted : Finset Y) (encode : X → A)
    (c d : QueryCache (A →ₒ Y)) (event : Option (X × Y) → Prop) (xs : List X)
    (agree : ∀ x ∈ xs, c (encode x) = d (encode x)) :
    answerProbability accepted encode c event xs =
      answerProbability accepted encode d event xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [answerProbability, List.foldr_cons]
    rw [agree x (by simp)]
    have tail := ih (fun x hx => agree x (by simp [hx]))
    unfold answerProbability at tail
    rw [tail]

variable [DecidableEq A]

/-- When the encoded positions are distinct, the fold over the initial cache gives the exact
probability of an event on the first accepted position and answer, including exhaustion. -/
theorem prEvent_scanWithAnswer (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (cache : QueryCache (A →ₒ Y))
    (event : Option (X × Y) → Prop) :
    Pr{let z ← (simulateQ randomOracle (scanWithAnswer accepted encode xs)).run cache}[event z.1] =
      answerProbability accepted encode cache event xs := by
  classical
  induction xs generalizing cache with
  | nil => simp [scanWithAnswer, answerProbability]
  | cons x xs ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp distinct
    simp only [scanWithAnswer, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    cases hc : cache (encode x) with
    | some y =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
      by_cases valid : y ∈ accepted
      · simp [valid, answerProbability, hc]
      · simpa [valid, answerProbability, hc] using ih rest cache
    | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      simp only [uniformSampleImpl]
      erw [bind_map_left]
      rw [OracleComp.prEvent_bind_eq_tsum]
      simp only [answerProbability, List.foldr_cons, hc]
      change _ = Pr{let y ← $ᵗ Y}[y ∈ accepted ∧ event (some (x, y))] +
        Pr{let y ← $ᵗ Y}[y ∉ accepted] * answerProbability accepted encode cache event xs
      rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite,
        ← ENNReal.tsum_mul_right, ← tsum_add]
      apply tsum_congr
      intro y
      by_cases valid : y ∈ accepted
      · by_cases hit : event (some (x, y)) <;> simp [valid, hit]
      · have outside := answerProbability_congr accepted encode
            (cache.cacheQuery (encode x) y) cache event xs (fun z hz =>
              QueryCache.cacheQuery_of_ne cache y fun heq =>
                fresh (List.mem_map.mpr ⟨z, hz, heq⟩))
        simp only [valid, ↓reduceIte, false_and, not_false_eq_true, zero_add]
        rw [ih rest, outside]

/-- Specializing the answer law to one target gives its probability of selection. -/
theorem probability_eq_fold [DecidableEq X] (accepted : Finset Y) (encode : X → A) (xs : List X)
    (hnodup : (xs.map encode).Nodup) (cache : QueryCache (A →ₒ Y)) (target : X) :
    Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run cache}[
      z.1 = some target] =
      xs.foldr (fun x tail => match cache (encode x) with
      | some y => if y ∈ accepted then (if x = target then 1 else 0) else tail
      | none => (Pr{let y ← $ᵗ Y}[y ∈ accepted]) * (if x = target then 1 else 0) +
          (1 - (Pr{let y ← $ᵗ Y}[y ∈ accepted])) * tail) 0 := by
  let event (r : Option (X × Y)) := r.map Prod.fst = some target
  have h := prEvent_scanWithAnswer accepted encode xs hnodup cache event
  simp only [scan, simulateQ_map, StateT.run_map, prEvent_norm]
  change Pr{let z ← (simulateQ randomOracle (scanWithAnswer accepted encode xs)).run cache}[
    event z.1] = _
  rw [h]
  clear h hnodup
  unfold answerProbability
  induction xs with
  | nil => simp [event]
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [ih]
    cases cache (encode x) with
    | some w =>
      by_cases ok : w ∈ accepted <;> by_cases atTarget : x = target <;> simp [ok, event, atTarget]
    | none =>
      by_cases atTarget : x = target <;> simp [event, atTarget, prEvent_not_eq_one_sub]

/-- A finder event depends only on the initial cache entries in its own query schedule. -/
theorem selection_congr (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c d : QueryCache (A →ₒ Y)) (event : Option X → Prop)
    (agree : ∀ x ∈ xs, c (encode x) = d (encode x)) :
    Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run c}[event z.1] =
      Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run d}[event z.1] := by
  let E (o : Option (X × Y)) := event (o.map Prod.fst)
  simp only [scan, simulateQ_map, StateT.run_map, prEvent_norm]
  exact (prEvent_scanWithAnswer accepted encode xs distinct c E).trans
    ((answerProbability_congr accepted encode c d E xs agree).trans
      (prEvent_scanWithAnswer accepted encode xs distinct d E).symm)

end OracleComp.AcceptedScan
