/-
Copyright (c) 2026 leanEthereum and VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: leanEthereum, VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan

/-!
# Cached selections over a permutation of the starting points

A fresh first query discounts the chance of selecting a later cached target by its rejection rate.
Summing over starting positions leaves the total tail mass unchanged under the permutation.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace OracleComp.AcceptedScan

variable {X A Y : Type}

/-- Visit the starting position and its successive images for the chosen number of steps. -/
@[expose] def orbit (step : Equiv.Perm X) (n : Nat) (x : X) : List X :=
  List.ofFn fun i : Fin n => step^[i.val] x

/-- Removing the first position advances the cyclic schedule by one step. -/
theorem orbit_succ (step : Equiv.Perm X) (n : Nat) (x : X) :
    orbit step (n + 1) x = x :: orbit step n (step x) := by
  simp [orbit, List.ofFn_succ, Function.iterate_succ_apply]

variable [Fintype X] [DecidableEq Y] [SampleableType Y]

/-- The initial positions at which the random oracle already has an answer. -/
@[expose] noncomputable def occupied (encode : X → A) (cache : (A →ₒ Y).QueryCache) : Finset X :=
  Finset.univ.filter fun x => (cache (encode x)).isSome

private def selectedIn (s : Finset X) (answer : Option (X × Y)) : Prop :=
  ∃ x ∈ s, answer.map Prod.fst = some x

private noncomputable def score (accepted : Finset Y) (encode : X → A)
    (cache : (A →ₒ Y).QueryCache) (s : Finset X) (xs : List X) : ℝ≥0∞ :=
  answerProbability accepted encode cache (selectedIn s) xs

open scoped Classical in
private theorem score_cons (accepted : Finset Y) (encode : X → A) (cache : (A →ₒ Y).QueryCache)
    (s : Finset X) (warm : s ⊆ occupied encode cache) (x : X) (xs : List X) :
    score accepted encode cache s (x :: xs) =
      match cache (encode x) with
      | some w => if w ∈ accepted then if x ∈ s then 1 else 0 else score accepted encode cache s xs
      | none => Pr{let y ← $ᵗ Y}[y ∉ accepted] * score accepted encode cache s xs := by
  classical
  cases hx : cache (encode x) with
  | some w => simp [score, answerProbability, hx, selectedIn]
  | none =>
    have skip : x ∉ s := fun h => by simpa [occupied, hx] using warm h
    simp [score, answerProbability, hx, selectedIn, skip]

private theorem score_le_one (accepted : Finset Y) (encode : X → A)
    (cache : (A →ₒ Y).QueryCache) (s : Finset X) (warm : s ⊆ occupied encode cache) :
    ∀ xs, score accepted encode cache s xs ≤ 1
  | [] => by simp [score, answerProbability, selectedIn]
  | x :: xs => by
    have tail := score_le_one accepted encode cache s warm xs
    cases h : cache (encode x) with
    | none =>
      have limited : Pr{let y ← $ᵗ Y}[y ∉ accepted] * score accepted encode cache s xs ≤ 1 :=
        (mul_le_mul' (prEvent_le_one _) tail).trans_eq (one_mul 1)
      simpa only [score_cons accepted encode cache s warm, h] using limited
    | some y =>
      classical
      by_cases yes : y ∈ accepted <;> by_cases good : x ∈ s <;>
        simp [score_cons accepted encode cache s warm, h, yes, good, tail]

variable [DecidableEq A]

/-- Summed over all starting points, selections from an initially occupied target set pay one
acceptance rate per occupied position and one rejection rate per target.

The schedule may stop after any finite horizon for which its physical query keys are distinct. -/
theorem cyclic_selection_mass_le (accepted : Finset Y) (encode : X → A)
    (cache : (A →ₒ Y).QueryCache) (s : Finset X) (warm : s ⊆ occupied encode cache)
    (step : Equiv.Perm X) (n : Nat) (distinct : ∀ r, ((orbit step n r).map encode).Nodup) :
    let p := Pr{let y ← $ᵗ Y}[y ∈ accepted]
    p * ∑ r, Pr{let z ← (simulateQ randomOracle (scan accepted encode (orbit step n r))).run cache}[
      ∃ x ∈ s, z.1 = some x] ≤
      p * (occupied encode cache).card + (1 - p) * s.card := by
  classical
  let p := Pr{let y ← $ᵗ Y}[y ∈ accepted]
  let q := Pr{let y ← $ᵗ Y}[y ∉ accepted]
  have pq : p + q = 1 := by
    simp only [p, q, prEvent_not_eq_one_sub, add_tsub_cancel_of_le (prEvent_le_one _)]
  let B := p * (occupied encode cache).card + q * s.card
  let F := fun k r => score accepted encode cache s (orbit step k r)
  have each (k : Nat) (r : X) :
      F (k + 1) r ≤ q * F k (step r) +
        (if r ∈ occupied encode cache then p else 0) + (if r ∈ s then q else 0) := by
    rw [show F (k+1) r = score accepted encode cache s (r :: orbit step k (step r)) by
      rw [← orbit_succ], score_cons accepted encode cache s warm]
    cases h : cache (encode r) with
    | none =>
      have hn : r ∉ s := fun h₀ => by simpa [occupied, h] using warm h₀
      simp [occupied, h, hn, F, q]
    | some y =>
      have here : r ∈ occupied encode cache := by simp [occupied, h]
      simp only [here, ite_true]
      by_cases ok : y ∈ accepted
      · by_cases target : r ∈ s
        · simp only [ok, target, ite_true]
          calc 1 = p + q := pq.symm
            _ ≤ q * F k (step r) + p + q := by gcongr; exact le_add_self
        · simp [ok, target]
      · simp only [ok, ite_false]
        calc F k (step r) = (q + p) * F k (step r) := by rw [add_comm q p, pq, one_mul]
          _ ≤ q * F k (step r) + p := by
            rw [add_mul]
            gcongr
            simpa using mul_le_mul_right (a := p) (score_le_one accepted encode cache s warm _)
          _ ≤ _ := le_self_add
  have count (a : Finset X) (v : ℝ≥0∞) : (∑ x : X, if x ∈ a then v else 0) = v * a.card := by
    simp [mul_comm]
  have sums : ∀ k, p * ∑ r, F k r ≤ B := by
    intro k
    induction k with
    | zero => simp [F, orbit, score, answerProbability, selectedIn]
    | succ k ih =>
      have next : ∑ r, F (k + 1) r ≤ q * ∑ r, F k r + B := by
        calc _ ≤ _ := Finset.sum_le_sum fun r _ => each k r
             _ = _ := by
               rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
                 Equiv.sum_comp step (F k), count, count]
               simp only [B, add_assoc]
      calc p * ∑ r, F (k + 1) r ≤ p * (q * ∑ r, F k r + B) := by gcongr
           _ = q * (p * ∑ r, F k r) + p * B := by ring
           _ ≤ q * B + p * B := by gcongr
           _ = B := by rw [← add_mul, add_comm q p, pq, one_mul]
  have actual (r : X) :
      Pr{let z ← (simulateQ randomOracle (scan accepted encode (orbit step n r))).run cache}[
        ∃ x ∈ s, z.1 = some x] = F n r := by
    simp only [scan, simulateQ_map, StateT.run_map, prEvent_norm]
    exact prEvent_scanWithAnswer accepted encode _ (distinct r) cache (selectedIn s)
  change p * _ ≤ p * _ + (1 - p) * _
  simpa only [actual, B, q, prEvent_not_eq_one_sub] using sums n

end OracleComp.AcceptedScan
