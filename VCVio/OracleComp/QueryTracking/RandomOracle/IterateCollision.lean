/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Collisions among the iterates of a random function

`OracleComp.prEvent_iterate_collision_le`: for a uniformly random function `g : α → α` on a finite
type and any start `s`, two of the iterates `s, g s, …, g^[n] s` coincide with probability at most
`n · n / |α|`.

The iterates are the answers of the program that queries the oracle `n` times, each time at its
last answer. If two iterates coincide, the first repeat is a query at a point `t` whose answer is
among the iterates up to the first one equal to `t`, and those iterates do not read the table at
`t`. The fresh-query bound `OracleComp.prEvent_tableQueryLog_bad_le` charges each query the
probability that a fresh uniform answer lands in that list, at most `n / |α|`, so the `n` queries
cost `n · n / |α|`.
-/

public section

open OracleSpec
open scoped ENNReal

namespace OracleComp

variable {α : Type}

/-- Query the oracle `n` times from `x`, each time at the last answer. -/
private def iterateQuery : ℕ → α → OracleComp (OracleSpec.ofFn fun _ : α => α) α
  | 0, x => pure x
  | n + 1, x => liftM ((OracleSpec.ofFn fun _ : α => α).query x) >>= iterateQuery n

private theorem isTotalQueryBound_iterateQuery :
    ∀ (n : ℕ) (x : α), IsTotalQueryBound (iterateQuery n x) n
  | 0, x => isTotalQueryBound_zero_iff.2 ⟨x, rfl⟩
  | n + 1, _ => isTotalQueryBound_query_bind_iff.2
      ⟨Nat.succ_pos n, fun u => isTotalQueryBound_iterateQuery n u⟩

/-- Against the table `g`, `iterateQuery n x` queries `g^[i] x` for every `i < n`. -/
private theorem exists_mem_tableQueryLog_iterateQuery (g : α → α) :
    ∀ (n : ℕ) (x : α) (i : ℕ), i < n → ∃ q ∈ tableQueryLog (iterateQuery n x) g, q.1 = g^[i] x
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, x, 0, _ => ⟨⟨x, g x⟩, by
      rw [iterateQuery, tableQueryLog_query_bind]
      exact List.mem_cons_self, rfl⟩
  | n + 1, x, i + 1, hi => by
    obtain ⟨q, hq, hq1⟩ := exists_mem_tableQueryLog_iterateQuery g n (g x) i (by omega)
    refine ⟨q, ?_, hq1.trans (Function.iterate_succ_apply g i x).symm⟩
    rw [iterateQuery, tableQueryLog_query_bind]
    exact List.mem_cons_of_mem _ hq

section Until

variable [DecidableEq α]

/-- The iterates of `g` from `x`, at most `n` of them, up to and including the first one equal to
`t`. -/
private def iteratesUntil (g : α → α) (t : α) : ℕ → α → List α
  | 0, _ => []
  | n + 1, x => if x = t then [x] else x :: iteratesUntil g t n (g x)

/-- The iterates up to `t` do not read the table at `t`. -/
private theorem iteratesUntil_update (g : α → α) (t u : α) :
    ∀ (n : ℕ) (x : α), iteratesUntil (Function.update g t u) t n x = iteratesUntil g t n x
  | 0, _ => rfl
  | n + 1, x => by
    simp only [iteratesUntil]
    split_ifs with hx
    · rfl
    · rw [Function.update_of_ne hx, iteratesUntil_update g t u n (g x)]

private theorem length_iteratesUntil_le (g : α → α) (t : α) :
    ∀ (n : ℕ) (x : α), (iteratesUntil g t n x).length ≤ n
  | 0, _ => le_rfl
  | n + 1, x => by
    simp only [iteratesUntil]
    split_ifs
    · simp
    · simpa using length_iteratesUntil_le g t n (g x)

/-- An iterate before the first one equal to `t`, or that one, is listed. -/
private theorem iterate_mem_iteratesUntil (g : α → α) (t : α) :
    ∀ (a n : ℕ) (x : α), a < n → (∀ i < a, g^[i] x ≠ t) → g^[a] x ∈ iteratesUntil g t n x
  | _, 0, _, ha, _ => absurd ha (Nat.not_lt_zero _)
  | 0, n + 1, x, _, _ => by
    simp only [iteratesUntil]
    split_ifs <;> simp
  | a + 1, n + 1, x, ha, hne => by
    have hx : x ≠ t := hne 0 (Nat.succ_pos a)
    simp only [iteratesUntil, hx, ↓reduceIte]
    rw [Function.iterate_succ_apply]
    refine List.mem_cons_of_mem _ (iterate_mem_iteratesUntil g t a n (g x) (by omega)
      fun i hi => ?_)
    rw [← Function.iterate_succ_apply]
    exact hne (i + 1) (by omega)

/-- If two iterates up to `g^[n] s` coincide, some query of `iterateQuery n s`, at a point `t`, is
answered by an iterate up to the first one equal to `t`. -/
private theorem exists_bad_query_of_iterate_eq (g : α → α) (s : α) (n : ℕ)
    (h : ∃ a b, a < b ∧ b ≤ n ∧ g^[a] s = g^[b] s) :
    ∃ q ∈ tableQueryLog (iterateQuery n s) g, g q.1 ∈ iteratesUntil g q.1 n s := by
  classical
  obtain ⟨a, b, hab, hbn, he⟩ := h
  have hP : ∃ m, ∃ a < m, g^[a] s = g^[m] s := ⟨b, a, hab, he⟩
  obtain ⟨a', ha', he'⟩ := Nat.find_spec hP
  have hmin : ∀ m, (∃ a < m, g^[a] s = g^[m] s) → Nat.find hP ≤ m := fun m hm => Nat.find_min' hP hm
  have hmb : Nat.find hP ≤ b := hmin b ⟨a, hab, he⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hP = k + 1 := ⟨Nat.find hP - 1, by omega⟩
  obtain ⟨q, hq, hq1⟩ := exists_mem_tableQueryLog_iterateQuery g n s k (by omega)
  refine ⟨q, hq, ?_⟩
  have hm : g (g^[k] s) = g^[a'] s := by
    rw [he', hk]
    exact (Function.iterate_succ_apply' g k s).symm
  rw [hq1, hm]
  refine iterate_mem_iteratesUntil g _ a' n s (by omega) fun i hi hik => ?_
  have := hmin k ⟨i, by omega, hik⟩
  omega

end Until

/-- **Iterates of a uniform function collide rarely.** For a uniformly random `g : α → α` and any
start `s`, two of the iterates `s, g s, …, g^[n] s` coincide with probability at most
`n · n / |α|`. -/
theorem prEvent_iterate_collision_le [SampleableType α] [SampleableType (α → α)] (s : α)
    (n : ℕ) :
    Pr{let g ← $ᵗ (α → α)}[∃ a b, a < b ∧ b ≤ n ∧ g^[a] s = g^[b] s] ≤
      n * (n / Nat.card α) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  refine (prEvent_mono _ _ _ fun g => exists_bad_query_of_iterate_eq g s n).trans
    (prEvent_tableQueryLog_bad_le (R := fun _ : α => α) (iterateQuery n s) n
      (isTotalQueryBound_iterateQuery n s) (fun t g => g t ∈ iteratesUntil g t n s) _
      fun t g => ?_)
  simp only [Function.update_self, iteratesUntil_update]
  rw [Nat.card_eq_fintype_card]
  exact (SampleableType.prEvent_uniformSample_mem_le _).trans
    (ENNReal.div_le_div_right (Nat.cast_le.2 (length_iteratesUntil_le g t n s)) _)

end OracleComp
