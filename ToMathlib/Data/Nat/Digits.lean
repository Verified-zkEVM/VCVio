/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD

/-!
# Ordered radix digits

Pointwise comparison of natural digit lists compares their reconstructed values. Reversal
connects the little-endian reconstruction to a big-endian accumulator, and padded digit
coordinates agree with quotient remainders.
-/

public section

namespace Nat

/-- Coordinatewise larger digit lists have larger numerical values at a fixed radix. -/
theorem ofDigits_le_of_forall₂ (b : ℕ) {xs ys : List ℕ}
    (h : List.Forall₂ (· ≤ ·) xs ys) : ofDigits b xs ≤ ofDigits b ys := by
  induction h with
  | nil => rfl
  | @cons _ _ _ _ hxy _ ih =>
    simpa only [ofDigits_cons] using Nat.add_le_add hxy (Nat.mul_le_mul_left b ih)

/-- Reconstructing the reversed list is the big-endian multiply-add fold. -/
theorem ofDigits_reverse_eq_foldl (b : ℕ) (ds : List ℕ) :
    ofDigits b ds.reverse = ds.foldl (fun acc d => acc * b + d) 0 := by
  induction ds using List.reverseRecOn with
  | nil => rfl
  | @append_singleton ds d ih =>
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      ofDigits_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
    simp [Nat.mul_comm, Nat.add_comm]

/-- The padded low-first digit at any coordinate is the corresponding quotient remainder. -/
theorem digitsAppend_getD (b l n i : ℕ) (hb : 1 < b) (hn : n < b ^ l) :
    (digitsAppend b l n).getD i 0 = n / b ^ i % b := by
  let ds := digitsAppend b l n
  have hds := mapsTo_digitsAppend hb l hn
  have hrec : ofDigits b ds = n := (setInvOn_digitsAppend_ofDigits hb l).2 hn
  have hmod : ds.getD i 0 % b = ds.getD i 0 := by
    by_cases hi : i < ds.length
    · exact Nat.mod_eq_of_lt (hds.2 _ (by
        rw [List.getD_eq_getElem ds 0 hi]
        exact List.getElem_mem hi))
    · simp [List.getD_eq_getElem?_getD, Nat.le_of_not_gt hi]
  have hdrop : ds.getD i 0 = (ds.drop i).head! := by
    simp [List.getD_eq_getElem?_getD, List.head!_eq_head?_getD]
  calc
    ds.getD i 0 = ds.getD i 0 % b := hmod.symm
    _ = (ds.drop i).head! % b := by rw [hdrop]
    _ = ofDigits b (ds.drop i) % b := (ofDigits_mod_eq_head! b (ds.drop i)).symm
    _ = n / b ^ i % b := by
      rw [← hrec, ofDigits_div_pow_eq_ofDigits_drop i (by omega : 0 < b) ds hds.2]

/-- Padded digits are the finite tuple of quotient remainders at the prescribed width. -/
theorem digitsAppend_eq_ofFn (b l n : ℕ) (hb : 1 < b) (hn : n < b ^ l) :
    digitsAppend b l n = List.ofFn (fun i : Fin l => n / b ^ i.val % b) := by
  apply List.ext_getElem
  · simp [Nat.length_digitsAppend hb l hn]
  · intro i hi _
    have hc := digitsAppend_getD b l n i hb hn
    rw [List.getD_eq_getElem _ 0 hi] at hc
    simpa only [List.getElem_ofFn] using hc

end Nat
