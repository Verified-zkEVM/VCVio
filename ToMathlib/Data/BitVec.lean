/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.BitVec

/-!
# Overwriting a Single Bit of a Bitvector

This file defines `BitVec.overwriteBit i b m`, the bitvector `m` with its `i`-th least
significant bit replaced by `b`, together with its `getLsbD` description and the involution
`(m, b) ↦ (m with bit i overwritten by b, original bit i of m)` on `BitVec n × Bool`.
The involution is the change of variables underlying uniform-distribution splitting
arguments: sampling a uniform bitvector and reading its `i`-th bit is equivalent to
sampling a uniform bit and a uniform bitvector and overwriting the `i`-th bit.
-/

@[expose] public section

namespace BitVec

variable {n : ℕ}

/-- Overwrite the `i`-th least significant bit of `m` with `b`, leaving all other bits
unchanged. Out-of-range positions (`n ≤ i`) leave `m` unmodified. -/
def overwriteBit (i : ℕ) (b : Bool) (m : BitVec n) : BitVec n :=
  if b then m ||| twoPow n i else m &&& ~~~ twoPow n i

@[simp] theorem getLsbD_overwriteBit_self {i : ℕ} (hi : i < n) (b : Bool) (m : BitVec n) :
    (overwriteBit i b m).getLsbD i = b := by
  cases b <;> simp [overwriteBit, hi]

@[simp] theorem getLsbD_overwriteBit_of_ne {i j : ℕ} (h : j ≠ i) (b : Bool) (m : BitVec n) :
    (overwriteBit i b m).getLsbD j = m.getLsbD j := by
  rcases lt_or_ge j n with hj | hj
  · cases b <;> simp [overwriteBit, h, hj]
  · cases b <;> simp [overwriteBit, getLsbD_of_ge _ _ hj]

theorem getLsbD_overwriteBit (i j : ℕ) (b : Bool) (m : BitVec n) :
    (overwriteBit i b m).getLsbD j = if j = i ∧ i < n then b else m.getLsbD j := by
  rcases eq_or_ne j i with rfl | h
  · rcases lt_or_ge j n with hj | hj
    · rw [if_pos ⟨rfl, hj⟩]
      exact getLsbD_overwriteBit_self hj b m
    · cases b <;> simp [overwriteBit, getLsbD_of_ge _ _ hj, Nat.not_lt.mpr hj]
  · simp [h]

/-- Overwriting the same position twice keeps only the outer write. -/
@[simp] theorem overwriteBit_overwriteBit (i : ℕ) (b c : Bool) (m : BitVec n) :
    overwriteBit i c (overwriteBit i b m) = overwriteBit i c m :=
  eq_of_getLsbD_eq_iff.mpr fun j _ => by
    simp only [getLsbD_overwriteBit]
    split <;> simp_all

/-- Overwriting a bit with its current value is the identity. -/
@[simp] theorem overwriteBit_getLsbD_self (i : ℕ) (m : BitVec n) :
    overwriteBit i (m.getLsbD i) m = m :=
  eq_of_getLsbD_eq_iff.mpr fun j _ => by
    rw [getLsbD_overwriteBit]
    split <;> simp_all

/-- Pairing a bitvector with its `i`-th bit while overwriting that bit with the paired
value is an involution on `BitVec n × Bool`. This is the change of variables that splits
a uniform bitvector by the value of its `i`-th bit. -/
theorem involutive_overwriteBit_pair {i : ℕ} (hi : i < n) :
    Function.Involutive fun p : BitVec n × Bool =>
      (overwriteBit i p.2 p.1, p.1.getLsbD i) := by
  rintro ⟨m, b⟩
  simp [getLsbD_overwriteBit_self hi]

end BitVec
