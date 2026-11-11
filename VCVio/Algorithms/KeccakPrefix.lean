/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.Algorithms.Keccak
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith

/-!
# Prefix consistency of multi-block SHAKE output

The XOF emits a fixed sequence of complete rate blocks followed by a partial block.
Taking a shorter prefix therefore commutes with squeezing, including at and beyond rate
boundaries. This is a deterministic property of the concrete implementation, independent
of any random-oracle game simulation.
-/

public section

namespace VCVio.Algorithms.Keccak

/-- A shorter single-block squeeze is the prefix of a longer squeeze. -/
theorem take_toList_squeeze (s : Array UInt64) {n m : ℕ} (hnm : n ≤ m) :
    (squeeze s m).data.toList.take n = (squeeze s n).data.toList := by
  simp only [squeeze, Array.toList_ofFn]
  apply List.ext_getElem
  · simp [hnm]
  · intro i h₁ h₂
    simp

/-- The first `n` complete blocks are unchanged when more blocks are squeezed. -/
theorem take_toList_squeezeFullBlocks (s : Array UInt64) (rate : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    (squeezeFullBlocks s rate m).2.data.toList.take (n * rate) =
      (squeezeFullBlocks s rate n).2.data.toList := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    simp [squeezeFullBlocks]
  | succ m ih =>
    by_cases hn : n ≤ m
    · simp only [squeezeFullBlocks, ByteArray.data_append, Array.toList_append]
      rw [List.take_append_of_le_length (by
        simpa [Array.length_toList, ByteArray.size_data] using Nat.mul_le_mul_right rate hn)]
      exact ih hn
    · have hn : n = m + 1 := by omega
      subst n
      simp [Array.length_toList, ByteArray.size_data]

/-- Squeezing an XOF to any longer length preserves every shorter prefix. -/
theorem take_toList_squeezeXof (s : Array UInt64) {rate n m : ℕ}
    (hr : 0 < rate) (hnm : n ≤ m) :
    (squeezeXof s rate m).data.toList.take n = (squeezeXof s rate n).data.toList := by
  have hdiv : n / rate ≤ m / rate := Nat.div_le_div_right hnm
  have hnmod := Nat.mod_lt n hr
  have hn : n / rate * rate + n % rate = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n rate
  have hm : m / rate * rate + m % rate = m := by
    simpa [Nat.mul_comm] using Nat.div_add_mod m rate
  have hleft : n / rate * rate ≤ n := by omega
  simp only [squeezeXof, ite_eq_right (Nat.ne_of_gt hr),
    ByteArray.data_append, Array.toList_append]
  by_cases heq : n / rate = m / rate
  · rw [← heq, List.take_append, List.take_of_length_le (by
      simpa [Array.length_toList, ByteArray.size_data] using hleft)]
    have hsub : n - n / rate * rate = n % rate := by omega
    rw [show (squeezeFullBlocks s rate (n / rate)).2.data.toList.length =
      n / rate * rate by simp [Array.length_toList, ByteArray.size_data], hsub]
    congr 1
    apply take_toList_squeeze
    have hm' : n / rate * rate + m % rate = m := by
      simpa only [← heq] using hm
    omega
  · have hnext : n / rate + 1 ≤ m / rate := by omega
    have hshort : n ≤ (n / rate + 1) * rate := by nlinarith
    have hlong : n ≤ m / rate * rate := by nlinarith
    rw [List.take_append_of_le_length (by
      simpa [Array.length_toList, ByteArray.size_data] using hlong)]
    calc
      _ = ((squeezeFullBlocks s rate (m / rate)).2.data.toList.take
          ((n / rate + 1) * rate)).take n := by
        rw [List.take_take, Nat.min_eq_left hshort]
      _ = (squeezeFullBlocks s rate (n / rate + 1)).2.data.toList.take n := by
        rw [take_toList_squeezeFullBlocks s rate hnext]
      _ = _ := by
        simp only [squeezeFullBlocks, ByteArray.data_append, Array.toList_append, List.take_append]
        rw [List.take_of_length_le (by
          simpa [Array.length_toList, ByteArray.size_data] using hleft)]
        have hsub : n - n / rate * rate = n % rate := by omega
        rw [show (squeezeFullBlocks s rate (n / rate)).2.data.toList.length =
          n / rate * rate by simp [Array.length_toList, ByteArray.size_data], hsub]
        rw [take_toList_squeeze _ (Nat.le_of_lt hnmod)]

/-- SHAKE256 prefix consistency at arbitrary output widths. -/
theorem take_toList_shake256 (x : ByteArray) {n m : ℕ} (hnm : n ≤ m) :
    (shake256 x m).data.toList.take n = (shake256 x n).data.toList :=
  take_toList_squeezeXof _ (by decide) hnm

/-- SHAKE128 prefix consistency at arbitrary output widths. -/
theorem take_toList_shake128 (x : ByteArray) {n m : ℕ} (hnm : n ≤ m) :
    (shake128 x m).data.toList.take n = (shake128 x n).data.toList :=
  take_toList_squeezeXof _ (by decide) hnm

end VCVio.Algorithms.Keccak
