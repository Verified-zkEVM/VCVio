/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.Algorithms.ComplementaryChecksum.Basic
public import VCVio.Algorithms.RadixEncoding

/-!
# Complementary-checksum decoder regressions

Both endian conventions reconstruct the same checksum but place its decreasing coordinate at
different positions. Leading zeroes and a nonsymmetric radix-4 example distinguish the layouts.
-/

public section

namespace VCVioTest.ComplementaryChecksum

open VCVio.Algorithms
open VCVio.Algorithms.RadixEncoding

/-- A radix-4 checksum word with two big-endian checksum digits. -/
@[expose] def wordBE (payload : List ℕ) : List ℕ :=
  ComplementaryChecksum.append (fun n => digitsOfBaseW n 4 2) 4 payload

/-- A radix-4 checksum word using the padded little-endian representation. -/
@[expose] def wordLE (payload : List ℕ) : List ℕ :=
  ComplementaryChecksum.append (Nat.digitsAppend 4 2) 4 payload

example : digitsOfBaseW 22 4 3 = [1, 1, 2] := by decide
example : digitsOfBaseW 22 4 4 = [0, 1, 1, 2] := by decide
example : Nat.digitsAppend 4 4 22 = [2, 1, 1, 0] := by
  rw [Nat.digitsAppend_eq_ofFn 4 4 22 (by decide) (by decide)]
  decide
example : digitsOfBaseW 22 4 0 = [] := rfl

/-- The shared big-endian inverse recovers the nonsymmetric three-digit value. -/
theorem big_endian_reconstruct : fromBaseW 4 (digitsOfBaseW 22 4 3) = 22 :=
  fromBaseW_digitsOfBaseW_of_lt 22 4 3 (by decide)

/-- The canonical little-endian inverse recovers the same value. -/
theorem little_endian_reconstruct : Nat.ofDigits 4 (Nat.digitsAppend 4 3 22) = 22 :=
  (Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 4) 3).2 (by decide)

example : wordBE [0, 0] = [0, 0, 1, 2] := by decide
example : wordBE [1, 1] = [1, 1, 1, 0] := by decide
example : wordLE [0, 0] = [0, 0, 2, 1] := by
  change [0, 0] ++ Nat.digitsAppend 4 2 6 = _
  rw [Nat.digitsAppend_eq_ofFn 4 2 6 (by decide) (by decide)]
  decide
example : wordLE [1, 1] = [1, 1, 0, 1] := by
  change [1, 1] ++ Nat.digitsAppend 4 2 4 = _
  rw [Nat.digitsAppend_eq_ofFn 4 2 4 (by decide) (by decide)]
  decide

/-- Advancing both payload digits forces a decrease in the big-endian checksum. -/
theorem big_endian_not_le : ¬ List.Forall₂ (· ≤ ·) (wordBE [0, 0]) (wordBE [1, 1]) := by
  intro hle
  have heq := ComplementaryChecksum.eq_of_append_le (base := 4)
    (fun n => digitsOfBaseW n 4 2) (fromBaseW 4)
    (by decide : ([0, 0] : List ℕ).length = ([1, 1] : List ℕ).length)
    (by simp) (by simp) (fun h => fromBaseW_pointwiseLE h) (by decide) (by decide) hle
  exact (by decide : ([0, 0] : List ℕ) ≠ [1, 1]) heq

/-- The decoder-parametric law also forbids advancement in the little-endian layout. -/
theorem little_endian_not_le : ¬ List.Forall₂ (· ≤ ·) (wordLE [0, 0]) (wordLE [1, 1]) := by
  intro hle
  have heq := ComplementaryChecksum.eq_of_append_le (base := 4)
    (Nat.digitsAppend 4 2) (Nat.ofDigits 4)
    (by decide : ([0, 0] : List ℕ).length = ([1, 1] : List ℕ).length)
    (by simp) (by simp) (Nat.ofDigits_le_of_forall₂ 4)
    ((Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 4) 2).2 (by decide))
    ((Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 4) 2).2 (by decide)) hle
  exact (by decide : ([0, 0] : List ℕ) ≠ [1, 1]) heq

end VCVioTest.ComplementaryChecksum
