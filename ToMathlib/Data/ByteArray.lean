/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module

/-!
# The byte list of a `ByteArray`

`ByteArray.toList` builds its list by an accumulator loop over the indices. This file identifies
that list with the list of the underlying `Array UInt8`, so facts about `ByteArray.data` transfer
to `ByteArray.toList`.
-/

public section

namespace ByteArray

/-- The accumulator loop underlying `ByteArray.toList` reverses its accumulator onto the bytes
from index `i` on. -/
theorem toList_loop_eq (bs : ByteArray) (i : Nat) (acc : List UInt8) :
    toList.loop bs i acc = acc.reverse ++ bs.data.toList.drop i := by
  fun_induction toList.loop bs i acc with
  | case1 i acc h ih =>
      rw [ih]
      have hi : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
      rw [List.drop_eq_getElem_cons hi]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      congr 2
      cases bs with
      | mk bs =>
        change bs[i]! = _
        rw [getElem!_pos bs i (show i < bs.size from h), Array.getElem_toList]
  | case2 i acc h =>
      have : bs.data.toList.length ≤ i := by
        rw [Array.length_toList]; exact Nat.le_of_not_lt h
      rw [List.drop_eq_nil_of_le this]; simp

/-- `ByteArray.toList` lists the bytes of the underlying array. -/
theorem toList_eq_toList_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [toList, toList_loop_eq]; simp

end ByteArray
