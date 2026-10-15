/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.SequenceOps

/-!
# Observation laws for structural primitives

These laws retain partial elements and erroneous source constructors. They
state which source observation is demanded, without an unsound outer-value
eta law for lazy sequences.
-/

public section

namespace Interop.Cryptol

@[simp] theorem Length.checkIndex_indexNat {l : Length} (i : l.Index) :
    l.checkIndex (Length.indexNat i) = some i := by
  cases l with
  | finite n =>
      obtain ⟨i, hi⟩ := i
      simp [Length.checkIndex, Length.indexNat, hi]
  | infinite =>
      change Nat at i
      simp [Length.checkIndex, Length.indexNat, Int.natCast_nonneg]

namespace Semantics

/-- A represented integer index selects its corresponding suspended sequence entry. -/
theorem index_value_indexNat {l : Length} {a : ClosedTy}
    (xs : l.Index → Computation a) (i : l.Index) :
    index (l := l) (a := a) (DomainResult.value xs)
      (DomainResult.value ⟨(Length.indexNat i : Int)⟩) = xs i := by
  rw [index_values, Length.checkIndex_indexNat]

@[simp] theorem indexAt_value {l : Length} {a : ClosedTy}
    (xs : l.Index → Computation a) (i : l.Index) :
    indexAt (DomainResult.value xs) (Length.indexNat i) = xs i := by
  rw [indexAt, index_values, Length.checkIndex_indexNat]

/-- In-range natural indices select precisely the corresponding suspended entry. -/
theorem indexAt_value_nat {n : Nat} {a : ClosedTy} (xs : Fin n → Computation a)
    (i : Nat) (hi : i < n) :
    indexAt (l := .finite n) (a := a) (DomainResult.value xs) (i : Int) = xs ⟨i, hi⟩ :=
  indexAt_value (l := .finite n) xs ⟨i, hi⟩

/-- Integer subtraction agrees with an earlier finite coordinate when its bounds are proved. -/
theorem indexAt_value_sub {n : Nat} {a : ClosedTy} (xs : Fin n → Computation a)
    (i d : Nat) (hd : d ≤ i) (hi : i - d < n) :
    indexAt (l := .finite n) (a := a) (DomainResult.value xs) ((i : Int) - d) =
      xs ⟨i - d, hi⟩ := by
  rw [← Int.ofNat_sub hd]
  exact indexAt_value_nat xs (i - d) hi

/-- A requested prefix element is exactly the corresponding source observation. -/
theorem indexAt_take {a : ClosedTy} (front back : Length)
    (xs : Computation (.seq (front.add back) a)) (i : front.Index) :
    indexAt (take front back xs) (Length.indexNat i) = indexAt xs (Length.indexNat i) := by
  change indexAt (DomainResult.value _) _ = _
  rw [indexAt_value]

/-- Dropping a finite prefix adds its length to the requested index. -/
theorem indexAt_drop {a : ClosedTy} (front : Nat) (back : Length)
    (xs : Computation (.seq ((Length.finite front).add back) a)) (i : back.Index) :
    indexAt (drop front back xs) (Length.indexNat i) =
      indexAt xs ((front : Int) + Length.indexNat i) := by
  change indexAt (DomainResult.value _) _ = _
  rw [indexAt_value]

/-- Reversal changes only the demanded source position. -/
theorem indexAt_reverse {a : ClosedTy} (n : Nat)
    (xs : Computation (.seq (.finite n) a)) (i : Fin n) :
    indexAt (reverse n xs) i.val = indexAt xs ((n : Int) - 1 - i.val) := by
  change indexAt (DomainResult.value _) (Length.indexNat (l := .finite n) i) = _
  exact indexAt_value (l := .finite n) _ i

/-- Splitting suspends both the source and each row until the element is selected. -/
theorem indexAt_split {a : ClosedTy} (parts : Length) (each : Nat)
    (xs : Computation (.seq (parts.mul (.finite each)) a)) (i : parts.Index) (j : Fin each) :
    indexAt (indexAt (split parts each xs) (Length.indexNat i)) j.val =
      indexAt xs ((Length.indexNat i : Int) * each + j.val) := by
  change indexAt (indexAt (DomainResult.value _) (Length.indexNat i))
    (Length.indexNat (l := .finite each) j) = _
  rw [indexAt_value]
  exact indexAt_value _ _

/-- Transposition swaps observations even for partial finite or infinite sources. -/
theorem indexAt_transpose {a : ClosedTy} (rows cols : Length)
    (xs : Computation (.seq rows (.seq cols a))) (r : rows.Index) (c : cols.Index) :
    indexAt (indexAt (transpose rows cols xs) (Length.indexNat c)) (Length.indexNat r) =
      indexAt (indexAt xs (Length.indexNat r)) (Length.indexNat c) := by
  change indexAt (indexAt (DomainResult.value _) (Length.indexNat c)) (Length.indexNat r) = _
  rw [indexAt_value]
  exact indexAt_value _ _

end Semantics

end Interop.Cryptol
