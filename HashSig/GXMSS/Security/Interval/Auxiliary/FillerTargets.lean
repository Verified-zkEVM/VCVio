/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Filler
import all HashSig.GXMSS.Interval.Filler

/-!
# Ordered registration of inactive frontier targets

Registration orders finite addresses by height and index. The traversal, ordering and accepted
indices are private; distinct targets retain their distinct original tree tweaks.
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Row-major code gives increasing height followed by increasing subtree index. -/
private def addressCode {f : Family} {I : Interval h} (n : Target f I) : ℕ :=
  let (height, index) := address n
  height.val * 2 ^ h + index.val

/-- The row-major address code is injective within the fixed finite rectangle. -/
private theorem addressCode_injective (f : Family) (I : Interval h) :
    Function.Injective (addressCode (f := f) (I := I)) := by
  intro a b hab
  apply address_injective f I
  cases ha : address a with
  | mk az ai =>
    cases hb : address b with
    | mk bz bi =>
      have heq : az.val * 2 ^ h + ai.val = bz.val * 2 ^ h + bi.val := by
        simpa only [addressCode, ha, hb] using hab
      have hp : 0 < 2 ^ h := by positivity
      have hz : az.val = bz.val := by
        have hd := congrArg (fun x => x / 2 ^ h) heq
        simpa only [Nat.mul_comm az.val, Nat.mul_comm bz.val, Nat.mul_add_div hp,
          Nat.div_eq_of_lt ai.isLt, Nat.div_eq_of_lt bi.isLt, Nat.add_zero] using hd
      have hi : ai.val = bi.val := by simpa only [hz, Nat.add_left_cancel_iff] using heq
      exact Prod.ext (Fin.ext hz) (Fin.ext hi)

/-- Address order used only to enumerate the targets. -/
private instance (f : Family) (I : Interval h) : LinearOrder (Target f I) :=
  LinearOrder.lift' addressCode (addressCode_injective f I)

/-- Computable traversal in increasing height, then increasing index. -/
private def targetList (f : Family) (I : Interval h) : List (Target f I) :=
  Finset.univ.sort (· ≤ ·)

/-- Every target is registered exactly once. -/
private theorem targetList_nodup (f : Family) (I : Interval h) : (targetList f I).Nodup :=
  Finset.sort_nodup _ _

/-- The traversal covers the entire target subtype. -/
@[simp] private theorem mem_targetList (f : Family) (I : Interval h) (n : Target f I) :
    n ∈ targetList f I := by
  simp [targetList]

/-- Registration follows the numeric row-major address code. -/
private theorem targetList_ordered (f : Family) (I : Interval h) :
    (targetList f I).Pairwise (fun a b => addressCode a ≤ addressCode b) :=
  Finset.pairwise_sort _ _

/-- Traversal length is the exact game capacity. -/
@[simp] private theorem length_targetList (f : Family) (I : Interval h) :
    (targetList f I).length = targetCapacity f I := by
  simp [targetList, targetCapacity]

/-- Accepted registration position of a target. -/
private def targetIndex {f : Family} {I : Interval h} (n : Target f I) : ℕ :=
  (targetList f I).idxOf n

/-- Every registration index is strictly below the exact capacity. -/
private theorem targetIndex_lt {f : Family} {I : Interval h} (n : Target f I) :
    targetIndex n < targetCapacity f I := by
  simpa [targetIndex] using List.idxOf_lt_length_of_mem (mem_targetList f I n)

/-- Accepted-index lookup returns the original target. -/
@[simp] private theorem targetList_getElem_targetIndex {f : Family} {I : Interval h}
    (n : Target f I) : (targetList f I)[targetIndex n]'(by
      simpa using targetIndex_lt n) = n := by
  exact List.getElem_idxOf (by simpa [targetIndex] using targetIndex_lt n)

/-- Registration order is an equivalence between exact targets and accepted indices. -/
private def targetEquiv (f : Family) (I : Interval h) :
    Target f I ≃ Fin (targetCapacity f I) where
  toFun n := ⟨targetIndex n, targetIndex_lt n⟩
  invFun j := (targetList f I)[j.val]'(by simp_all)
  left_inv n := targetList_getElem_targetIndex n
  right_inv j := by
    apply Fin.ext
    exact (targetList_nodup f I).idxOf_getElem j.val (by simp_all)

/-- Distinct targets register distinct original tree tweaks. -/
theorem tweak_injective (P : HashInstance PP T X H h w v) (f : Family) (I : Interval h) :
    Function.Injective (tweak P (f := f) (I := I)) :=
  Function.Injective.comp (Function.Embedding.injective P.treeTweak) (address_injective f I)

/-- No challenge tweak is repeated in registration order. -/
private theorem targetTweaks_nodup (P : HashInstance PP T X H h w v) (f : Family) (I : Interval h) :
    ((targetList f I).map (tweak P)).Nodup :=
  (targetList_nodup f I).map (tweak_injective P f I)

/-- Full-range registration issues no target. -/
@[simp] private theorem targetList_full (f : Family) (h : ℕ) :
    targetList f (Interval.full h) = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  simp

end GXMSS.Interval.Filler
