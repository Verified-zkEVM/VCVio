/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.Algorithms.IndexedChain.Basic
public import Batteries.Data.Fin.Lemmas
import Batteries.Data.List.Lemmas

/-!
# Computable merge and cut witnesses for indexed chains

Finite searches find the first unequal predecessor pair with equal next values. A designated
cut either supplies a predecessor of its selected value or a merge strictly after that cut.
The callback is arbitrary; cryptographic domain embeddings belong to the calling construction.
-/

public section

namespace VCVio.Algorithms.IndexedChain

variable {H : Type*}

/-- Search predecessor offsets in increasing order for a pair that merges on its next call. -/
@[expose] def findMerge [DecidableEq H] (step : Nat → H → H) (start steps : Nat)
    (x y : H) : Option (Fin steps) :=
  Fin.find? fun d => decide (chain step start d x ≠ chain step start d y ∧
    chain step start (d.val + 1) x = chain step start (d.val + 1) y)

/-- Forgetting the finite bound gives the same first witness as an increasing natural scan. -/
theorem findMerge_map_val [DecidableEq H] (step : Nat → H → H) (start steps : Nat)
    (x y : H) :
    (findMerge step start steps x y).map Fin.val =
      (List.range steps).find? (fun d => decide (chain step start d x ≠ chain step start d y ∧
        chain step start (d + 1) x = chain step start (d + 1) y)) := by
  rw [findMerge, Fin.find?_eq_find?_finRange, ← List.map_coe_finRange_eq_range]
  rw [List.find?_map]
  rfl

/-- A returned predecessor offset has distinct values and equal next values. -/
theorem findMerge_sound [DecidableEq H] (step : Nat → H → H) (start steps : Nat)
    (x y : H) {d : Fin steps} (hd : findMerge step start steps x y = some d) :
    chain step start d x ≠ chain step start d y ∧
      chain step start (d.val + 1) x = chain step start (d.val + 1) y := by
  exact of_decide_eq_true (Fin.eq_true_of_find?_eq_some hd)

/-- Unequal starts with equal endpoints meet immediately after some unequal predecessor pair. -/
theorem exists_merge (step : Nat → H → H) (start steps : Nat) (x y : H)
    (hne : x ≠ y) (heq : chain step start steps x = chain step start steps y) :
    ∃ d : Fin steps, chain step start d x ≠ chain step start d y ∧
      chain step start (d.val + 1) x = chain step start (d.val + 1) y := by
  induction steps with
  | zero => exact (hne heq).elim
  | succ steps ih =>
    by_cases hprev : chain step start steps x = chain step start steps y
    · obtain ⟨d, hd⟩ := ih hprev
      exact ⟨⟨d.val, by omega⟩, hd⟩
    · exact ⟨⟨steps, by omega⟩, hprev, heq⟩

/-- The finite merge search succeeds for unequal starts with equal endpoints. -/
theorem findMerge_isSome [DecidableEq H] (step : Nat → H → H) (start steps : Nat)
    (x y : H) (hne : x ≠ y) (heq : chain step start steps x = chain step start steps y) :
    (findMerge step start steps x y).isSome := by
  obtain ⟨d, hd⟩ := exists_merge step start steps x y hne heq
  exact Fin.isSome_find?_of_eq_true (i := d) (decide_eq_true hd)

/-- A merge is a same-position collision, with the first trajectory as its first input. -/
theorem findMerge_step_sound [DecidableEq H] (step : Nat → H → H) (start steps : Nat)
    (x y : H) {d : Fin steps} (hd : findMerge step start steps x y = some d) :
    chain step start d x ≠ chain step start d y ∧
      step (start + d.val) (chain step start d x) =
        step (start + d.val) (chain step start d y) := by
  simpa only [chain_succ] using findMerge_sound step start steps x y hd

/-- A predecessor at the cut, or a merge offset after the cut. The earlier trajectory starts
at position `t`, and the first trajectory starts at the designated position `s`. -/
@[expose] def findCut [DecidableEq H] (step : Nat → H → H) (t s b : Nat) (x y : H) :
    Option (H ⊕ Fin (b - s)) :=
  if chain step t (s - t) y = x then
    some (.inl (chain step t (s - t - 1) y))
  else
    (findMerge step s (b - s) x (chain step t (s - t) y)).map Sum.inr

/-- A returned predecessor hashes at position `s - 1` to the selected value at the cut. -/
theorem findCut_preimage_sound [DecidableEq H] (step : Nat → H → H)
    (t s b : Nat) (x y u : H) (hts : t < s)
    (hu : findCut step t s b x y = some (.inl u)) : step (s - 1) u = x := by
  unfold findCut at hu
  split at hu
  next heq =>
    have hu' : chain step t (s - t - 1) y = u := by simpa using hu
    have hoff : t + (s - t - 1) = s - 1 := by omega
    have hlen : s - t - 1 + 1 = s - t := by omega
    simpa [hoff, hlen, hu', heq] using (chain_succ step t (s - t - 1) y).symm
  next hne => simp at hu

/-- The merge branch keeps the trajectory starting at the selected cut as its first input. -/
theorem findCut_merge_sound [DecidableEq H] (step : Nat → H → H)
    (t s b : Nat) (x y : H) {d : Fin (b - s)}
    (hd : findCut step t s b x y = some (.inr d)) :
    findMerge step s (b - s) x (chain step t (s - t) y) = some d := by
  unfold findCut at hd
  split at hd
  · simp at hd
  · simpa using hd

/-- Equal endpoints after a legal cut force one of the two computed witness branches. -/
theorem findCut_isSome [DecidableEq H] (step : Nat → H → H)
    (t s b : Nat) (x y : H) (hts : t < s) (hsb : s ≤ b)
    (heq : chain step s (b - s) x = chain step t (b - t) y) :
    (findCut step t s b x y).isSome := by
  unfold findCut
  split
  · rfl
  next hne =>
    simp only [Option.isSome_map]
    apply findMerge_isSome step s (b - s) x _ (Ne.symm hne)
    have hcomp := chain_add step t (s - t) (b - s) y
    have hstart : t + (s - t) = s := by omega
    have hlen : s - t + (b - s) = b - t := by omega
    rw [hstart, hlen] at hcomp
    exact heq.trans hcomp

end VCVio.Algorithms.IndexedChain
