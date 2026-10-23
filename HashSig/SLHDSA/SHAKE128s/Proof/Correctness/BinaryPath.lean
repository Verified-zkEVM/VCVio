/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import Mathlib.Data.Nat.Bitwise
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-! Ordered authentication paths recover the root of any deterministic binary tree. -/

@[expose] public section

namespace SlhDsaSecurity.Correctness

theorem foldlM_id {α β : Type} (f : α → β → Id α) (initial : α) (items : List β) :
    items.foldlM f initial = items.foldl (fun value item => f value item) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
      simpa only [List.foldlM_cons, List.foldl_cons, bind] using ih (f initial item)

theorem finRange_foldl {α : Type} (size : Nat) (values : Nat → α)
    (step : α → Fin size → α)
    (hstep : ∀ j, step (values j.val) j = values (j.val + 1)) :
    (List.finRange size).foldl step (values 0) = values size := by
  induction size with
  | zero => rfl
  | succ size ih =>
      rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (fun value j => step value j.castSucc) (fun j => hstep j.castSucc)]
      exact hstep (Fin.last size)

theorem parent_reconstruction {α : Type} (nodes : Nat → Nat → α)
    (combine : Nat → Nat → α → α → α)
    (hnodes : ∀ height index, nodes (height + 1) index =
      combine (height + 1) index (nodes height (2 * index)) (nodes height (2 * index + 1)))
    (height index : Nat) :
    (if index % 2 = 0 then
      combine (height + 1) (index / 2) (nodes height index) (nodes height (Nat.xor index 1))
     else
      combine (height + 1) (index / 2) (nodes height (Nat.xor index 1)) (nodes height index)) =
      nodes (height + 1) (index / 2) := by
  rw [hnodes]
  by_cases heven : index % 2 = 0
  · have hxor : Nat.xor index 1 = index + 1 := Nat.xor_one_of_even (Nat.even_iff.mpr heven)
    rw [if_pos heven, hxor]
    have hindex : index = 2 * (index / 2) := by omega
    rw [← hindex]
  · have hodd : index % 2 = 1 := by omega
    have hxor : Nat.xor index 1 = index - 1 := Nat.xor_one_of_odd (Nat.odd_iff.mpr hodd)
    rw [if_neg heven, hxor]
    have hindex : index = 2 * (index / 2) + 1 := by omega
    have hsibling : index - 1 = 2 * (index / 2) := by omega
    rw [hsibling, ← hindex]

theorem div_pow_succ (index height : Nat) :
    index / 2 ^ (height + 1) = (index / 2 ^ height) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem offset_div_pow (tree leaf height level : Nat) (hle : level ≤ height) :
    (tree * 2 ^ height + leaf) / 2 ^ level =
      tree * 2 ^ (height - level) + leaf / 2 ^ level := by
  have hp : 2 ^ height = 2 ^ (height - level) * 2 ^ level := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide))]
  omega

theorem offset_even (tree height level : Nat) (hlt : level < height) :
    (tree * 2 ^ (height - level)) % 2 = 0 := by
  obtain ⟨remaining, hremaining⟩ := Nat.exists_eq_succ_of_ne_zero
    (show height - level ≠ 0 by omega)
  rw [hremaining, pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]

theorem xor_add_even (offset index : Nat) (heven : offset % 2 = 0) :
    Nat.xor (offset + index) 1 = offset + Nat.xor index 1 := by
  have hmod : (offset + index) % 2 = index % 2 := by
    simp [Nat.add_mod, heven]
  by_cases hindex : index % 2 = 0
  · have hleft : Nat.xor (offset + index) 1 = offset + index + 1 :=
      Nat.xor_one_of_even (Nat.even_iff.mpr (hmod.trans hindex))
    have hright : Nat.xor index 1 = index + 1 :=
      Nat.xor_one_of_even (Nat.even_iff.mpr hindex)
    rw [hleft, hright, Nat.add_assoc]
  · have hodd : index % 2 = 1 := by omega
    have hleft : Nat.xor (offset + index) 1 = offset + index - 1 :=
      Nat.xor_one_of_odd (Nat.odd_iff.mpr (hmod.trans hodd))
    have hright : Nat.xor index 1 = index - 1 :=
      Nat.xor_one_of_odd (Nat.odd_iff.mpr hodd)
    rw [hleft, hright]
    omega

/-- The full fold is the actual verifier's increasing-height path traversal. -/
theorem recover_path {α : Type} (nodes : Nat → Nat → α)
    (combine : Nat → Nat → α → α → α)
    (hnodes : ∀ height index, nodes (height + 1) index =
      combine (height + 1) index (nodes height (2 * index)) (nodes height (2 * index + 1)))
    (height index : Nat) :
    (List.finRange height).foldl (fun value j =>
      if index / 2 ^ j.val % 2 = 0 then
        combine (j.val + 1) (index / 2 ^ (j.val + 1)) value
          (nodes j.val (Nat.xor (index / 2 ^ j.val) 1))
      else
        combine (j.val + 1) (index / 2 ^ (j.val + 1))
          (nodes j.val (Nat.xor (index / 2 ^ j.val) 1)) value)
      (nodes 0 index) = nodes height (index / 2 ^ height) := by
  have hzero : nodes 0 index = nodes 0 (index / 2 ^ 0) := by simp
  rw [hzero]
  apply finRange_foldl height (fun j => nodes j (index / 2 ^ j))
  intro j
  simpa only [div_pow_succ] using
    parent_reconstruction nodes combine hnodes j.val (index / 2 ^ j.val)

end SlhDsaSecurity.Correctness
