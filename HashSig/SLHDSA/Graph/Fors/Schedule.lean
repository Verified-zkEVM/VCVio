/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Children
public import HashSig.SLHDSA.Fors
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Sibling

/-! # Actual FORS signing schedules in structural coordinates -/

public section

open PerfectMerkleTree

namespace SLHDSA.Graph.ForsSchedule

variable {p : Params}

/-- The graph cell computed at a natural FORS height and a level-bounded global index. -/
@[expose] def treeNode (key : ForsKey p) (height : Nat) (bound : height ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - height))) : StructuralNode p :=
  .forsTree key ⟨height, by omega⟩ index

/-- Every canonical leaf executes its provider query and then its leaf hash. -/
@[expose] def subtree (key : ForsKey p) :
    (height : Nat) → (bound : height ≤ p.a) →
      Fin (p.k * 2 ^ (p.a - height)) → List (StructuralNode p)
  | 0, _, index =>
      [.forsPrf key ⟨index.val, index.isLt⟩,
        treeNode key 0 (by omega) index]
  | height + 1, bound, index =>
      subtree key height (by omega)
        ⟨2 * index.val, by
          simpa using child_index_lt p.a height p.k (by omega) index 0⟩ ++
      subtree key height (by omega)
        ⟨2 * index.val + 1, by
          simpa using child_index_lt p.a height p.k (by omega) index 1⟩ ++
      [treeNode key (height + 1) bound index]

/-- The sibling of an ancestor stays in the actual global FORS level rectangle. -/
theorem sibling_bound (selected : Fin (p.k * 2 ^ p.a)) (height : Nat)
    (bound : height < p.a) :
    sibling (selected.val / 2 ^ height) < p.k * 2 ^ (p.a - height) := by
  have ancestor : selected.val / 2 ^ height / 2 < p.k * 2 ^ (p.a - height - 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
    convert selected.isLt using 1
    calc
      p.k * 2 ^ (p.a - height - 1) * (2 ^ height * 2) =
          p.k * (2 ^ (p.a - height - 1) * 2 ^ (height + 1)) := by ring
      _ = p.k * 2 ^ p.a := by
        rw [← pow_add, show p.a - height - 1 + (height + 1) = p.a by omega]
  have sameParent := sibling_div_two (selected.val / 2 ^ height)
  rw [show p.a - height = p.a - height - 1 + 1 by omega, pow_succ,
    ← Nat.mul_assoc]
  omega

/-- The authenticating sibling node at an actual height. -/
@[expose] def authentication (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a))
    (height : Fin p.a) : StructuralNode p :=
  treeNode key height.val (by omega)
    ⟨sibling (selected.val / 2 ^ height.val), sibling_bound selected height.val height.isLt⟩

/-- Authentication subtrees execute from the leaf level upward. -/
@[expose] def auth (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a)) :
    (height : Nat) → height ≤ p.a → List (StructuralNode p)
  | 0, _ => []
  | height + 1, bound =>
      auth key selected height (by omega) ++
        subtree key height (by omega)
          ⟨sibling (selected.val / 2 ^ height), sibling_bound selected height (by omega)⟩

/-- The global leaf selected by one actual FORS message digit. -/
@[expose] def selected (md : List Byte) (tree : Fin p.k) : Fin (p.k * 2 ^ p.a) :=
  ⟨tree.val * 2 ^ p.a + forsIdx p md tree.val, by
    have digit := forsIdx_lt p md tree.val
    have positive : 0 < 2 ^ p.a := by positivity
    nlinarith [tree.isLt]⟩

/-- The complete actual component call list, including each selected provider call. -/
@[expose] def signing (key : ForsKey p) (md : List Byte) : List (StructuralNode p) :=
  (List.ofFn fun tree : Fin p.k =>
    .forsPrf key (selected md tree) :: auth key (selected md tree) p.a le_rfl).flatten

/-- Every subtree finishes by writing its root cell. -/
theorem subtree_last (key : ForsKey p) (height : Nat) (bound : height ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - height))) :
    (subtree key height bound index).getLast? = some (treeNode key height bound index) := by
  cases height <;> simp [subtree]

/-- Every subtree computes its root cell, without any width or cache hypothesis. -/
theorem root_mem_subtree (key : ForsKey p) (height : Nat) (bound : height ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - height))) :
    treeNode key height bound index ∈ subtree key height bound index := by
  cases height <;> simp [subtree]

/-- Every returned authentication cell is computed by its exact subtree. -/
theorem authentication_mem_auth (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a))
    (height : Nat) (bound : height ≤ p.a) (level : Fin height) :
    authentication key selected ⟨level.val, by omega⟩ ∈ auth key selected height bound := by
  induction height with
  | zero => exact Fin.elim0 level
  | succ height ih =>
    by_cases lower : level.val < height
    · apply List.mem_append_left
      exact ih (by omega) ⟨level.val, lower⟩
    · apply List.mem_append_right
      rcases level with ⟨level, levelBound⟩
      change ¬ level < height at lower
      have same : level = height := by omega
      subst level
      exact root_mem_subtree key height (by omega)
        ⟨sibling (selected.val / 2 ^ height), sibling_bound selected height (by omega)⟩

/-- Provider calls in a subtree are exactly its descendant leaf interval. -/
theorem prf_mem_subtree_iff (key : ForsKey p) (height : Nat) (bound : height ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - height))) (leaf : Fin (p.k * 2 ^ p.a)) :
    StructuralNode.forsPrf key leaf ∈ subtree key height bound index ↔
      leaf.val / 2 ^ height = index.val := by
  induction height with
  | zero => simp [subtree, treeNode, Fin.ext_iff]
  | succ height ih =>
      simp only [subtree, List.mem_append, ih]
      simp only [treeNode, List.mem_singleton, reduceCtorEq, or_false]
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      omega

/-- Sibling subtrees never query the provider of the selected secret. -/
theorem selected_prf_not_mem_auth (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a))
    (height : Nat) (bound : height ≤ p.a) :
    StructuralNode.forsPrf key selected ∉ auth key selected height bound := by
  induction height with
  | zero => simp [auth]
  | succ height ih =>
      rw [auth, List.mem_append, not_or]
      refine ⟨ih (by omega), ?_⟩
      rw [prf_mem_subtree_iff]
      change selected.val / 2 ^ height ≠ sibling (selected.val / 2 ^ height)
      unfold sibling
      split_ifs <;> omega

/-- Every provider query of an authentication path stays in its selected global tree. -/
theorem prf_mem_auth_block (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a))
    (height : Nat) (bound : height ≤ p.a) (leaf : Fin (p.k * 2 ^ p.a))
    (member : StructuralNode.forsPrf key leaf ∈ auth key selected height bound) :
    leaf.val / 2 ^ p.a = selected.val / 2 ^ p.a := by
  induction height with
  | zero => simp [auth] at member
  | succ height ih =>
      rw [auth, List.mem_append] at member
      rcases member with earlier | current
      · exact ih (by omega) earlier
      · have descendant := (prf_mem_subtree_iff key height (by omega) _ leaf).mp current
        change leaf.val / 2 ^ height = sibling (selected.val / 2 ^ height) at descendant
        calc
          leaf.val / 2 ^ p.a = leaf.val / 2 ^ height / 2 ^ (p.a - height) :=
            div_pow_eq_div_pow_div_pow _ _ _ (by omega)
          _ = sibling (selected.val / 2 ^ height) / 2 ^ (p.a - height) := by rw [descendant]
          _ = selected.val / 2 ^ height / 2 ^ (p.a - height) :=
            sibling_div_pow _ _ (by omega)
          _ = selected.val / 2 ^ p.a := (div_pow_eq_div_pow_div_pow _ _ _ (by omega)).symm

/-- An actual message digit selects a leaf in the original tree, without a digest-size premise. -/
theorem selected_div (md : List Byte) (tree : Fin p.k) :
    (selected md tree).val / 2 ^ p.a = tree.val := by
  change (tree.val * 2 ^ p.a + forsIdx p md tree.val) / 2 ^ p.a = tree.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (forsIdx_lt p md tree.val), Nat.zero_add]

/-- A provider call from a different global tree cannot overwrite an earlier selected secret. -/
theorem selected_prf_not_mem_other_auth (key : ForsKey p) (md : List Byte)
    (left right : Fin p.k) (different : left ≠ right) :
    StructuralNode.forsPrf key (selected md left) ∉
      auth key (selected md right) p.a le_rfl := by
  intro member
  have same := prf_mem_auth_block key (selected md right) p.a le_rfl (selected md left) member
  rw [selected_div, selected_div] at same
  exact different (Fin.ext same)

end SLHDSA.Graph.ForsSchedule
