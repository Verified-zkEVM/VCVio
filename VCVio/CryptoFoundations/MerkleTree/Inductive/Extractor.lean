/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Transcript extractor for inductive Merkle trees

This file contains the pure, executable extraction algorithm used by the Merkle-tree
extractability games. Given a claimed root and the committing phase's hash-query log, the
extractor follows response-to-input links down the existing `Skeleton` and returns a partial
tree `FullData (Option α) s`.

The extractor makes no oracle calls. At a node labelled `a`, `children` selects the first
logged query `(x, y)` whose response is `a`. If no such query exists, `tree` leaves the
corresponding descendants unknown. On collision-free logs, the selected preimage is unique,
so the use of `List.find?` does not introduce an additional choice.

The `targets` function follows the same response-link recurrence and exposes the labels used by
the probability proof to identify the finite set of random-oracle answers that could change the
extracted tree.
-/

@[expose] public section

namespace InductiveMerkleTree

open List OracleSpec BinaryTree

variable {α : Type}

namespace Extractor

variable [DecidableEq α]

/-- Recover the children of `a` from the first logged hash query whose response is `a`. -/
def children (log : (spec α).QueryLog) (a : α) : Option (α × α) :=
  match log.find? (fun ⟨_, response⟩ => response == a) with
  | none => none
  | some ⟨(left, right), _⟩ => some (left, right)

/--
Reconstruct the partial Merkle tree rooted at `root` from a hash-query log.

The root is always present. Descendants are present exactly while the log contains a chain of
queries whose responses match the labels reached from the root.
-/
def tree (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    FullData (Option α) s :=
  optionPopulateDown s (children log) root

/-- The leaf and authentication path exposed by an extracted partial tree at `idx`. -/
structure Opening (α : Type) {s : Skeleton} (idx : SkeletonLeafIndex s) where
  /-- The extracted leaf, or `none` if the transcript does not reach it. -/
  leaf : Option α
  /-- The extracted sibling path; unknown siblings are represented by `none`. -/
  proof : List.Vector (Option α) idx.depth

/-- Inspect the leaf and authentication path extracted at `idx`. -/
def opening {s : Skeleton} (tree : FullData (Option α) s)
    (idx : SkeletonLeafIndex s) : Opening α idx where
  leaf := tree.get idx.toNodeIndex
  proof := generateProof tree idx

/-- The non-dummy labels reached by extraction from `root`. -/
def targets : (s : Skeleton) → (spec α).QueryLog → α → List α
  | .leaf, _, root => [root]
  | .internal left right, log, root =>
      root :: match children log root with
        | none => []
        | some (leftRoot, rightRoot) =>
            targets left log leftRoot ++ targets right log rightRoot

@[simp]
theorem tree_leaf (log : (spec α).QueryLog) (root : α) :
    tree .leaf log root = FullData.leaf (some root) := by
  simp [tree]

@[simp]
theorem tree_getRootValue (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    (tree s log root).getRootValue = some root := by
  simp [tree]

/-- If no logged response equals `a`, extraction cannot recover its children. -/
theorem children_eq_none_of_find?_eq_none (log : (spec α).QueryLog) (a : α)
    (hfind : log.find? (fun ⟨_, response⟩ => response == a) = none) :
    children log a = none := by
  simp [children, hfind]

/-- The internal-node equation when the log does not determine children for `root`. -/
theorem tree_internal_of_children_eq_none (left right : Skeleton)
    (log : (spec α).QueryLog) (root : α) (hchildren : children log root = none) :
    tree (.internal left right) log root =
      FullData.internal (some root)
        (populateDown left (Option.bindPair (children log)) none)
        (populateDown right (Option.bindPair (children log)) none) := by
  simp [tree, optionPopulateDown_internal, hchildren]

/-- The internal-node equation when the log determines children `(x, y)` for `root`. -/
theorem tree_internal_of_children_eq_some (left right : Skeleton)
    (log : (spec α).QueryLog) (root x y : α)
    (hchildren : children log root = some (x, y)) :
    tree (.internal left right) log root =
      FullData.internal (some root) (tree left log x) (tree right log y) := by
  simp [tree, optionPopulateDown_internal, hchildren]
  constructor <;> rfl

@[simp]
theorem targets_leaf (log : (spec α).QueryLog) (root : α) :
    targets .leaf log root = [root] := rfl

@[simp]
theorem root_mem_targets (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    root ∈ targets s log root := by
  cases s <;> simp [targets]

theorem targets_internal_of_children_eq_none (left right : Skeleton)
    (log : (spec α).QueryLog) (root : α) (hchildren : children log root = none) :
    targets (.internal left right) log root = [root] := by
  simp [targets, hchildren]

theorem targets_internal_of_children_eq_some (left right : Skeleton)
    (log : (spec α).QueryLog) (root x y : α)
    (hchildren : children log root = some (x, y)) :
    targets (.internal left right) log root =
      root :: (targets left log x ++ targets right log y) := by
  simp [targets, hchildren]

omit [DecidableEq α] in
@[simp]
theorem opening_leaf {s : Skeleton} (tree : FullData (Option α) s)
    (idx : SkeletonLeafIndex s) :
    (opening tree idx).leaf = tree.get idx.toNodeIndex := rfl

omit [DecidableEq α] in
@[simp]
theorem opening_proof {s : Skeleton} (tree : FullData (Option α) s)
    (idx : SkeletonLeafIndex s) :
    (opening tree idx).proof = generateProof tree idx := rfl

/-- If the first logged preimage of `root` is `(x, y)`, extraction recurses from `x` and `y`. -/
theorem tree_internal_eq_of_find?_eq (left right : Skeleton)
    (log : (spec α).QueryLog) (root x y : α)
    (hfind : log.find? (fun ⟨_, response⟩ => response == root) =
      some ⟨(x, y), root⟩) :
    tree (.internal left right) log root =
      FullData.internal (some root) (tree left log x) (tree right log y) := by
  simp only [tree, optionPopulateDown_internal, children, hfind]
  rfl

/-- A full binary skeleton with `L` leaves exposes at most `2L - 1` extractor targets. -/
theorem targets_length_le (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    (targets s log root).length ≤ 2 * s.leafCount - 1 := by
  induction s generalizing root with
  | leaf => simp [targets]
  | internal left right ihLeft ihRight =>
      simp only [targets, List.length_cons]
      cases hchildren : children log root with
      | none =>
          simp only [List.length_nil]
          have hl := Skeleton.leafCount_pos left
          have hr := Skeleton.leafCount_pos right
          simp only [Skeleton.leafCount_internal]
          omega
      | some children =>
          obtain ⟨leftRoot, rightRoot⟩ := children
          simp only [List.length_append]
          have hl := ihLeft leftRoot
          have hr := ihRight rightRoot
          have hsl := Skeleton.leafCount_pos left
          have hsr := Skeleton.leafCount_pos right
          simp only [Skeleton.leafCount_internal]
          omega

/-- Every extractor target is the claimed root or one component of a logged hash input. -/
theorem mem_targets_root_or_log_input (s : Skeleton) (log : (spec α).QueryLog)
    (root : α) {target : α} (htarget : target ∈ targets s log root) :
    target = root ∨ ∃ entry ∈ log, target = entry.1.1 ∨ target = entry.1.2 := by
  induction s generalizing root with
  | leaf =>
      simp only [targets, List.mem_singleton] at htarget
      exact Or.inl htarget
  | internal left right ihLeft ihRight =>
      simp only [targets, List.mem_cons] at htarget
      rcases htarget with hroot | htarget
      · exact Or.inl hroot
      · cases hchildren : children log root with
        | none => simp [hchildren] at htarget
        | some children =>
            obtain ⟨leftRoot, rightRoot⟩ := children
            simp only [hchildren, List.mem_append] at htarget
            unfold children at hchildren
            cases hfind : log.find? (fun ⟨_, response⟩ => response == root) with
            | none => simp [hfind] at hchildren
            | some entry =>
                obtain ⟨⟨leftRoot', rightRoot'⟩, response⟩ := entry
                simp only [hfind, Option.some.injEq, Prod.mk.injEq] at hchildren
                obtain ⟨hleft, hright⟩ := hchildren
                subst leftRoot'
                subst rightRoot'
                have hentry :
                    (⟨(leftRoot, rightRoot), response⟩ : (_ : α × α) × α) ∈ log :=
                  List.mem_of_find?_eq_some hfind
                rcases htarget with htarget | htarget
                · rcases ihLeft leftRoot htarget with hroot | hdeeper
                  · exact Or.inr ⟨⟨(leftRoot, rightRoot), response⟩, hentry, Or.inl hroot⟩
                  · exact Or.inr hdeeper
                · rcases ihRight rightRoot htarget with hroot | hdeeper
                  · exact Or.inr ⟨⟨(leftRoot, rightRoot), response⟩, hentry, Or.inr hroot⟩
                  · exact Or.inr hdeeper

end Extractor

/-! Legacy names retained so downstream users can migrate to the explicit extractor namespace. -/

/-- Compatibility alias for `Extractor.children`. -/
abbrev extractorChildren [DecidableEq α] := Extractor.children (α := α)

/-- Compatibility alias for `Extractor.tree`. -/
abbrev extractor [DecidableEq α] := Extractor.tree (α := α)

end InductiveMerkleTree
