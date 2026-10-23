/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Generic transcript extractor for Merkle trees

This module owns the shared extraction recurrence for both unaddressed and addressed Merkle
trees. `QueryView` explains how an oracle query exposes an address key and an ordered pair of
children. `treeAt` reconstructs a partial tree by looking up the first logged query with the
expected address and response, threading the caller's map from typed tree positions to actual
oracle keys.

The unaddressed extractor specializes `Address := Unit`; an addressed extractor supplies its
actual oracle address type. Consequently these are two views of one algorithm, not parallel
implementations. A non-injective position-to-address map is allowed and faithfully models
concrete address encodings that alias.
-/

@[expose] public section

namespace MerkleTreeExtractor

open BinaryTree InductiveMerkleTree

universe u v w

variable {Query : Type u} {Address : Type v} {Y : Type w}

/-- Recover a payload at a reached leaf of a partial digest tree. -/
def recoverLeaf {Payload : Type*} {s : Skeleton} (resolve : Y → Option Payload)
    (t : FullData (Option Y) s) (i : SkeletonLeafIndex s) : Option Payload :=
  (t.get i.toNodeIndex).bind resolve

/-- Projection from an oracle query to the address key and ordered children used by extraction. -/
structure QueryView (Query : Type u) (Address : Type v) (Y : Type w) where
  /-- Actual oracle address/key of the query. -/
  address : Query → Address
  /-- Ordered child labels hashed by the query. -/
  input : Query → Y × Y

/-- A homogeneous query/response log. -/
abbrev QueryLog (Query : Type u) (Y : Type w) := List ((_query : Query) × Y)

/-- The leaf and authentication path exposed by an extracted partial tree at `idx`. -/
structure ExtractedOpening (Y : Type w) {s : Skeleton} (idx : SkeletonLeafIndex s) where
  /-- Extracted leaf, or `none` when the transcript does not reach it. -/
  leaf : Option Y
  /-- Extracted sibling path; unknown siblings are represented by `none`. -/
  proof : List.Vector (Option Y) idx.depth

/-- Inspect the leaf and authentication path extracted at `idx`. -/
def opening {s : Skeleton} (tree : FullData (Option Y) s)
    (idx : SkeletonLeafIndex s) : ExtractedOpening Y idx where
  leaf := tree.get idx.toNodeIndex
  proof := generateProof tree idx

@[simp] theorem opening_leaf {s : Skeleton} (tree : FullData (Option Y) s)
    (idx : SkeletonLeafIndex s) :
    (opening tree idx).leaf = tree.get idx.toNodeIndex := rfl

@[simp] theorem opening_proof {s : Skeleton} (tree : FullData (Option Y) s)
    (idx : SkeletonLeafIndex s) :
    (opening tree idx).proof = generateProof tree idx := rfl

/-- Recover the ordered children of `root` at `address` from the first matching logged query. -/
def children [DecidableEq Address] [DecidableEq Y] (view : QueryView Query Address Y)
    (log : QueryLog Query Y)
    (address : Address) (root : Y) : Option (Y × Y) :=
  match log.find? fun entry => view.address entry.1 == address && entry.2 == root with
  | none => none
  | some entry => some (view.input entry.1)

/-- Reconstruct a partial tree using an address-indexed resolver for child labels. -/
@[simp]
def treeWith (resolve : Address → Y → Option (Y × Y)) : (subtree : Skeleton) →
    (SkeletonInternalIndex subtree → Address) → Y → FullData (Option Y) subtree
  | .leaf, _, root => .leaf (some root)
  | .internal left right, addressKey, root =>
      match resolve (addressKey .ofInternal) root with
      | none =>
          .internal (some root)
            (populateDown left (fun _ : Option Y => (none, none)) none)
            (populateDown right (fun _ : Option Y => (none, none)) none)
      | some (leftRoot, rightRoot) =>
          .internal (some root)
            (treeWith resolve left (fun address => addressKey (.ofLeft address)) leftRoot)
            (treeWith resolve right (fun address => addressKey (.ofRight address)) rightRoot)

/-- The claimed label is retained at the root even when no children are recovered. -/
@[simp]
theorem treeWith_getRootValue (resolve : Address → Y → Option (Y × Y)) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address) (root : Y) :
    (treeWith resolve s addressKey root).getRootValue = some root := by
  cases s <;> simp [treeWith]
  split <;> rfl

/-- Enumerate labels reached by an address-indexed child resolver. -/
def targetsWith (resolve : Address → Y → Option (Y × Y)) : (subtree : Skeleton) →
    (SkeletonInternalIndex subtree → Address) → Y → List Y
  | .leaf, _, root => [root]
  | .internal left right, addressKey, root =>
      root :: match resolve (addressKey .ofInternal) root with
        | none => []
        | some (leftRoot, rightRoot) =>
            targetsWith resolve left (fun address => addressKey (.ofLeft address)) leftRoot ++
              targetsWith resolve right (fun address => addressKey (.ofRight address)) rightRoot

/-- Present labels of a partial tree in root-left-right order. -/
def presentLabels : {s : Skeleton} → FullData (Option Y) s → List Y
  | _, .leaf value => value.toList
  | _, .internal value l r => value.toList ++ (presentLabels l ++ presentLabels r)

/-- An entirely unknown tree contributes no present labels. -/
@[simp]
theorem presentLabels_none (s : Skeleton) :
    presentLabels (populateDown s (fun _ : Option Y => (none, none)) none) = [] := by
  induction s with
  | leaf => rfl
  | internal l r ihl ihr => simp [populateDown, presentLabels, ihl, ihr]

/-- Resolver targets enumerate exactly the labels in the reconstructed partial tree. -/
theorem targetsWith_eq_presentLabels (resolve : Address → Y → Option (Y × Y))
    (s : Skeleton) (addressKey : SkeletonInternalIndex s → Address) (root : Y) :
    targetsWith resolve s addressKey root = presentLabels (treeWith resolve s addressKey root) := by
  induction s generalizing root with
  | leaf => rfl
  | internal l r ihl ihr =>
      simp only [targetsWith, treeWith]
      cases h : resolve (addressKey .ofInternal) root with
      | none => simp [presentLabels]
      | some c =>
          rcases c with ⟨a, b⟩
          simp only [presentLabels, Option.toList_some, List.singleton_append]
          rw [ihl, ihr]

/-- A resolver reaches at most one label per vertex of the skeleton. -/
theorem targetsWith_length_le (resolve : Address → Y → Option (Y × Y)) (subtree : Skeleton)
    (addressKey : SkeletonInternalIndex subtree → Address) (root : Y) :
    (targetsWith resolve subtree addressKey root).length ≤ 2 * subtree.leafCount - 1 := by
  induction subtree generalizing root with
  | leaf => simp [targetsWith]
  | internal left right ihLeft ihRight =>
      simp only [targetsWith, List.length_cons]
      cases hchildren : resolve (addressKey .ofInternal) root with
      | none =>
          simp only [List.length_nil]
          have hl := Skeleton.leafCount_pos left
          have hr := Skeleton.leafCount_pos right
          simp only [Skeleton.leafCount_internal]
          omega
      | some pair =>
          obtain ⟨leftRoot, rightRoot⟩ := pair
          simp only [List.length_append]
          have hl := ihLeft (fun address => addressKey (.ofLeft address)) leftRoot
          have hr := ihRight (fun address => addressKey (.ofRight address)) rightRoot
          have hsl := Skeleton.leafCount_pos left
          have hsr := Skeleton.leafCount_pos right
          simp only [Skeleton.leafCount_internal]
          omega

variable [DecidableEq Address] [DecidableEq Y]

/-- Reconstruct a subtree while mapping each typed internal position to its actual oracle key. -/
def treeAt (view : QueryView Query Address Y) (subtree : Skeleton)
    (addressKey : SkeletonInternalIndex subtree → Address) (log : QueryLog Query Y) (root : Y) :
    FullData (Option Y) subtree :=
  treeWith (children view log) subtree addressKey root

/-- Reconstruct a partial tree from a claimed root and homogeneous oracle log. -/
def tree (view : QueryView Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address) (log : QueryLog Query Y) (root : Y) :
    FullData (Option Y) s :=
  treeAt view s addressKey log root

/-- Enumerate the non-dummy labels reached by the extraction recurrence. -/
def targets (view : QueryView Query Address Y) (subtree : Skeleton)
    (addressKey : SkeletonInternalIndex subtree → Address) (log : QueryLog Query Y) (root : Y) :
    List Y :=
  targetsWith (children view log) subtree addressKey root

/-- Collision-freedom on the finite transcript, in the orientation used by extraction. -/
def ResponseInjectiveOn (log : QueryLog Query Y) : Prop :=
  ∀ entry₁ ∈ log, ∀ entry₂ ∈ log, entry₁.2 = entry₂.2 → entry₁.1 = entry₂.1

/-- Canonical query-chain predicate used by the generic recovery theorem. -/
def ChainInLogAt (view : QueryView Query Address Y) (log : QueryLog Query Y) (leaf : Y) :
    {subtree : Skeleton} →
      (SkeletonInternalIndex subtree → Address) →
      (root : Y) → (idx : SkeletonLeafIndex subtree) →
      List.Vector Y idx.depth → Prop
  | _, _, root, .ofLeaf, _ => leaf = root
  | _, addressKey, root, .ofLeft idx, proof =>
      ∃ query ancestor,
        view.address query = addressKey .ofInternal ∧
        view.input query = (ancestor, proof.head) ∧
        (⟨query, root⟩ : (_query : Query) × Y) ∈ log ∧
        ChainInLogAt view log leaf (fun address => addressKey (.ofLeft address))
          ancestor idx proof.tail
  | _, addressKey, root, .ofRight idx, proof =>
      ∃ query ancestor,
        view.address query = addressKey .ofInternal ∧
        view.input query = (proof.head, ancestor) ∧
        (⟨query, root⟩ : (_query : Query) × Y) ∈ log ∧
        ChainInLogAt view log leaf (fun address => addressKey (.ofRight address))
          ancestor idx proof.tail

@[simp]
theorem treeAt_getRootValue (view : QueryView Query Address Y) (subtree : Skeleton)
    (addressKey : SkeletonInternalIndex subtree → Address)
    (log : QueryLog Query Y) (root : Y) :
    (treeAt view subtree addressKey log root).getRootValue = some root := by
  cases subtree <;> simp [treeAt, treeWith]
  split <;> simp

@[simp]
theorem targets_leaf (view : QueryView Query Address Y)
    (addressKey : SkeletonInternalIndex .leaf → Address)
    (log : QueryLog Query Y) (root : Y) :
    targets view .leaf addressKey log root = [root] := rfl

@[simp]
theorem root_mem_targets (view : QueryView Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : QueryLog Query Y) (root : Y) :
    root ∈ targets view s addressKey log root := by
  cases s <;> simp [targets, targetsWith]

theorem targets_internal_of_children_eq_none (view : QueryView Query Address Y)
    (left right : Skeleton) (addressKey : SkeletonInternalIndex (.internal left right) → Address)
    (log : QueryLog Query Y) (root : Y)
    (hchildren : children view log (addressKey .ofInternal) root = none) :
    targets view (.internal left right) addressKey log root = [root] := by
  simp [targets, targetsWith, hchildren]

theorem targets_internal_of_children_eq_some (view : QueryView Query Address Y)
    (left right : Skeleton) (addressKey : SkeletonInternalIndex (.internal left right) → Address)
    (log : QueryLog Query Y) (root leftRoot rightRoot : Y)
    (hchildren : children view log (addressKey .ofInternal) root = some (leftRoot, rightRoot)) :
    targets view (.internal left right) addressKey log root =
      root ::
        (targets view left (fun address => addressKey (.ofLeft address)) log leftRoot ++
          targets view right (fun address => addressKey (.ofRight address)) log rightRoot) := by
  simp [targets, targetsWith, hchildren]

/-- A full binary skeleton with `L` leaves exposes at most `2L - 1` extractor targets. -/
private theorem targets_length_le_aux (view : QueryView Query Address Y) (subtree : Skeleton)
    (addressKey : SkeletonInternalIndex subtree → Address)
    (log : QueryLog Query Y) (root : Y) :
    (targets view subtree addressKey log root).length ≤ 2 * subtree.leafCount - 1 :=
  targetsWith_length_le (children view log) subtree addressKey root

/-- The public target-list cardinality bound. -/
theorem targets_length_le (view : QueryView Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : QueryLog Query Y) (root : Y) :
    (targets view s addressKey log root).length ≤ 2 * s.leafCount - 1 :=
  targets_length_le_aux view s addressKey log root

/-- A successful child lookup is witnessed by the complete query/response entry selected from
the log. -/
private theorem exists_mem_of_children_eq_some (view : QueryView Query Address Y)
    (log : QueryLog Query Y) (address : Address) (root leftRoot rightRoot : Y)
    (hchildren : children view log address root = some (leftRoot, rightRoot)) :
    ∃ entry ∈ log,
      view.address entry.1 = address ∧ entry.2 = root ∧
        view.input entry.1 = (leftRoot, rightRoot) := by
  unfold children at hchildren
  cases hfind : log.find? (fun entry => view.address entry.1 == address && entry.2 == root) with
  | none => simp [hfind] at hchildren
  | some entry =>
      have hpred := List.find?_some hfind
      have hmem := List.mem_of_find?_eq_some hfind
      simp only [hfind, Option.some.injEq] at hchildren
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      exact ⟨entry, hmem, hpred.1, hpred.2, hchildren⟩

/-- Every extractor target is the claimed root or one component of a complete logged query. -/
private theorem mem_targets_root_or_log_input_aux (view : QueryView Query Address Y)
    (subtree : Skeleton) (addressKey : SkeletonInternalIndex subtree → Address)
    (log : QueryLog Query Y) (root : Y) {target : Y}
    (htarget : target ∈ targets view subtree addressKey log root) :
    target = root ∨
      ∃ entry ∈ log, target = (view.input entry.1).1 ∨ target = (view.input entry.1).2 := by
  induction subtree generalizing root with
  | leaf =>
      simp only [targets, targetsWith, List.mem_singleton] at htarget
      exact Or.inl htarget
  | internal left right ihLeft ihRight =>
      simp only [targets, targetsWith, List.mem_cons] at htarget
      rcases htarget with hroot | htarget
      · exact Or.inl hroot
      · cases hchildren : children view log (addressKey .ofInternal) root with
        | none => simp [hchildren] at htarget
        | some pair =>
            obtain ⟨leftRoot, rightRoot⟩ := pair
            simp only [hchildren, List.mem_append] at htarget
            obtain ⟨entry, hentry, _, _, hinput⟩ :=
              exists_mem_of_children_eq_some view log (addressKey .ofInternal) root
                leftRoot rightRoot hchildren
            rcases htarget with htarget | htarget
            · rcases ihLeft (fun address => addressKey (.ofLeft address)) leftRoot htarget with
                hroot | hdeeper
              · exact Or.inr ⟨entry, hentry, Or.inl (by rw [hroot, hinput])⟩
              · exact Or.inr hdeeper
            · rcases ihRight (fun address => addressKey (.ofRight address)) rightRoot htarget with
                hroot | hdeeper
              · exact Or.inr ⟨entry, hentry, Or.inr (by rw [hroot, hinput])⟩
              · exact Or.inr hdeeper

/-- Public support characterization for targets reached by extraction. -/
theorem mem_targets_root_or_log_input (view : QueryView Query Address Y)
    (s : Skeleton) (addressKey : SkeletonInternalIndex s → Address)
    (log : QueryLog Query Y) (root : Y) {target : Y}
    (htarget : target ∈ targets view s addressKey log root) :
    target = root ∨
      ∃ entry ∈ log, target = (view.input entry.1).1 ∨ target = (view.input entry.1).2 :=
  mem_targets_root_or_log_input_aux view s addressKey log root htarget

/-- A collision-free matching log entry determines the extractor lookup. -/
theorem children_eq_some_of_mem_of_responseInjectiveOn
    (view : QueryView Query Address Y) (log : QueryLog Query Y)
    (address : Address) (root : Y) (query : Query)
    (haddress : view.address query = address)
    (hmem : (⟨query, root⟩ : (_query : Query) × Y) ∈ log)
    (hinj : ResponseInjectiveOn log) :
    children view log address root = some (view.input query) := by
  unfold children
  cases hfind : log.find? (fun entry => view.address entry.1 == address && entry.2 == root) with
  | none =>
      have hsome :
          (log.find? (fun entry => view.address entry.1 == address && entry.2 == root)).isSome =
            true := by
        rw [List.find?_isSome]
        exact ⟨⟨query, root⟩, hmem, by simp [haddress]⟩
      simp [hfind] at hsome
  | some entry =>
      obtain ⟨foundQuery, response⟩ := entry
      have hpred := List.find?_some hfind
      have hfoundMem : (⟨foundQuery, response⟩ : (_query : Query) × Y) ∈ log :=
        List.mem_of_find?_eq_some hfind
      have hresponse : response = root := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        exact hpred.2
      have hquery : foundQuery = query :=
        hinj ⟨foundQuery, response⟩ hfoundMem ⟨query, root⟩ hmem hresponse
      simp [hquery]

/-- Deterministic recovery from a collision-free query chain. -/
theorem opening_eq_of_chainInLogAt
    (view : QueryView Query Address Y) {subtree : Skeleton}
    (log : QueryLog Query Y) (hinj : ResponseInjectiveOn log)
    (addressKey : SkeletonInternalIndex subtree → Address)
    (root leaf : Y) (idx : SkeletonLeafIndex subtree)
    (proof : List.Vector Y idx.depth)
    (hchain : ChainInLogAt view log leaf addressKey root idx proof) :
    (treeAt view subtree addressKey log root).get idx.toNodeIndex = some leaf ∧
      (generateProof (treeAt view subtree addressKey log root) idx).toList =
        proof.toList.map some := by
  induction idx generalizing root with
  | ofLeaf =>
      simp only [ChainInLogAt] at hchain
      subst root
      constructor
      · rfl
      · simp [generateProof]
  | @ofLeft left right idx ih =>
      obtain ⟨query, ancestor, haddress, hinput, hmem, htail⟩ := hchain
      have hchildren : children view log (addressKey .ofInternal) root =
          some (ancestor, proof.head) := by
        rw [← hinput]
        exact children_eq_some_of_mem_of_responseInjectiveOn view log
          (addressKey .ofInternal) root query haddress hmem hinj
      have hrec := ih (fun address => addressKey (.ofLeft address)) ancestor proof.tail htail
      simp only [treeAt, treeWith, hchildren]
      constructor
      · simpa only [treeAt, SkeletonLeafIndex.toNodeIndex, FullData.get_internal_ofLeft] using
          hrec.1
      · calc
          (generateProof
              (.internal (some root)
                (treeAt view left (fun address => addressKey (.ofLeft address)) log ancestor)
                (treeAt view right (fun address => addressKey (.ofRight address)) log proof.head))
              (.ofLeft idx)).toList =
              some proof.head ::
                (generateProof
                  (treeAt view left (fun address => addressKey (.ofLeft address)) log ancestor)
                  idx).toList := by simp [generateProof, treeAt_getRootValue]
          _ = some proof.head :: proof.tail.toList.map some :=
            congrArg (fun tail => some proof.head :: tail) hrec.2
          _ = proof.toList.map some := by
            rw [← List.map_cons]
            exact congrArg (List.map some)
              (congrArg List.Vector.toList proof.cons_head_tail)
  | @ofRight left right idx ih =>
      obtain ⟨query, ancestor, haddress, hinput, hmem, htail⟩ := hchain
      have hchildren : children view log (addressKey .ofInternal) root =
          some (proof.head, ancestor) := by
        rw [← hinput]
        exact children_eq_some_of_mem_of_responseInjectiveOn view log
          (addressKey .ofInternal) root query haddress hmem hinj
      have hrec := ih (fun address => addressKey (.ofRight address)) ancestor proof.tail htail
      simp only [treeAt, treeWith, hchildren]
      constructor
      · simpa only [treeAt, SkeletonLeafIndex.toNodeIndex, FullData.get_internal_ofRight] using
          hrec.1
      · calc
          (generateProof
              (.internal (some root)
                (treeAt view left (fun address => addressKey (.ofLeft address)) log proof.head)
                (treeAt view right (fun address => addressKey (.ofRight address)) log ancestor))
              (.ofRight idx)).toList =
              some proof.head ::
                (generateProof
                  (treeAt view right (fun address => addressKey (.ofRight address)) log ancestor)
                  idx).toList := by simp [generateProof, treeAt_getRootValue]
          _ = some proof.head :: proof.tail.toList.map some :=
            congrArg (fun tail => some proof.head :: tail) hrec.2
          _ = proof.toList.map some := by
            rw [← List.map_cons]
            exact congrArg (List.map some)
              (congrArg List.Vector.toList proof.cons_head_tail)

end MerkleTreeExtractor
