/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import VCVio.CryptoFoundations.MerkleTree.Hashing.Encoding
public import ToMathlib.Data.IndexedBinaryTree.Lemmas
public import ToMathlib.Data.IndexedBinaryTree.Perfect

/-!
# Prescribed hash checks along a Merkle path

A labelled opening supplies both the path label and its sibling at every step from the root.
Every expected hash answer is therefore determined before any query is made. The same typed
leaf indices govern reading the opening and forming its checks.
-/

public section

namespace MerkleTreeHashing

open BinaryTree

universe u v
variable {X : Type u} {Y : Type v}

/-- Read path labels and siblings from a partial tree, failing if either is absent. -/
@[expose]
def readPath : {s : Skeleton} → (t : FullData (Option Y) s) →
    (i : SkeletonLeafIndex s) → Option (List.Vector (Y × Y) i.depth)
  | _, _, .ofLeaf => some List.Vector.nil
  | _, .internal _ l r, .ofLeft i => do
      let a ← l.getRootValue
      let b ← r.getRootValue
      let tail ← readPath l i
      pure (List.Vector.cons (a, b) tail)
  | _, .internal _ l r, .ofRight i => do
      let a ← r.getRootValue
      let b ← l.getRootValue
      let tail ← readPath r i
      pure (List.Vector.cons (a, b) tail)

/-- List prescribed node checks followed by the leaf check. -/
@[expose]
def pathIO (node : Y × Y → X) (leaf : X) : {s : Skeleton} →
    (i : SkeletonLeafIndex s) → Y → List.Vector (Y × Y) i.depth → List (X × Y)
  | _, .ofLeaf, root, _ => [(leaf, root)]
  | _, .ofLeft i, root, p =>
      (node p.head, root) :: pathIO node leaf i p.head.1 p.tail
  | _, .ofRight i, root, p =>
      (node p.head.swap, root) :: pathIO node leaf i p.head.1 p.tail

/-- A labelled path prescribes one check per edge and one check for the leaf. -/
theorem length_pathIO (node : Y × Y → X) (leaf : X) {s : Skeleton}
    (i : SkeletonLeafIndex s) (root : Y) (p : List.Vector (Y × Y) i.depth) :
    (pathIO node leaf i root p).length = i.depth + 1 := by
  induction i generalizing root with
  | ofLeaf => rfl
  | ofLeft i ih => simp [pathIO, ih, SkeletonLeafIndex.depth]
  | ofRight i ih => simp [pathIO, ih, SkeletonLeafIndex.depth]

/-- The sibling projection of a successfully read labelled path is the usual Merkle proof. -/
theorem readPath_siblings {s : Skeleton} (t : FullData (Option Y) s)
    (i : SkeletonLeafIndex s) (p : List.Vector (Y × Y) i.depth)
    (h : readPath t i = some p) :
    (InductiveMerkleTree.generateProof t i).toList = p.toList.map (some ∘ Prod.snd) := by
  induction i with
  | ofLeaf =>
      cases t
      simp only [readPath, Option.some.injEq] at h
      subst p
      rfl
  | ofLeft i ih =>
      cases t with
      | internal root l r =>
        simp only [readPath, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, tail, ht, rfl⟩ := h
        simp [InductiveMerkleTree.generateProof, hb, ih l tail ht]
  | ofRight i ih =>
      cases t with
      | internal root l r =>
        simp only [readPath, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, tail, ht, rfl⟩ := h
        simp [InductiveMerkleTree.generateProof, hb, ih r tail ht]

/-- All prescribed pairs of a partial tree, using a supplied root and optional leaf inputs. -/
@[expose]
def treeIO (node : Y × Y → X) : {s : Skeleton} → FullData (Option Y) s →
    (SkeletonLeafIndex s → Option X) → Y → List (X × Y)
  | _, .leaf _, inputs, root => (inputs .ofLeaf).toList.map (·, root)
  | _, .internal _ l r, inputs, root =>
      match l.getRootValue, r.getRootValue with
      | some a, some b => (node (a, b), root) ::
          (treeIO node l (fun i => inputs (.ofLeft i)) a ++
            treeIO node r (fun i => inputs (.ofRight i)) b)
      | _, _ => []

/-- The complete pair list has at most one entry per vertex. -/
theorem length_treeIO_le (node : Y × Y → X) {s : Skeleton} (t : FullData (Option Y) s)
    (inputs : SkeletonLeafIndex s → Option X) (root : Y) :
    (treeIO node t inputs root).length ≤ 2 * s.leafCount - 1 := by
  induction t generalizing root with
  | leaf value =>
      cases inputs .ofLeaf <;> simp [treeIO, Skeleton.leafCount]
  | @internal l r value left right ihl ihr =>
      simp only [treeIO]
      cases hl : left.getRootValue <;> cases hr : right.getRootValue <;>
        simp only [List.length_nil, Nat.zero_le, List.length_cons, List.length_append]
      rename_i a b
      have h₁ := ihl (fun i => inputs (.ofLeft i)) a
      have h₂ := ihr (fun i => inputs (.ofRight i)) b
      have := Skeleton.leafCount_pos l
      have := Skeleton.leafCount_pos r
      simp only [Skeleton.leafCount_internal]
      omega

/-- Every check read along one path occurs in the full pair list of that tree. -/
theorem pathIO_subset_treeIO (node : Y × Y → X) {s : Skeleton} (t : FullData (Option Y) s)
    (inputs : SkeletonLeafIndex s → Option X) (root : Y) (i : SkeletonLeafIndex s)
    (p : List.Vector (Y × Y) i.depth) (h : readPath t i = some p)
    {leaf : X} (hleaf : inputs i = some leaf) :
    ∀ q ∈ pathIO node leaf i root p, q ∈ treeIO node t inputs root := by
  induction i generalizing root with
  | ofLeaf =>
      cases t
      simp only [readPath, Option.some.injEq] at h
      subst p
      simp [pathIO, treeIO, hleaf]
  | ofLeft i ih =>
      cases t with
      | internal value l r =>
        simp only [readPath, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, tail, ht, rfl⟩ := h
        simp only [pathIO, List.Vector.head_cons, List.Vector.tail_cons,
          treeIO, ha, hb, List.mem_cons, List.mem_append]
        intro q hq
        rcases hq with hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl (ih l (fun j => inputs (.ofLeft j)) a tail ht hleaf q hq))
  | ofRight i ih =>
      cases t with
      | internal value l r =>
        simp only [readPath, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, tail, ht, rfl⟩ := h
        simp only [pathIO, List.Vector.head_cons, List.Vector.tail_cons,
          treeIO, ha, hb, List.mem_cons, List.mem_append, Prod.swap_prod_mk]
        intro q hq
        rcases hq with hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inr (ih r (fun j => inputs (.ofRight j)) a tail ht hleaf q hq))

/-- In a consistent partial tree, a present child has a present sibling and parent, and their
labels satisfy the node relation. -/
@[expose]
def PartialTreeConsistent (G : X → Y → Prop) (node : Y × Y → X) :
    {s : Skeleton} → FullData (Option Y) s → Prop
  | _, .leaf _ => True
  | _, .internal root l r =>
      PartialTreeConsistent G node l ∧ PartialTreeConsistent G node r ∧
        (l.getRootValue ≠ none ∨ r.getRootValue ≠ none →
          ∃ u a b, root = some u ∧ l.getRootValue = some a ∧
            r.getRootValue = some b ∧ G (node (a, b)) u)

/-- A present leaf in a consistent tree yields a complete labelled path whose checks hold. -/
theorem PartialTreeConsistent.readPath {G : X → Y → Prop} {node : Y × Y → X}
    {s : Skeleton} {t : FullData (Option Y) s} (hc : PartialTreeConsistent G node t)
    (i : SkeletonLeafIndex s) {a : Y} (ha : t.get i.toNodeIndex = some a)
    {leaf : X} (hleaf : G leaf a) :
    ∃ root p, t.getRootValue = some root ∧ readPath t i = some p ∧
      ∀ q ∈ pathIO node leaf i root p, G q.1 q.2 := by
  induction i with
  | ofLeaf =>
      cases t with
      | leaf value =>
        exact ⟨a, List.Vector.nil, ha, rfl, by simpa [pathIO] using hleaf⟩
  | ofLeft i ih =>
      cases t with
      | internal value l r =>
        obtain ⟨a', p, ha', hp, hchecks⟩ := ih hc.1 ha
        obtain ⟨root, aa, b, hroot, haa, hb, hnode⟩ :=
          hc.2.2 (Or.inl (by simp [ha']))
        rw [ha'] at haa
        cases haa
        refine ⟨root, List.Vector.cons (a', b) p, hroot, ?_, ?_⟩
        · simp [MerkleTreeHashing.readPath, ha', hb, hp]
        · simpa [pathIO] using And.intro hnode hchecks
  | ofRight i ih =>
      cases t with
      | internal value l r =>
        obtain ⟨a', p, ha', hp, hchecks⟩ := ih hc.2.1 ha
        obtain ⟨root, b, aa, hroot, hb, haa, hnode⟩ :=
          hc.2.2 (Or.inr (by simp [ha']))
        rw [ha'] at haa
        cases haa
        refine ⟨root, List.Vector.cons (a', b) p, hroot, ?_, ?_⟩
        · simp [MerkleTreeHashing.readPath, ha', hb, hp]
        · simpa [pathIO] using And.intro hnode hchecks

/-- A tree hashed with a fixed function satisfies all its node equations. -/
theorem partialTreeConsistent_populateUp (node : Y × Y → X) (H : X → Y)
    {s : Skeleton} (leaves : LeafData Y s) :
    PartialTreeConsistent (fun x y => H x = y) node
      ((populateUp leaves (fun a b => H (node (a, b)))).map some) := by
  induction leaves with
  | leaf a => trivial
  | internal l r ihl ihr =>
      refine ⟨ihl, ihr, fun _ => ?_⟩
      exact ⟨_, _, _, rfl, FullData.map_getRootValue _ _, FullData.map_getRootValue _ _, rfl⟩

/-- The entirely unknown tree satisfies every node relation. -/
theorem partialTreeConsistent_none (G : X → Y → Prop) (node : Y × Y → X) (s : Skeleton) :
    PartialTreeConsistent G node (populateDown s (fun _ : Option Y => (none, none)) none) := by
  induction s with
  | leaf => trivial
  | internal l r ihl ihr =>
      refine ⟨ihl, ihr, ?_⟩
      simp

/-- A sound child resolver reconstructs a consistent partial tree on every table. -/
theorem partialTreeConsistent_treeWith (G : X → Y → Prop) (node : Y × Y → X)
    (resolve : Unit → Y → Option (Y × Y))
    (hsound : ∀ u c, resolve () u = some c → G (node c) u) (s : Skeleton) (root : Y) :
    PartialTreeConsistent G node (MerkleTreeExtractor.treeWith resolve s (fun _ => ()) root) := by
  induction s generalizing root with
  | leaf => trivial
  | internal l r ihl ihr =>
      simp only [MerkleTreeExtractor.treeWith]
      cases h : resolve () root with
      | none =>
          refine ⟨partialTreeConsistent_none G node l, partialTreeConsistent_none G node r, ?_⟩
          simp
      | some c =>
          refine ⟨ihl c.1, ihr c.2, fun _ => ⟨root, c.1, c.2, rfl, ?_, ?_, hsound _ _ h⟩⟩ <;>
            exact MerkleTreeExtractor.treeWith_getRootValue _ _ _ _

/-- When a resolver recovers every prescribed node pair, extraction recovers the exact labelled
path and its leaf label. -/
theorem readPath_treeWith_of_checks (node : Y × Y → X) (D : X → Option Y)
    (resolve : Unit → Y → Option (Y × Y))
    (hresolve : ∀ u c, D (node c) = some u → resolve () u = some c)
    {s : Skeleton} (i : SkeletonLeafIndex s) (root : Y)
    (p : List.Vector (Y × Y) i.depth) (leaf : X)
    (hchecks : ∀ q ∈ pathIO node leaf i root p, D q.1 = some q.2) :
    readPath (MerkleTreeExtractor.treeWith resolve s (fun _ => ()) root) i = some p ∧
      ∃ a, (MerkleTreeExtractor.treeWith resolve s (fun _ => ()) root).get i.toNodeIndex =
        some a ∧ D leaf = some a := by
  induction i generalizing root with
  | ofLeaf =>
      have hp : p = List.Vector.nil := List.Vector.eq_nil p
      subst p
      exact ⟨rfl, root, rfl, hchecks (leaf, root) (by simp [pathIO])⟩
  | ofLeft i ih =>
      have hc := hresolve root p.head (hchecks (node p.head, root) (by simp [pathIO]))
      have ht := ih p.head.1 p.tail (fun q hq => hchecks q (by simp [pathIO, hq]))
      simp only [MerkleTreeExtractor.treeWith, hc]
      constructor
      · simp [readPath, MerkleTreeExtractor.treeWith_getRootValue, ht.1]
      · exact ht.2
  | ofRight i ih =>
      have hc := hresolve root p.head.swap
        (hchecks (node p.head.swap, root) (by simp [pathIO]))
      have ht := ih p.head.1 p.tail (fun q hq => hchecks q (by simp [pathIO, hq]))
      simp only [MerkleTreeExtractor.treeWith, hc]
      constructor
      · simp [readPath, MerkleTreeExtractor.treeWith_getRootValue, ht.1]
      · exact ht.2

end MerkleTreeHashing
