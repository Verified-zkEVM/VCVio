/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.General

/-!
# Callback-Parametric Perfect Merkle Trees

This module implements perfect binary Merkle trees without materializing a full tree. Leaves and
internal nodes are supplied by monadic callbacks. The internal-node callback receives the height
and horizontal index of the node it is producing, which supports the address-dependent hashing
used by hash-based signatures.

`treeHashM` computes a subtree root in depth-first, left-to-right order. `authenticationPathM`
computes only the sibling subtrees on one branch, and `climbM` reconstructs an ancestor from a
length-indexed authentication path. Root-level wrappers use `Fin (2 ^ height)` for leaf indices,
so both out-of-range leaves and wrong-length paths are excluded by their types.

The monadic definitions intentionally make no consistency claim about repeated callback
invocations. For example, a randomized or stateful callback may return different results when
called twice at the same address. Deterministic completeness is therefore stated for the `Id`
specialization (`climb_authenticationPath` and `reconstructRoot_authenticationPath`). A caller that
interprets callbacks as random-oracle queries must provide the shared-oracle semantics needed to
relate separately evaluated computations.
-/

@[expose] public section

namespace PerfectMerkleTree

universe u v

variable {Y : Type u} {m : Type u → Type v}

/-- The address of a perfect-tree node. `height = 0` denotes a leaf; internal-node callbacks are
invoked only at addresses with positive height. -/
structure Address where
  height : ℕ
  index : ℕ
deriving DecidableEq, Repr

/-- An authentication path whose length is fixed by the height it traverses. Entries are ordered
from the queried node upward: the first entry is the node's immediate sibling. -/
abbrev AuthenticationPath (Y : Type u) (height : ℕ) := List.Vector Y height

/-- A leaf index in a perfect tree of the given height. -/
abbrev LeafIndex (height : ℕ) := Fin (2 ^ height)

/-- The sibling of a node index, obtained by flipping its least-significant bit. -/
def sibling (index : ℕ) : ℕ :=
  if index % 2 = 0 then index + 1 else index - 1

/-- Compute the root at `(height, index)` using effectful leaf and internal-node callbacks.

The computation uses stack space proportional to `height` and does not construct a `FullData`
tree. Callback order is depth-first and left-to-right, with each internal-node callback invoked
after both child callbacks finish. -/
def treeHashM [Monad m] (leaf : ℕ → m Y) (nodeHash : Address → Y → Y → m Y) : ℕ → ℕ → m Y
  | 0, index => leaf index
  | height + 1, index => do
      let left ← treeHashM leaf nodeHash height (2 * index)
      let right ← treeHashM leaf nodeHash height (2 * index + 1)
      nodeHash ⟨height + 1, index⟩ left right

/-- Compute the root of a perfect tree of the given height. -/
def rootM [Monad m] (leaf : ℕ → m Y) (nodeHash : Address → Y → Y → m Y)
    (height : ℕ) : m Y :=
  treeHashM leaf nodeHash height 0

/-- Compute a sized authentication path for the node at `(base, index)` through `depth` levels.

Only sibling subtrees are evaluated. In particular, this function neither evaluates the queried
node nor materializes the surrounding tree. -/
def authenticationPathM [Monad m] (leaf : ℕ → m Y) (nodeHash : Address → Y → Y → m Y)
    (base index : ℕ) : (depth : ℕ) → m (AuthenticationPath Y depth)
  | 0 => pure List.Vector.nil
  | depth + 1 => do
      let siblingRoot ← treeHashM leaf nodeHash base (sibling index)
      let rest ← authenticationPathM leaf nodeHash (base + 1) (index / 2) depth
      pure (List.Vector.cons siblingRoot rest)

/-- Fold a sized authentication path upward, using the running node address at every step. -/
def climbM [Monad m] (nodeHash : Address → Y → Y → m Y) (base index : ℕ) :
    (depth : ℕ) → Y → AuthenticationPath Y depth → m Y
  | 0, node, _ => pure node
  | depth + 1, node, path => do
      let parent ←
        if index % 2 = 0 then
          nodeHash ⟨base + 1, index / 2⟩ node path.head
        else
          nodeHash ⟨base + 1, index / 2⟩ path.head node
      climbM nodeHash (base + 1) (index / 2) depth parent path.tail

/-- Generate a root-level authentication path. The index and path length are statically tied to
the tree height. -/
def rootAuthenticationPathM [Monad m] (leaf : ℕ → m Y)
    (nodeHash : Address → Y → Y → m Y) {height : ℕ} (index : LeafIndex height) :
    m (AuthenticationPath Y height) :=
  authenticationPathM leaf nodeHash 0 index.val height

/-- Reconstruct a putative root from a root-level leaf opening. -/
def reconstructRootM [Monad m] (nodeHash : Address → Y → Y → m Y) {height : ℕ}
    (index : LeafIndex height) (leafValue : Y) (path : AuthenticationPath Y height) : m Y :=
  climbM nodeHash 0 index.val height leafValue path

/-! ## Deterministic specialization -/

/-- Deterministic subtree-root computation. Its direct recursion gives pure correctness proofs
useful definitional equations; `treeHashM_id` relates it to the production monadic engine. -/
def treeHash (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y) : ℕ → ℕ → Y
  | 0, index => leaf index
  | height + 1, index =>
      nodeHash ⟨height + 1, index⟩ (treeHash leaf nodeHash height (2 * index))
        (treeHash leaf nodeHash height (2 * index + 1))

/-- Deterministic specialization of `rootM`. -/
def root (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y) (height : ℕ) : Y :=
  treeHash leaf nodeHash height 0

/-- Deterministic authentication-path generation. -/
def authenticationPath (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y)
    (base index : ℕ) : (depth : ℕ) → AuthenticationPath Y depth
  | 0 => List.Vector.nil
  | depth + 1 =>
      List.Vector.cons (treeHash leaf nodeHash base (sibling index))
        (authenticationPath leaf nodeHash (base + 1) (index / 2) depth)

/-- Deterministic authentication-path folding. -/
def climb (nodeHash : Address → Y → Y → Y) (base index : ℕ) :
    (depth : ℕ) → Y → AuthenticationPath Y depth → Y
  | 0, node, _ => node
  | depth + 1, node, path =>
      let parent :=
        if index % 2 = 0 then
          nodeHash ⟨base + 1, index / 2⟩ node path.head
        else
          nodeHash ⟨base + 1, index / 2⟩ path.head node
      climb nodeHash (base + 1) (index / 2) depth parent path.tail

/-- Deterministic root-level authentication-path generation. -/
def rootAuthenticationPath (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y)
    {height : ℕ} (index : LeafIndex height) : AuthenticationPath Y height :=
  authenticationPath leaf nodeHash 0 index.val height

/-- Deterministic root reconstruction. -/
def reconstructRoot (nodeHash : Address → Y → Y → Y) {height : ℕ}
    (index : LeafIndex height) (leafValue : Y) (path : AuthenticationPath Y height) : Y :=
  climb nodeHash 0 index.val height leafValue path

/-! The following parity lemmas justify the deterministic API as the `Id` interpretation of the
monadic production engine. -/

@[simp]
theorem treeHashM_id (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y)
    (height index : ℕ) :
    Id.run (treeHashM (m := Id) leaf nodeHash height index) =
      treeHash leaf nodeHash height index := by
  induction height generalizing index with
  | zero => rfl
  | succ height ih =>
      simp [treeHashM, treeHash, Id.run_bind, ih]
      rfl

@[simp]
theorem rootM_id (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y) (height : ℕ) :
    Id.run (rootM (m := Id) leaf nodeHash height) = root leaf nodeHash height := by
  simp [rootM, root]

@[simp]
theorem authenticationPathM_id (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y)
    (base index depth : ℕ) :
    Id.run (authenticationPathM (m := Id) leaf nodeHash base index depth) =
      authenticationPath leaf nodeHash base index depth := by
  induction depth generalizing base index with
  | zero => rfl
  | succ depth ih => simp [authenticationPathM, authenticationPath, Id.run_bind, ih]

@[simp]
theorem climbM_id (nodeHash : Address → Y → Y → Y) (base index depth : ℕ) (node : Y)
    (path : AuthenticationPath Y depth) :
    Id.run (climbM (m := Id) nodeHash base index depth node path) =
      climb nodeHash base index depth node path := by
  induction depth generalizing base index node with
  | zero => rfl
  | succ depth ih =>
      by_cases h : index % 2 = 0 <;>
        simp [climbM, climb, h, Id.run_bind, ih] <;> rfl

@[simp]
theorem treeHash_zero (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y) (index : ℕ) :
    treeHash leaf nodeHash 0 index = leaf index := rfl

@[simp]
theorem treeHash_succ (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y)
    (height index : ℕ) :
    treeHash leaf nodeHash (height + 1) index =
      nodeHash ⟨height + 1, index⟩ (treeHash leaf nodeHash height (2 * index))
        (treeHash leaf nodeHash height (2 * index + 1)) := rfl

/-- Folding one honest sibling into its node reproduces the deterministic parent subtree root. -/
theorem combineSibling_eq_treeHash (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y)
    (base index : ℕ) :
    (if index % 2 = 0 then
      nodeHash ⟨base + 1, index / 2⟩ (treeHash leaf nodeHash base index)
        (treeHash leaf nodeHash base (sibling index))
    else
      nodeHash ⟨base + 1, index / 2⟩ (treeHash leaf nodeHash base (sibling index))
        (treeHash leaf nodeHash base index)) =
      treeHash leaf nodeHash (base + 1) (index / 2) := by
  have hdm := Nat.div_add_mod index 2
  change _ = nodeHash ⟨base + 1, index / 2⟩
    (treeHash leaf nodeHash base (2 * (index / 2)))
    (treeHash leaf nodeHash base (2 * (index / 2) + 1))
  by_cases h : index % 2 = 0
  · rw [if_pos h, sibling, if_pos h]
    have h1 : 2 * (index / 2) = index := by omega
    rw [h1]
  · rw [if_neg h, sibling, if_neg h]
    have h2 : 2 * (index / 2) = index - 1 := by omega
    have h3 : 2 * (index / 2) + 1 = index := by omega
    rw [h3, h2]

/-- Climbing the honest deterministic authentication path reconstructs the indicated ancestor. -/
theorem climb_authenticationPath (leaf : ℕ → Y) (nodeHash : Address → Y → Y → Y) :
    ∀ (depth base index : ℕ),
      climb nodeHash base index depth (treeHash leaf nodeHash base index)
          (authenticationPath leaf nodeHash base index depth) =
        treeHash leaf nodeHash (base + depth) (index / 2 ^ depth) := by
  intro depth
  induction depth with
  | zero =>
      intro base index
      simp [climb]
  | succ depth ih =>
      intro base index
      simp only [authenticationPath, climb, List.Vector.head_cons, List.Vector.tail_cons]
      rw [combineSibling_eq_treeHash, ih (base + 1) (index / 2)]
      congr 1
      · omega
      · rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- A root-level honest deterministic opening reconstructs `root`. -/
theorem reconstructRoot_authenticationPath (leaf : ℕ → Y)
    (nodeHash : Address → Y → Y → Y) {height : ℕ} (index : LeafIndex height) :
    reconstructRoot nodeHash index (leaf index.val)
        (rootAuthenticationPath leaf nodeHash index) =
      root leaf nodeHash height := by
  simpa [reconstructRoot, rootAuthenticationPath, root, Nat.div_eq_of_lt index.isLt] using
    climb_authenticationPath leaf nodeHash height 0 index.val

end PerfectMerkleTree
