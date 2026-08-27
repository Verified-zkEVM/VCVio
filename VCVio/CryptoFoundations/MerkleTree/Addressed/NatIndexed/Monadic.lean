/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Monadic
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed

/-!
# Effectful natural-number-indexed perfect Merkle trees

Effectful companions to `PerfectMerkleTree.tree`, `merkleRoot`, `authPath`, and `climb`, built on
the canonical typed-address engine.  Both leaves and node hashes are monadic, which is the API
needed by SLH-DSA to represent public hashing as explicit oracle calls.

No oracle handler or cache is selected here.  The caller must interpret the whole surrounding
program with one handler.  In particular, random-oracle consumers must install one shared lazy
oracle across construction, signing, the adversary, and verification.
-/

@[expose] public section

namespace PerfectMerkleTree

open AddressedMerkleTree BinaryTree InductiveMerkleTree OracleComp OracleSpec

universe u v

variable {Y : Type v}

/-- Effectfully build the fully populated perfect subtree at `(height z, index t)`. -/
def treeM {m : Type v → Type*} [Monad m] (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (z t : ℕ) : m (FullData Y (Skeleton.perfect z)) :=
  buildMerkleTreeAddressedM
    (fun i => leaf (i.natIndex t))
    (fun a => nodeHash (a.natAddr t).height (a.natAddr t).index)

/-- Effectfully compute the root of the perfect subtree at `(height z, index t)` without
materializing it.  Evaluation is depth-first and left-to-right. -/
def merkleRootM {m : Type v → Type*} [Monad m] (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) : ℕ → ℕ → m Y
  | 0, t => leaf t
  | z + 1, t => do
      let left ← merkleRootM leaf nodeHash z (2 * t)
      let right ← merkleRootM leaf nodeHash z (2 * t + 1)
      nodeHash (z + 1) t left right

/-- Flip the least-significant bit of a heap-style node index. -/
def sibling (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- Extending an authentication path by one level appends the root of the sibling subtree at
that level. -/
theorem authPath_succ (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    authPath leaf nodeHash idx (z + 1) =
      authPath leaf nodeHash idx z ++
        [merkleRoot leaf nodeHash z (sibling (idx / 2 ^ z))] := by
  unfold authPath sibling
  simp only [SkeletonLeafIndex.ofNat]
  rw [tree_succ]
  by_cases h : idx / 2 ^ z % 2 = 0
  · rw [if_pos h]
    have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have heven : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
    simp only [generateProof, List.Vector.toList_cons, List.reverse_cons,
      FullData.leftSubtree, FullData.rightSubtree, FullData.getRootValue]
    rw [heven]
    rw [if_pos h]
    rfl
  · rw [if_neg h]
    have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
    have hmod : idx / 2 ^ z % 2 = 1 := by omega
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hodd : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by
      rw [hdiv]
      omega
    have hleft : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z - 1 := by omega
    simp only [generateProof, List.Vector.toList_cons, List.reverse_cons,
      FullData.leftSubtree, FullData.rightSubtree, FullData.getRootValue]
    rw [hodd]
    rw [if_neg h]
    unfold merkleRoot
    unfold FullData.getRootValue
    rw [hleft]

/-- Effectfully compute the authentication path of global leaf `idx` over `z` levels.  Only the
sibling subtrees are evaluated: the queried leaf and nodes on its direct path are not recomputed.
Entries and effects are ordered from the leaf level upward, as in FIPS 205. -/
def authPathM {m : Type v → Type*} [Monad m] (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) : ℕ → m (List Y)
  | 0 => pure []
  | z + 1 => do
      let path ← authPathM leaf nodeHash idx z
      let siblingRoot ← merkleRootM leaf nodeHash z (sibling (idx / 2 ^ z))
      return path ++ [siblingRoot]

/-- Effectfully recover a root from a leaf value and a leaf-first authentication path. -/
def climbM {m : Type v → Type*} [Monad m] (nodeHash : ℕ → ℕ → Y → Y → m Y)
    (idx : ℕ) (node : Y) (auth : List Y) : m Y :=
  getPutativeRootAddressedM
    (fun a => nodeHash (a.natAddr (idx / 2 ^ auth.length)).height
      (a.natAddr (idx / 2 ^ auth.length)).index)
    (SkeletonLeafIndex.ofNat auth.length idx) node ⟨auth.reverse, by simp⟩

section DeterministicInterpretation

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- A deterministic handler commutes with effectful perfect-tree construction. -/
@[simp]
theorem simulateQ_treeM (impl : QueryImpl spec Id) (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (z t : ℕ) :
    simulateQ impl (treeM leaf nodeHash z t) =
      tree (fun i => simulateQ impl (leaf i))
        (fun h i l r => simulateQ impl (nodeHash h i l r)) z t := by
  unfold treeM tree
  rw [simulateQ_buildMerkleTreeAddressedM]
  rfl

/-- A deterministic handler commutes with effectful root production. -/
@[simp]
theorem simulateQ_merkleRootM (impl : QueryImpl spec Id) (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (z t : ℕ) :
    simulateQ impl (merkleRootM leaf nodeHash z t) =
      merkleRoot (fun i => simulateQ impl (leaf i))
        (fun h i l r => simulateQ impl (nodeHash h i l r)) z t := by
  induction z generalizing t with
  | zero => rfl
  | succ z ih =>
      simp only [merkleRootM, simulateQ_bind, merkleRoot_succ, ih]
      rfl

/-- A deterministic handler commutes with effectful authentication-path production. -/
@[simp]
theorem simulateQ_authPathM (impl : QueryImpl spec Id) (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (idx z : ℕ) :
    simulateQ impl (authPathM leaf nodeHash idx z) =
      authPath (fun i => simulateQ impl (leaf i))
        (fun h i l r => simulateQ impl (nodeHash h i l r)) idx z := by
  induction z with
  | zero => rfl
  | succ z ih =>
      simp only [authPathM, simulateQ_bind, simulateQ_pure, ih, simulateQ_merkleRootM]
      rw [authPath_succ]
      rfl

/-- A deterministic handler commutes with effectful root recovery. -/
@[simp]
theorem simulateQ_climbM (impl : QueryImpl spec Id)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (idx : ℕ) (node : Y)
    (auth : List Y) :
    simulateQ impl (climbM nodeHash idx node auth) =
      climb (fun h i l r => simulateQ impl (nodeHash h i l r)) idx node auth := by
  unfold climbM climb
  unfold nodeHashAt
  simpa only using
    (simulateQ_getPutativeRootAddressedM impl
      (fun a => nodeHash (a.natAddr (idx / 2 ^ auth.length)).height
        (a.natAddr (idx / 2 ^ auth.length)).index)
      (SkeletonLeafIndex.ofNat auth.length idx) node
      (⟨auth.reverse, by simp⟩ :
        List.Vector Y (SkeletonLeafIndex.ofNat auth.length idx).depth))

/-- Functional Merkle completeness after fixing one deterministic answer function for the whole
honest opening computation.  This does not claim completeness under raw free-oracle evaluation,
where repeated syntactic queries would be sampled independently. -/
theorem simulateQ_climbM_authPathM (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y) (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx z : ℕ) :
    simulateQ impl (do
      let leafValue ← leaf idx
      let path ← authPathM leaf nodeHash idx z
      climbM nodeHash idx leafValue path) =
      simulateQ impl (merkleRootM leaf nodeHash z (idx / 2 ^ z)) := by
  simp only [simulateQ_bind, simulateQ_authPathM, simulateQ_climbM, simulateQ_merkleRootM]
  exact climb_authPath
    (fun i => simulateQ impl (leaf i))
    (fun h i l r => simulateQ impl (nodeHash h i l r)) idx z

end DeterministicInterpretation

end PerfectMerkleTree
