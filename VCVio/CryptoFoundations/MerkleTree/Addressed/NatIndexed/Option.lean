/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.OracleComp.SimSemantics.SimulateQ.Option

/-!
# Natural-number-indexed Merkle programs under a partial oracle

Decompositions of the effectful perfect-tree programs `PerfectMerkleTree.merkleRootM`,
`intrinsicAuthPathM` and `climbM` when their oracle is interpreted into `Option`: a root, a path or
a climb is settled (`= some _`) exactly when each of its hash queries is settled, at the value the
program passes on.  This is the interface a cache-level argument uses to read honest intermediate
values off a partial oracle one hash query at a time.

The climb lemmas rest on monad-generic equations for `climbM`: `climbM_concat` peels the final
(root-level) hash, `climbM_append` splits a climb at any height, and `climbM_cons` peels the
leaf-level hash.  Because the node addresses of `climbM` are relative to the leaf, splitting a
climb re-bases the upper part: it climbs from leaf index `idx / 2 ^ k` with the heights of
`nodeHash` shifted by `k`.  In particular the leaf-first step does **not** continue with the same
`nodeHash`.
-/

public section

namespace PerfectMerkleTree

open AddressedMerkleTree BinaryTree OracleComp OracleSpec

universe u v

/-! ## Monad-generic climb equations -/

section Monadic

variable {Y : Type v} {m : Type v → Type u} [Monad m]

/-- `climbM` on a path of known length `z`, unfolded to the addressed engine's putative root. -/
theorem climbM_eq (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node : Y) (auth : List Y)
    {z : ℕ} (hp : auth.reverse.length = (SkeletonLeafIndex.ofNat z idx).depth) :
    climbM nodeHash idx node auth =
      getPutativeRootAddressedM
        (fun a => nodeHash (a.natAddr (idx / 2 ^ z)).height (a.natAddr (idx / 2 ^ z)).index)
        (SkeletonLeafIndex.ofNat z idx) node ⟨auth.reverse, hp⟩ := by
  obtain rfl : auth.length = z := by simpa using hp
  rfl

/-- A climb along the empty path returns the starting node. -/
@[simp]
theorem climbM_nil (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node : Y) :
    climbM nodeHash idx node [] = pure node := rfl

/-- A climb along `auth ++ [a]` is the climb along `auth`, followed by one hash at height
`auth.length + 1` and index `idx / 2 ^ (auth.length + 1)` whose inputs are the climbed value and
`a`, ordered by the parity of `idx / 2 ^ auth.length`. -/
theorem climbM_concat (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node : Y) (auth : List Y)
    (a : Y) :
    climbM nodeHash idx node (auth ++ [a]) =
      climbM nodeHash idx node auth >>= fun child =>
        if idx / 2 ^ auth.length % 2 = 0 then
          nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1)) child a
        else nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1)) a child := by
  have hp : (auth ++ [a]).reverse.length =
      (SkeletonLeafIndex.ofNat (auth.length + 1) idx).depth := by simp
  rw [climbM_eq nodeHash idx node (auth ++ [a]) hp]
  unfold climbM
  have hdiv : idx / 2 ^ (auth.length + 1) = idx / 2 ^ auth.length / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  revert hp
  generalize hi : SkeletonLeafIndex.ofNat (auth.length + 1) idx = i
  simp only [SkeletonLeafIndex.ofNat] at hi
  cases i <;> split at hi <;> cases hi <;> intro hp <;> rename_i h <;>
    rw [show (⟨(auth ++ [a]).reverse, hp⟩ : List.Vector Y _) =
      ⟨a :: auth.reverse, by simpa using hp⟩ from Subtype.ext (by simp)]
  · have heven : 2 * (idx / 2 ^ (auth.length + 1)) = idx / 2 ^ auth.length := by omega
    simp only [getPutativeRootAddressedM, SkeletonInternalIndex.natAddr, heven, h, ↓reduceIte]
    rfl
  · have hodd : 2 * (idx / 2 ^ (auth.length + 1)) + 1 = idx / 2 ^ auth.length := by omega
    simp only [getPutativeRootAddressedM, SkeletonInternalIndex.natAddr, hodd, h, ↓reduceIte]
    rfl

variable [LawfulMonad m]

/-- A climb along a single sibling is one hash at height `1`, index `idx / 2`, with inputs
ordered by the parity of `idx`. -/
theorem climbM_singleton (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node a : Y) :
    climbM nodeHash idx node [a] =
      if idx % 2 = 0 then nodeHash 1 (idx / 2) node a else nodeHash 1 (idx / 2) a node := by
  simpa using climbM_concat nodeHash idx node [] a

/-- A climb along `auth₁ ++ auth₂` is the climb along `auth₁`, then a climb along `auth₂` from
leaf index `idx / 2 ^ auth₁.length` with the heights of `nodeHash` shifted by `auth₁.length`. -/
theorem climbM_append (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node : Y)
    (auth₁ auth₂ : List Y) :
    climbM nodeHash idx node (auth₁ ++ auth₂) =
      climbM nodeHash idx node auth₁ >>= fun v =>
        climbM (fun h i => nodeHash (h + auth₁.length) i) (idx / 2 ^ auth₁.length) v auth₂ := by
  induction auth₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton auth₂ b ih =>
    rw [← List.append_assoc, climbM_concat, ih, bind_assoc]
    simp only [climbM_concat, List.length_append, Nat.div_div_eq_div_mul, ← pow_add,
      Nat.add_comm, Nat.add_assoc]

/-- A climb along `a :: auth` is the leaf-level hash at height `1`, index `idx / 2`, followed
by a climb along `auth` from leaf index `idx / 2` with the heights of `nodeHash` shifted by
one. -/
theorem climbM_cons (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node a : Y) (auth : List Y) :
    climbM nodeHash idx node (a :: auth) =
      (if idx % 2 = 0 then nodeHash 1 (idx / 2) node a else nodeHash 1 (idx / 2) a node) >>=
        fun parent => climbM (fun h i => nodeHash (h + 1) i) (idx / 2) parent auth := by
  rw [← List.singleton_append, climbM_append, climbM_singleton]
  simp only [List.length_singleton, pow_one]

end Monadic

/-! ## Settled climbs -/

section Option

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {Y : Type v} (impl : QueryImpl spec Option)

/-- A climb along the empty path is settled exactly at its starting node. -/
theorem simulateQ_climbM_nil_eq_some_iff (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx : ℕ) (node : Y) {r : Y} :
    simulateQ impl (climbM nodeHash idx node []) = some r ↔ node = r := by
  rw [climbM_nil, simulateQ_pure_eq_some_iff]

/-- A climb along `auth₁ ++ auth₂` is settled exactly when the climb along `auth₁` is settled
and the re-based climb along `auth₂` from its value is settled. -/
theorem simulateQ_climbM_append_eq_some_iff (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx : ℕ) (node : Y) (auth₁ auth₂ : List Y) {r : Y} :
    simulateQ impl (climbM nodeHash idx node (auth₁ ++ auth₂)) = some r ↔
      ∃ v, simulateQ impl (climbM nodeHash idx node auth₁) = some v ∧
        simulateQ impl (climbM (fun h i => nodeHash (h + auth₁.length) i)
          (idx / 2 ^ auth₁.length) v auth₂) = some r := by
  rw [climbM_append, simulateQ_bind_eq_some_iff]

/-- A climb along `auth ++ [a]` is settled exactly when the climb along `auth` is settled and
the root-level hash of its value with `a` is settled. -/
theorem simulateQ_climbM_concat_eq_some_iff (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx : ℕ) (node : Y) (auth : List Y) (a : Y) {r : Y} :
    simulateQ impl (climbM nodeHash idx node (auth ++ [a])) = some r ↔
      ∃ child, simulateQ impl (climbM nodeHash idx node auth) = some child ∧
        simulateQ impl (if idx / 2 ^ auth.length % 2 = 0 then
          nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1)) child a
        else nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1)) a child) = some r := by
  rw [climbM_concat, simulateQ_bind_eq_some_iff]

/-- A climb along `a :: auth` is settled exactly when the leaf-level hash is settled and the
re-based climb along `auth` from its value is settled. -/
theorem simulateQ_climbM_cons_eq_some_iff (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx : ℕ) (node a : Y) (auth : List Y) {r : Y} :
    simulateQ impl (climbM nodeHash idx node (a :: auth)) = some r ↔
      ∃ parent, simulateQ impl (if idx % 2 = 0 then nodeHash 1 (idx / 2) node a
          else nodeHash 1 (idx / 2) a node) = some parent ∧
        simulateQ impl (climbM (fun h i => nodeHash (h + 1) i) (idx / 2) parent auth) =
          some r := by
  rw [climbM_cons, simulateQ_bind_eq_some_iff]

/-- A settled climb settles the climb along every prefix of its path. -/
theorem exists_simulateQ_climbM_take_eq_some (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx : ℕ) (node : Y) (auth : List Y) {r : Y}
    (h : simulateQ impl (climbM nodeHash idx node auth) = some r) (k : ℕ) :
    ∃ v, simulateQ impl (climbM nodeHash idx node (auth.take k)) = some v := by
  rw [← List.take_append_drop k auth, simulateQ_climbM_append_eq_some_iff] at h
  exact h.imp fun v hv => hv.1

/-- Every hash query of a settled climb is settled at the climb's intermediate values: at each
height `k < auth.length`, the climb along the first `k` siblings is settled at some `v`, the climb
along the first `k + 1` is settled at some `w`, and the hash at height `k + 1`, index
`idx / 2 ^ (k + 1)`, of `v` and `auth[k]` (ordered by the parity of `idx / 2 ^ k`) is settled at
`w`. -/
theorem simulateQ_climbM_query_settled (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx : ℕ) (node : Y) (auth : List Y) {r : Y}
    (h : simulateQ impl (climbM nodeHash idx node auth) = some r) {k : ℕ}
    (hk : k < auth.length) :
    ∃ v w, simulateQ impl (climbM nodeHash idx node (auth.take k)) = some v ∧
      simulateQ impl (climbM nodeHash idx node (auth.take (k + 1))) = some w ∧
      simulateQ impl (if idx / 2 ^ k % 2 = 0 then nodeHash (k + 1) (idx / 2 ^ (k + 1)) v auth[k]
        else nodeHash (k + 1) (idx / 2 ^ (k + 1)) auth[k] v) = some w := by
  obtain ⟨w, hw⟩ := exists_simulateQ_climbM_take_eq_some impl nodeHash idx node auth h (k + 1)
  have hw' := hw
  rw [List.take_succ_eq_append_getElem hk, simulateQ_climbM_concat_eq_some_iff,
    List.length_take_of_le hk.le] at hw'
  obtain ⟨v, hv, hq⟩ := hw'
  exact ⟨v, w, hv, hw, hq⟩

/-! ## Settled roots and authentication paths -/

/-- The root of a perfect subtree of height `z + 1` is settled exactly when both child roots are
settled and the hash of their values at height `z + 1`, index `t`, is settled. -/
theorem simulateQ_merkleRootM_succ_eq_some_iff (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (z t : ℕ) {r : Y} :
    simulateQ impl (merkleRootM leaf nodeHash (z + 1) t) = some r ↔
      ∃ l rr, simulateQ impl (merkleRootM leaf nodeHash z (2 * t)) = some l ∧
        simulateQ impl (merkleRootM leaf nodeHash z (2 * t + 1)) = some rr ∧
        simulateQ impl (nodeHash (z + 1) t l rr) = some r := by
  simp only [merkleRootM, simulateQ_bind_eq_some_iff, exists_and_left]

/-- An authentication path over `z + 1` levels is settled exactly when the path over `z` levels
is settled, the root of the sibling subtree at height `z` is settled, and the path is the shorter
path extended by that root. -/
theorem simulateQ_intrinsicAuthPathM_succ_eq_some_iff (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (idx z : ℕ) {path : Vector Y (z + 1)} :
    simulateQ impl (intrinsicAuthPathM leaf nodeHash idx (z + 1)) = some path ↔
      ∃ (prefix_ : Vector Y z) (sib : Y),
        simulateQ impl (intrinsicAuthPathM leaf nodeHash idx z) = some prefix_ ∧
        simulateQ impl (merkleRootM leaf nodeHash z (sibling (idx / 2 ^ z))) = some sib ∧
        prefix_.push sib = path := by
  simp only [intrinsicAuthPathM, simulateQ_bind_eq_some_iff, simulateQ_pure_eq_some_iff,
    exists_and_left]

end Option

end PerfectMerkleTree
