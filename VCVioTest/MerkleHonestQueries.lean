/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Query.Honest
public import ToMathlib.Data.IndexedBinaryTree.Perfect

/-!
# Honest opening query provenance controls

Height zero has no node query. The height-three control uses a noncommutative hash and repeats
the same concrete key at every ancestor; its log still records the actual ordered child pairs.
-/

public section
namespace VCVioTest.MerkleHonestQueries
open BinaryTree AddressedMerkleTree

/-- Eight independently labeled leaves. -/
@[expose] def leaves : LeafData ℕ (Skeleton.perfect 3) :=
  .internal (.internal (.internal (.leaf 1) (.leaf 2)) (.internal (.leaf 3) (.leaf 4)))
    (.internal (.internal (.leaf 5) (.leaf 6)) (.internal (.leaf 7) (.leaf 8)))

/-- The sixth leaf visits right, left and right from the root. -/
@[expose] def idx : SkeletonLeafIndex (Skeleton.perfect 3) :=
  .ofRight (.ofLeft (.ofRight .ofLeaf))

/-- A deliberately non-injective concrete key map. -/
@[expose] def key (_ : SkeletonInternalIndex (Skeleton.perfect 3)) : Unit := ()

/-- Right and left inputs carry different weights. -/
@[expose] def hash (_ : Unit) (left right : ℕ) : ℕ := left + 10 * right

/-- Honest values at every internal node. -/
@[expose] def tree := buildMerkleTreeAddressedWithHash leaves (fun a => hash (key a))

/-- The generated proof is root-first in the addressed engine. -/
@[expose] def proof := InductiveMerkleTree.generateProof tree idx

/-- Repeated addresses retain three different, ordered raw inputs. -/
theorem exact_log : openingQueries key hash idx (leaves.get idx) proof =
    [⟨(), (451, 935)⟩, ⟨(), (65, 87)⟩, ⟨(), (5, 6)⟩] := by
  rfl

/-- Exchanging the lower levels does not preserve the actual query log. -/
theorem lower_levels_not_swapped : openingQueries key hash idx (leaves.get idx) proof ≠
    [⟨(), (451, 935)⟩, ⟨(), (5, 6)⟩, ⟨(), (65, 87)⟩] := by
  rw [exact_log]
  decide

/-- The actual root query is present in the generated opening. -/
theorem root_query_mem :
    (⟨(), (451, 935)⟩ : NodeQuery Unit ℕ) ∈
      openingQueries key hash idx (leaves.get idx) proof := by
  rw [exact_log]
  decide

/-- Query membership recovers a visited ancestor and its exact stored children. -/
theorem root_provenance : ∃ a : SkeletonInternalIndex (Skeleton.perfect 3),
    a.IsAncestorOf idx ∧ (⟨(), (451, 935)⟩ : NodeQuery Unit ℕ).address = key a ∧
      (451, 935) = childPairAt tree a :=
  mem_openingQueries_honestTree key hash leaves idx _ root_query_mem

/-- Height zero performs no internal hash query. -/
theorem height_zero : openingQueries
    (fun a : SkeletonInternalIndex .leaf => nomatch a) hash .ofLeaf 9 ⟨[], rfl⟩ = [] := rfl

end VCVioTest.MerkleHonestQueries
