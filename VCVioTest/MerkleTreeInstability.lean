/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Instability

/-!
# Merkle extraction instability canary

A two-leaf tree over `Fin 4` with pair queries. The empty database does not extract the opening of
the left leaf `1` with sibling `2` at the root `3`, and one fresh answer at the query `(1, 2)`
makes that opening verify exactly when the answer is `3`. So the source property of
`MerkleTreeExtractability.flip_nonExtractingCaches_acceptingCaches_le` is inhabited and the
transition has positive probability.
-/

public section

open OracleSpec OracleComp ENNReal BinaryTree MerkleTreeExtractability

namespace VCVioTest.MerkleTreeInstability

abbrev Y := Fin 4

abbrev TestSpec := (Y × Y) →ₒ Y

noncomputable local instance : UniformAnswerMeasure TestSpec :=
  UniformAnswerMeasure.ofFiniteNonempty TestSpec

/-- Queries are the ordered pairs of children, with one address for every node. -/
def model : NodeQueryModel (Y × Y) Unit Y where
  view := ⟨fun _ => (), id⟩
  mkQuery := fun _ p => p
  address_mkQuery := fun _ _ => rfl
  input_mkQuery := fun _ _ => rfl

def shape : Skeleton := .internal .leaf .leaf

def address : SkeletonInternalIndex shape → Unit := fun _ => ()

/-- The left leaf. -/
def idx : SkeletonLeafIndex shape := .ofLeft .ofLeaf

/-- The authentication path of the left leaf with sibling `2`. -/
def proof : List.Vector Y idx.depth := ⟨[2], rfl⟩

-- The empty database has no collision and extracts nothing, so it disagrees with the opening.
example : (∅ : QueryCache TestSpec) ∈ nonExtractingCaches model address 1 3 idx proof := by
  refine ⟨?_, [], ?_, ?_⟩
  · rintro ⟨x, y, a, b, _, h, _, _⟩
    simp at h
  · simp [LogRepresentsCache]
  · left
    decide

-- Exactly one of the four answers at `(1, 2)` completes the opening.
example : (∅ : QueryCache TestSpec).extendProb (1, 2)
    (acceptingCaches model address 1 3 idx proof) = 1 / 4 := by
  classical
  rw [QueryCache.extendProb_eq_card_div]
  have hp : ∀ u : Y, (∅ : QueryCache TestSpec).cacheQuery (1, 2) u ∈
      acceptingCaches model address 1 3 idx proof ↔ u = 3 := by
    intro u
    change (∃ a : Y, (∅ : QueryCache TestSpec).cacheQuery (1, 2) u (a, 2) = some 3 ∧ 1 = a) ↔
      u = 3
    simp
  simp only [hp]
  simp [Finset.filter_eq']

end VCVioTest.MerkleTreeInstability
