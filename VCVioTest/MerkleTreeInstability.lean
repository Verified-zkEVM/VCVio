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
transition has positive probability. Reordered and duplicated representing logs test extraction
invariance and the fixed-log characterization of disagreement.
-/

public section

open OracleSpec OracleComp ENNReal BinaryTree MerkleTreeExtractability

namespace VCVioTest.MerkleTreeInstability

/-- The four labels used by the Merkle extraction canaries. -/
abbrev Y := Fin 4

/-- An oracle hashing ordered pairs of four-valued labels. -/
abbrev TestSpec := (Y × Y) →ₒ Y

noncomputable local instance : UniformAnswerMeasure TestSpec :=
  UniformAnswerMeasure.ofFiniteNonempty TestSpec

/-- Queries are the ordered pairs of children, with one address for every node. -/
private def model : NodeQueryModel (Y × Y) Unit Y where
  view := ⟨fun _ => (), id⟩
  mkQuery := fun _ p => p
  address_mkQuery := fun _ _ => rfl
  input_mkQuery := fun _ _ => rfl

private def shape : Skeleton := .internal .leaf .leaf

private def address : SkeletonInternalIndex shape → Unit := fun _ => ()

/-- The left leaf. -/
private def idx : SkeletonLeafIndex shape := .ofLeft .ofLeaf

/-- The authentication path of the left leaf with sibling `2`. -/
private def proof : List.Vector Y idx.depth := ⟨[2], rfl⟩

-- The empty database has no collision and does not extract this opening.
example : (∅ : QueryCache TestSpec) ∈ nonExtractingCaches model address 1 3 idx proof := by
  refine ⟨?_, [], ?_, ?_⟩
  · rintro ⟨x, y, a, b, _, h, _, _⟩
    simp at h
  · simp [LogRepresentsCache]
  · left
    decide

-- Exactly one of the four answers at `(1, 2)` completes the opening.
example : (∅ : QueryCache TestSpec).updateProb (1, 2)
    (acceptingCaches model address 1 3 idx proof) = 1 / 4 := by
  classical
  rw [QueryCache.updateProb_eq_card_div]
  have hp : ∀ u : Y, (∅ : QueryCache TestSpec).cacheQuery (1, 2) u ∈
      acceptingCaches model address 1 3 idx proof ↔ u = 3 := by
    intro u
    change (∃ a : Y, (∅ : QueryCache TestSpec).cacheQuery (1, 2) u (a, 2) = some 3 ∧ 1 = a) ↔
      u = 3
    simp
  simp only [hp]
  simp [Finset.filter_eq']

/-- A collision-free cache with two distinct queries and responses. -/
private def twoEntryCache : QueryCache TestSpec :=
  ⟨fun q => if q = (1, 2) then some 3 else if q = (0, 0) then some 0 else none⟩

/-- The two cached responses uniquely identify their queries. -/
private lemma twoEntryCache_noCollision : ¬CacheHasCollision twoEntryCache := by
  rintro ⟨x, y, a, b, hxy, hx, hy, hab⟩
  have hab' : a = b := eq_of_heq hab
  simp only [twoEntryCache] at hx hy
  split_ifs at hx hy <;> simp_all
  all_goals have h := hx.trans hy.symm; norm_num at h

/-- Listing each entry once represents the two-entry cache. -/
private lemma twoEntryLog_represents :
    LogRepresentsCache [⟨(1, 2), 3⟩, ⟨(0, 0), 0⟩] twoEntryCache := by
  constructor
  · intro entry hentry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl <;> decide
  · intro input value hvalue
    simp only [twoEntryCache] at hvalue
    split_ifs at hvalue with h₁ h₂ <;> simp_all

/-- Reordering and repeating the entries still represents the same cache. -/
private lemma repeatedLog_represents :
    LogRepresentsCache [⟨(0, 0), 0⟩, ⟨(1, 2), 3⟩, ⟨(0, 0), 0⟩] twoEntryCache := by
  constructor
  · intro entry hentry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl | rfl <;> decide
  · intro input value hvalue
    simp only [twoEntryCache] at hvalue
    split_ifs at hvalue with h₁ h₂ <;> simp_all

-- The public invariance bridge handles permutations and duplicate log entries together.
example :
    MerkleTreeExtractor.tree model.view shape address [⟨(1, 2), 3⟩, ⟨(0, 0), 0⟩] 3 =
      MerkleTreeExtractor.tree model.view shape address
        [⟨(0, 0), 0⟩, ⟨(1, 2), 3⟩, ⟨(0, 0), 0⟩] 3 :=
  tree_eq_of_logRepresentsCache model.view twoEntryLog_represents repeatedLog_represents
    twoEntryCache_noCollision shape address 3

-- A fixed representing log suffices to characterize failure to extract an opening.
example (leaf root : Y) :
    twoEntryCache ∈ nonExtractingCaches model address leaf root idx proof ↔
      OpeningDisagrees model address [⟨(0, 0), 0⟩, ⟨(1, 2), 3⟩, ⟨(0, 0), 0⟩]
        leaf root idx proof := by
  rw [mem_nonExtractingCaches_iff_of_logRepresentsCache repeatedLog_represents,
    and_iff_right twoEntryCache_noCollision]

end VCVioTest.MerkleTreeInstability
