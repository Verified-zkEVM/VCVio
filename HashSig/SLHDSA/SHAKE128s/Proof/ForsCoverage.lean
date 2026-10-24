/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.MessageDigest
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# FORS coverage for an independent target

The target here is a fresh uniform index and fourteen fresh uniform leaf indices. `Covered`
says that every one of the target's fourteen leaves lies in the disclosed set of its FORS tree,
`covered_card` counts the covered views through the equivalence `coveredEquiv`, and
`fresh_coverage` gives the exact probability that a fresh uniform view is covered. This file does
not identify that distribution with an adaptively selected message digest.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.ForsCoverage

/-- The FORS instance selected by a message digest. -/
abbrev Instance := MessageDigest.Instance
/-- The index of one of the fourteen FORS trees. -/
abbrev Tree := MessageDigest.ForsTree
/-- A leaf index inside one FORS tree. -/
abbrev Leaf := MessageDigest.ForsLeaf
/-- The parsed FORS view of a message digest: an instance and one leaf per tree. -/
abbrev View := MessageDigest.View
/-- For every instance and tree, the set of leaves whose secrets have been disclosed. -/
abbrev Disclosures := Instance → Tree → Finset Leaf

/-- A view is covered when every one of its leaves has been disclosed in its own tree. -/
@[expose] def Covered (revealed : Disclosures) (view : View) : Prop :=
  ∀ tree, view.2 tree ∈ revealed view.1 tree

/-- Coverage of a view is decidable. -/
instance (revealed : Disclosures) : DecidablePred (Covered revealed) :=
  fun view => inferInstanceAs (Decidable (∀ tree, view.2 tree ∈ revealed view.1 tree))

/-- Covered views are equivalent to an instance with a disclosed leaf chosen in every tree. -/
@[expose] def coveredEquiv (revealed : Disclosures) :
    (Σ index : Instance, (tree : Tree) → {leaf : Leaf // leaf ∈ revealed index tree}) ≃
      {view : View // Covered revealed view} where
  toFun choice :=
    ⟨(choice.1, fun tree => (choice.2 tree).val), fun tree => (choice.2 tree).property⟩
  invFun view := ⟨view.val.1, fun tree => ⟨view.val.2 tree, view.property tree⟩⟩
  left_inv := by rintro ⟨index, leaves⟩; rfl
  right_inv := by rintro ⟨⟨index, leaves⟩, h⟩; rfl

/-- The number of covered views is the sum over instances of the product of disclosure sizes. -/
theorem covered_card (revealed : Disclosures) :
    (Finset.univ.filter (Covered revealed)).card =
      ∑ index : Instance, ∏ tree : Tree, (revealed index tree).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_congr (coveredEquiv revealed), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro index _
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro tree _
  simp

/-- The probability that a fresh uniform view is covered, as a count over `2 ^ 231` views. -/
theorem fresh_coverage (revealed : Disclosures) :
    Pr{let x ← ($ᵗ View : ProbComp View)}[(Covered revealed) x] =
      ((∑ index : Instance, ∏ tree : Tree, (revealed index tree).card : Nat) : ℝ≥0∞) /
        ((2 ^ 231 : Nat) : ℝ≥0∞) := by
  rw [SampleableType.prEvent_uniformSample, covered_card]
  have hcard : Fintype.card View = 2 ^ 231 := by
    norm_num [View, Instance, Tree, Leaf, MessageDigest.View, MessageDigest.Instance,
      MessageDigest.ForsTree, MessageDigest.ForsLeaf, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, totalHeight, forsHeight, forsTrees]
  rw [hcard]

end SLHDSA.SHAKE128s.ForsCoverage
