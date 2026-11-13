/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Merkle.Basic

/-!
# Counting inactive frontier nodes

Distinct maximal inactive subtrees have distinct least covered epochs. Their images are
separate from the inclusive active interval, giving a bound by the inactive leaf count.
-/

public section

namespace GXMSS.IntervalMerkle

variable {h : ℕ}

/-- Number of epochs in the inclusive active interval. -/
@[expose] def Interval.length (I : Interval h) : ℕ := I.last.val - I.first.val + 1

/-- Full-range interval length is the complete epoch count, including at height zero. -/
@[simp] theorem Interval.length_full (h : ℕ) : (Interval.full h).length = 2 ^ h := by
  have hn : 0 < 2 ^ h := by positivity
  simp [Interval.length, Interval.full]
  omega

private def frontierLeastEpoch (I : Interval h) (node : Subtree.FrontierNode I) : Fin (2 ^ h) :=
  match node with
  | ⟨(height, index), hf⟩ =>
    ⟨index.val * 2 ^ height.val, by
      have hp : 0 < 2 ^ height.val := by positivity
      have hs := hf.span_le
      nlinarith⟩

private theorem frontierLeastEpoch_covers (I : Interval h) (node : Subtree.FrontierNode I) :
    let (height, index) := node.val
    Subtree.CoversEpoch height.val index.val (frontierLeastEpoch I node).val := by
  obtain ⟨⟨height, index⟩, hf⟩ := node
  dsimp [frontierLeastEpoch, Subtree.CoversEpoch]
  have hp : 0 < 2 ^ height.val := by positivity
  constructor
  · rfl
  · nlinarith

private theorem frontierLeastEpoch_inactive (I : Interval h) (node : Subtree.FrontierNode I) :
    ¬ Epoch.IsActive I (frontierLeastEpoch I node) := by
  obtain ⟨⟨height, index⟩, hf⟩ := node
  exact Epoch.not_isActive_of_isInactiveFrontier_coversEpoch I _ _ _ hf
    (frontierLeastEpoch_covers I ⟨(height, index), hf⟩)

private theorem frontierLeastEpoch_injective (I : Interval h) :
    Function.Injective (frontierLeastEpoch I) := by
  intro x y hxy
  have hx := frontierLeastEpoch_inactive I x
  have hy : let (height, index) := y.val
      Subtree.CoversEpoch height.val index.val (frontierLeastEpoch I x).val := by
    rw [hxy]
    exact frontierLeastEpoch_covers I y
  exact (Subtree.frontierNode_unique I _ hx x (frontierLeastEpoch_covers I x)).trans
    (Subtree.frontierNode_unique I _ hx y hy).symm

private def activeOffset (I : Interval h) (offset : Fin I.length) : Fin (2 ^ h) :=
  ⟨I.first.val + offset.val, by
    have ho := offset.isLt
    have hi := I.ordered
    have hl := I.last.isLt
    dsimp [Interval.length] at ho
    omega⟩

private theorem activeOffset_active (I : Interval h) (offset : Fin I.length) :
    Epoch.IsActive I (activeOffset I offset) := by
  have ho := offset.isLt
  have hi := I.ordered
  dsimp [Interval.length] at ho
  change I.first.val ≤ I.first.val + offset.val ∧ I.first.val + offset.val ≤ I.last.val
  omega

private def frontierAndActiveEpoch (I : Interval h) :
    Subtree.FrontierNode I ⊕ Fin I.length → Fin (2 ^ h) :=
  Sum.elim (frontierLeastEpoch I) (activeOffset I)

private theorem frontierAndActiveEpoch_injective (I : Interval h) :
    Function.Injective (frontierAndActiveEpoch I) := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (frontierLeastEpoch_injective I hxy)
    | inr y =>
      change frontierLeastEpoch I x = activeOffset I y at hxy
      exact False.elim (frontierLeastEpoch_inactive I x
        (hxy.symm ▸ activeOffset_active I y))
  | inr x =>
    cases y with
    | inl y =>
      change activeOffset I x = frontierLeastEpoch I y at hxy
      exact False.elim (frontierLeastEpoch_inactive I y
        (hxy ▸ activeOffset_active I x))
    | inr y =>
      apply congrArg Sum.inr
      apply Fin.ext
      have he := congrArg Fin.val hxy
      change I.first.val + x.val = I.first.val + y.val at he
      omega

/-- Each inactive frontier node consumes a distinct inactive epoch; no height or numerical
frontier cap is assumed. -/
theorem frontier_card_le_inactive (I : Interval h) :
    Fintype.card (Subtree.FrontierNode I) ≤ 2 ^ h - I.length := by
  have hc := Fintype.card_le_of_injective _ (frontierAndActiveEpoch_injective I)
  simp only [Fintype.card_sum, Fintype.card_fin] at hc
  omega

end GXMSS.IntervalMerkle
