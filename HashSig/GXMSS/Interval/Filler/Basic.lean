/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Merkle

/-!
# Inactive frontier input families

Each inactive frontier address belongs to the endpoint-vector or ordered-child-pair family.
Their finite target subtypes retain exact capacities and original hash input embeddings.
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle OracleSpec OracleComp TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The two original-input domains used at an inactive frontier. -/
inductive Family
  /-- A leaf hashes its complete endpoint vector. -/
  | endpointVector
  /-- An internal node hashes its ordered left and right children. -/
  | childPair
  deriving DecidableEq, Repr

/-- Original input payload at a frontier of the selected family. -/
@[expose] def Input (f : Family) (H : Type) (v : ℕ) : Type :=
  match f with
  | .endpointVector => Fin v → H
  | .childPair => H × H

instance (f : Family) [SampleableType H] : SampleableType (Input f H v) := by
  cases f <;> unfold Input <;> infer_instance

/-- Family membership depends only on the address height. -/
@[expose] def HasFamily (f : Family) {I : Interval h} (node : Subtree.FrontierNode I) : Prop :=
  let (height, _) := node.val
  match f with
  | .endpointVector => height.val = 0
  | .childPair => 0 < height.val

instance (f : Family) (I : Interval h) (node : Subtree.FrontierNode I) :
    Decidable (HasFamily f node) := by
  cases f <;> unfold HasFamily <;> infer_instance

/-- Exact finite target subtype; no frontier-size estimate is used. -/
@[expose] def Target (f : Family) (I : Interval h) :=
  { node : Subtree.FrontierNode I // HasFamily f node }

instance (f : Family) (I : Interval h) : Fintype (Target f I) :=
  inferInstanceAs (Fintype { node : Subtree.FrontierNode I // HasFamily f node })

instance (f : Family) (I : Interval h) : DecidableEq (Target f I) :=
  inferInstanceAs (DecidableEq { node : Subtree.FrontierNode I // HasFamily f node })

/-- The finite Merkle address associated to a target. -/
@[expose] def address {f : Family} {I : Interval h} (n : Target f I) :
    Fin (h + 1) × Fin (2 ^ h) :=
  let node := n.val
  node.val

/-- Distinct targets have distinct original tree addresses. -/
theorem address_injective (f : Family) (I : Interval h) :
    Function.Injective (address (f := f) (I := I)) := by
  intro a b hab
  exact Subtype.ext (Subtype.ext hab)

/-- Number of nodes in the selected inactive frontier family. -/
@[expose] def targetCapacity (f : Family) (I : Interval h) : ℕ := Fintype.card (Target f I)

/-- The vector and pair target families partition the inactive frontier by height. -/
theorem targetCapacity_sum_eq_frontier_card (I : Interval h) :
    GXMSS.Interval.Filler.targetCapacity .endpointVector I +
      GXMSS.Interval.Filler.targetCapacity .childPair I = Fintype.card (Subtree.FrontierNode I) :=
          by
  let split : GXMSS.Interval.Filler.Target .endpointVector I ⊕
      GXMSS.Interval.Filler.Target .childPair I ≃ Subtree.FrontierNode I :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun node =>
        if hz : GXMSS.Interval.Filler.HasFamily .endpointVector node then Sum.inl ⟨node, hz⟩
        else Sum.inr ⟨node, by
          obtain ⟨⟨height, index⟩, hf⟩ := node
          change ¬ height.val = 0 at hz
          change 0 < height.val
          omega⟩
      left_inv := by
        rintro (⟨node, hn⟩ | ⟨node, hn⟩)
        · change (if hz : GXMSS.Interval.Filler.HasFamily .endpointVector node then
              (Sum.inl ⟨node, hz⟩ : GXMSS.Interval.Filler.Target .endpointVector I ⊕
                GXMSS.Interval.Filler.Target .childPair I) else Sum.inr ⟨node, _⟩) = Sum.inl ⟨node,
                    hn⟩
          rw [dite_eq_left hn]
        · have hz : ¬ GXMSS.Interval.Filler.HasFamily .endpointVector node := by
            obtain ⟨⟨height, index⟩, hf⟩ := node
            change 0 < height.val at hn
            change ¬ height.val = 0
            omega
          change (if hz : GXMSS.Interval.Filler.HasFamily .endpointVector node then
              (Sum.inl ⟨node, hz⟩ : GXMSS.Interval.Filler.Target .endpointVector I ⊕
                GXMSS.Interval.Filler.Target .childPair I) else Sum.inr ⟨node, _⟩) = Sum.inr ⟨node,
                    hn⟩
          rw [dite_eq_right hz]
      right_inv := by intro node; dsimp; split <;> rfl }
  simpa only [Fintype.card_sum, GXMSS.Interval.Filler.targetCapacity] using Fintype.card_congr split

/-- Embedding of the selected original input domain into the common THF domain. -/
@[expose] def embed (P : HashInstance PP T X H h w v) (f : Family) : Input f H v ↪ X :=
  match f with
  | .endpointVector => P.vectorInput
  | .childPair => P.pairInput

/-- The target's original addressed-tree tweak. -/
@[expose] def tweak (P : HashInstance PP T X H h w v) {f : Family} {I : Interval h}
    (n : Target f I) : T := P.treeTweak (address n)

instance (f : Family) (h : ℕ) : IsEmpty (Target f (Interval.full h)) where
  false n := isEmptyElim n.val

/-- A full interval has no target of either family. -/
@[simp] theorem targetCapacity_full (f : Family) (h : ℕ) :
    targetCapacity f (Interval.full h) = 0 := Fintype.card_eq_zero

/-- The family whose fillers remain independently uniform in a one-family hybrid. -/
@[expose] def Family.other : Family → Family
  | .endpointVector => .childPair
  | .childPair => .endpointVector

end GXMSS.Interval.Filler
