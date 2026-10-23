/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.BinaryPath
public import HashSig.SLHDSA.SHAKE128s.Proof.Hashing

/-!
# Collision extraction along a binary authentication path

A changed authentication path that reaches the canonical root contains a collision at one of its
own hash calls. `value` is the generic increasing-height fold that both the FORS and the XMSS
verifiers perform, `canonicalPair` is the pair of genuine children at a height, and
`canonical_or_collision` shows that a path reaching the canonical root either agrees with the
canonical nodes everywhere or exhibits a `Collision` at a concrete height. The witness keeps the
path position, so it names a concrete hash input.
-/

@[expose] public section

namespace SlhDsaSecurity.Extraction.BinaryPath

variable {α : Type}

/-- The ordered pair of a path value and its sibling at `height`: the value goes on the left
exactly when bit `height` of the leaf `index` is zero. -/
def ordered (index height : Nat) (value sibling : α) : α × α :=
  if index / 2 ^ height % 2 = 0 then (value, sibling) else (sibling, value)

/-- `ordered` is injective in the pair it orders. -/
theorem ordered_eq_iff (index height : Nat) (value sibling value' sibling' : α) :
    ordered index height value sibling = ordered index height value' sibling' ↔
      value = value' ∧ sibling = sibling' := by
  unfold ordered
  split <;> simp [and_comm]

/-- The value at `height` recomputed from the leaf and the supplied siblings, combining at each
level with `combine height nodeIndex left right`. -/
def value (combine : Nat → Nat → α → α → α) (index : Nat)
    (leaf : α) (siblings : Nat → α) : Nat → α
  | 0 => leaf
  | height + 1 =>
    let pair := ordered index height (value combine index leaf siblings height) (siblings height)
    combine (height + 1) (index / 2 ^ (height + 1)) pair.1 pair.2

/-- The canonical ordered pair of children at `height` on the path of leaf `index`, read off the
genuine node table `nodes height nodeIndex`. -/
def canonicalPair (nodes : Nat → Nat → α) (index height : Nat) : α × α :=
  ordered index height (nodes height (index / 2 ^ height))
    (nodes height (Nat.xor (index / 2 ^ height) 1))

/-- Combining the canonical pair at `height` yields the canonical parent at `height + 1`. -/
theorem canonical_step (nodes : Nat → Nat → α)
    (combine : Nat → Nat → α → α → α)
    (hnodes : ∀ height index, nodes (height + 1) index =
      combine (height + 1) index (nodes height (2 * index)) (nodes height (2 * index + 1)))
    (index height : Nat) :
    combine (height + 1) (index / 2 ^ (height + 1))
      (canonicalPair nodes index height).1 (canonicalPair nodes index height).2 =
      nodes (height + 1) (index / 2 ^ (height + 1)) := by
  have h := Correctness.parent_reconstruction nodes combine hnodes height (index / 2 ^ height)
  by_cases hparity : index / 2 ^ height % 2 = 0 <;>
    simpa only [canonicalPair, ordered, Correctness.div_pow_succ, hparity,
      ite_true, ite_false, Prod.fst, Prod.snd] using h

/-- A collision at `height` on the path of leaf `index`: the recomputed ordered pair differs from
the canonical one, yet both combine to the same parent. -/
def Collision (nodes : Nat → Nat → α) (combine : Nat → Nat → α → α → α)
    (index : Nat) (leaf : α) (siblings : Nat → α) (height : Nat) : Prop :=
  let actual := ordered index height (value combine index leaf siblings height) (siblings height)
  let canonical := canonicalPair nodes index height
  actual ≠ canonical ∧
    combine (height + 1) (index / 2 ^ (height + 1)) actual.1 actual.2 =
    combine (height + 1) (index / 2 ^ (height + 1)) canonical.1 canonical.2

/-- Either every supplied value on this path is canonical, or a concrete pair
of different child tuples hashes to the same parent at a queried position. -/
theorem canonical_or_collision (nodes : Nat → Nat → α)
    (combine : Nat → Nat → α → α → α)
    (hnodes : ∀ height index, nodes (height + 1) index =
      combine (height + 1) index (nodes height (2 * index)) (nodes height (2 * index + 1)))
    (index : Nat) (leaf : α) (siblings : Nat → α) (height : Nat)
    (hroot : value combine index leaf siblings height = nodes height (index / 2 ^ height)) :
    (leaf = nodes 0 index ∧ ∀ j < height,
      siblings j = nodes j (Nat.xor (index / 2 ^ j) 1)) ∨
    ∃ j < height, Collision nodes combine index leaf siblings j := by
  classical
  induction height with
  | zero => exact Or.inl ⟨by simpa [value] using hroot, by omega⟩
  | succ height ih =>
      let actual :=
        ordered index height (value combine index leaf siblings height) (siblings height)
      by_cases hpair : actual = canonicalPair nodes index height
      · have hvalues := (ordered_eq_iff index height _ _ _ _).mp hpair
        rcases ih hvalues.1 with hcanonical | ⟨j, hj, hcollision⟩
        · refine Or.inl ⟨hcanonical.1, ?_⟩
          intro j hj
          by_cases heq : j = height
          · subst j; exact hvalues.2
          · exact hcanonical.2 j (by omega)
        · exact Or.inr ⟨j, by omega, hcollision⟩
      · refine Or.inr ⟨height, by omega, hpair, ?_⟩
        exact hroot.trans (canonical_step nodes combine hnodes index height).symm

/-- The recursive values describe the increasing-height fold used by both
concrete FORS and XMSS verification. -/
theorem value_eq_fold (combine : Nat → Nat → α → α → α)
    (index : Nat) (leaf : α) (siblings : Nat → α) (height : Nat) :
    value combine index leaf siblings height =
      (List.finRange height).foldl (fun current j =>
        let pair := ordered index j.val current (siblings j.val)
        combine (j.val + 1) (index / 2 ^ (j.val + 1)) pair.1 pair.2) leaf := by
  symm
  exact Correctness.finRange_foldl height (value combine index leaf siblings)
    _ (fun _ => rfl)

/-- The byte encoding of an ordered pair of digests, as hashed by an internal tree node. -/
def pairBytes (pair : Digest × Digest) : Bytes := bytesBE n pair.1 ++ bytesBE n pair.2

end SlhDsaSecurity.Extraction.BinaryPath
