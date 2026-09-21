/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed

/-!
# Classifying the nodes of a perfect tree against one leaf's root path

In the perfect tree of height `hp` over heap-style `(height, horizontal index)` addresses, fix a
leaf `idx`.  Every node `(z, t)` of the tree is either the height-`z` ancestor `idx / 2 ^ z` of
that leaf, or lies in the subtree rooted at the sibling of the ancestor at some height
`z ≤ s < hp`.  This is the shape in which an XMSS authentication path covers the tree: the path
entries are exactly the sibling subtree roots, so everything a signature does not sit on is under
one of them.

## Scope

* Pure arithmetic on `PerfectMerkleTree.sibling` and natural-number division; no tree data, hash
  or monad is involved.
* Nothing here is probabilistic, and nothing here is quantum.

## Labels

Three declarations: `div_pow_eq_div_pow_div_pow`, `eq_sibling_of_div_two_eq`,
`eq_div_pow_or_exists_sibling`.
-/

public section

namespace PerfectMerkleTree

/-- The height-`z` ancestor of `i` is the height-`(z - s)` ancestor of its height-`s` ancestor,
for `s ≤ z`. -/
theorem div_pow_eq_div_pow_div_pow (i s z : ℕ) (hsz : s ≤ z) :
    i / 2 ^ z = i / 2 ^ s / 2 ^ (z - s) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hsz]

/-- Two distinct nodes with the same parent are siblings. -/
theorem eq_sibling_of_div_two_eq {a b : ℕ} (h : a / 2 = b / 2) (hne : a ≠ b) : a = sibling b := by
  unfold sibling
  split_ifs <;> omega

/-- In the perfect tree of height `hp`, a node `(z, t)` is the height-`z` ancestor of leaf
`idx`, or lies in the subtree of the sibling of that ancestor at some height `z ≤ s < hp`. -/
theorem eq_div_pow_or_exists_sibling {idx hp z t : ℕ} (hidx : idx < 2 ^ hp) (hz : z ≤ hp)
    (ht : t < 2 ^ (hp - z)) :
    t = idx / 2 ^ z ∨ ∃ s, z ≤ s ∧ s < hp ∧ t / 2 ^ (s - z) = sibling (idx / 2 ^ s) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hz
  clear hz
  induction k generalizing z t with
  | zero =>
    simp only [Nat.add_zero, Nat.sub_self, pow_zero, Nat.lt_one_iff] at ht
    exact Or.inl (by rw [ht, Nat.div_eq_of_lt (by simpa using hidx)])
  | succ k ih =>
    have hidx' : idx < 2 ^ (z + 1 + k) := by rwa [Nat.add_right_comm]
    have ht' : t / 2 < 2 ^ (z + 1 + k - (z + 1)) := by
      rw [show z + 1 + k - (z + 1) = k by omega]
      rw [show z + (k + 1) - z = k + 1 by omega, pow_succ] at ht
      omega
    rcases ih hidx' ht' with h | ⟨s, hzs, hs, hsib⟩
    · by_cases hte : t = idx / 2 ^ z
      · exact Or.inl hte
      · refine Or.inr ⟨z, le_rfl, by omega, ?_⟩
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        exact eq_sibling_of_div_two_eq (by rw [h, pow_succ, Nat.div_div_eq_div_mul]) hte
    · refine Or.inr ⟨s, by omega, by omega, ?_⟩
      rw [← hsib, div_pow_eq_div_pow_div_pow t 1 (s - z) (by omega), pow_one, Nat.sub_sub]

end PerfectMerkleTree
