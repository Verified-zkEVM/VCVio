/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.HonestProbes
public import HashSig.SLHDSA.SHAKE128s.Proof.SensitiveShape

/-!
# The digit each hypertree key reveals, read off the table

Each WOTS key of the hypertree signs one message, and that message is a public cell: at the
bottom layer the FORS public key at the key's leaf, above it the root of the subtree one layer
down. So the digit a key reveals on a chain is a function of one always-available cell, and the
shared half's availability is defined that way (`revealedOf`).

`GraphStakes.honestRevealed` replays the warm cache to the same digits, but it is defined at
every key of the padded graph, including keys whose subtree below lies outside the hypertree's
index range; there the replay reads entries no table holds, and showing it reads no cell would
mean showing every one of those lookups misses. `revealedOf` gives such keys the most
restrictive digit, `w - 1`, under which only the always-available cells are available — so
nothing outside the hypertree is ever made available, and the digit is plainly blind to every
cell but the always-available ones (`revealedOf_congr`).
-/

@[expose] public section

namespace SlhDsaSecurity.ShareCells

open CanonicalGraph

/-- **The node whose cell a hypertree key signs**, for a key the hypertree uses. -/
def messageNode (key : WotsKey) : Option StructuralNode :=
  match key.tree.layer.val with
  | 0 => some (.forsRoots ⟨key.tree.tree, key.leaf⟩)
  | layer + 1 =>
    if hlayer : layer < layers then
      if htree : key.tree.tree.val * 2 ^ subtreeHeight + key.leaf.val <
          2 ^ (totalHeight - subtreeHeight) then
        some (HonestProbes.subtreeRootNode ⟨⟨layer, hlayer⟩, ⟨_, htree⟩⟩)
      else none
    else none

/-- **The digit each key reveals on a chain**, read off the table. -/
def revealedOf (cells : Cells) (key : WotsKey) (chain : Fin chains) : Nat :=
  match messageNode key with
  | some node => (Checksum.encode (cells (.structural node)) chain).val
  | none => w - 1

/-- A revealed digit is at most `w - 1`. -/
theorem revealedOf_le (cells : Cells) (key : WotsKey) (chain : Fin chains) :
    revealedOf cells key chain ≤ w - 1 := by
  unfold revealedOf
  split
  · rename_i node _
    have := (Checksum.encode (cells (.structural node)) chain).isLt
    omega
  · exact le_refl _

/-- The signed cell is always available. -/
theorem alwaysAvailable_messageNode (key : WotsKey) (node : StructuralNode)
    (hnode : messageNode key = some node) : AlwaysAvailable (.structural node) := by
  unfold messageNode at hnode
  split at hnode
  · cases hnode
    exact True.intro
  · split_ifs at hnode
    cases hnode
    exact alwaysAvailable_merkleNode _ _ _ _

/-- **The digits read only always-available cells.** -/
theorem revealedOf_congr (left right : Cells)
    (hagree : ∀ node, AlwaysAvailable node → left node = right node) :
    revealedOf left = revealedOf right := by
  funext key chain
  unfold revealedOf
  split
  · rename_i node hnode
    rw [hagree _ (alwaysAvailable_messageNode key node hnode)]
  · rfl

end SlhDsaSecurity.ShareCells
