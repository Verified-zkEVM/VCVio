/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import HashSig.GXMSS.Merkle
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses

/-!
# Oriented raw Merkle collision controls
-/

public section

namespace GXMSS.MerkleWitnessProbe

open GXMSS.Security

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Disjoint constructors preserve each raw input form. -/
abbrev Input := ℕ ⊕ ((ℕ × ℕ) ⊕ (Fin 1 → ℕ))

/-- Finite chain and tree coordinates are embedded in separately tagged natural coordinates. -/
abbrev Tweak := (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ)

/-- A nonconstant, order-sensitive hash with deliberate parity collisions.
Each chain call adds its positive paper position; each node weights its right input by ten. -/
@[expose] def witnessInstance (h w : ℕ) : HashInstance Unit Tweak Input ℕ h w 1 where
  thf := {
    seedGen := pure ()
    eval := fun _ t x => match t, x with
      | .inl (_, _, j), .inl x => x / 2 + j + 1
      | .inr (z, i), .inr (.inl (l, r)) => l / 2 + 10 * (r / 2) + 100 * z + i
      | .inr (_, _), .inr (.inr xs) => xs 0 / 2
      | _, _ => 0 }
  digestInput := ⟨Sum.inl, by intro a b hab; exact Sum.inl.inj hab⟩
  pairInput := ⟨fun x => .inr (.inl x), by intro a b hab; exact Sum.inl.inj (Sum.inr.inj hab)⟩
  vectorInput := ⟨fun x => .inr (.inr x), by intro a b hab; exact Sum.inr.inj (Sum.inr.inj hab)⟩
  chainTweak := ⟨fun (e, i, j) => .inl (e.val, i.val, j.val), by
    intro a b hab
    simpa only [Sum.inl.injEq, Prod.ext_iff, Fin.ext_iff] using hab⟩
  treeTweak := ⟨fun (z, i) => .inr (z.val, i.val), by
    intro a b hab
    simpa only [Sum.inr.injEq, Prod.ext_iff, Fin.ext_iff] using hab⟩
  chain_ne_tree := by intro c t heq; cases c; cases t; cases heq

/-- Two distinct vectors with values two and three hash to the same leaf digest. -/
theorem leaf_compression :
    ((witnessInstance 3 3).findMerkleCollision () 5 (fun _ => 2) (fun _ => 3)
      ![4, 6, 8] ![4, 6, 8]).map (fun c => c.tweak) = some (.inr (0, 5)) := by decide

/-- A path-only leaf-sibling change four to five merges at parent (1,2).
Index five places the sibling on the left and the current digest on the right. -/
theorem path_only_low :
    ((witnessInstance 3 3).findMerkleCollision () 5 (fun _ => 2) (fun _ => 2)
      ![4, 6, 8] ![5, 6, 8]).map (fun c => (c.tweak, c.first, c.second)) =
      some (.inr (1, 2), .inr (.inl (4, 1)), .inr (.inl (5, 1))) := by rfl

/-- The next level places the computed 104 on the left and path sibling six on the right. -/
theorem path_only_middle :
    ((witnessInstance 3 3).findMerkleCollision () 5 (fun _ => 2) (fun _ => 2)
      ![4, 6, 8] ![4, 7, 8]).map (fun c => (c.tweak, c.first, c.second)) =
      some (.inr (2, 1), .inr (.inl (104, 6)), .inr (.inl (104, 7))) := by rfl

/-- The root places path sibling eight on the left and computed 283 on the right. -/
theorem path_only_root :
    ((witnessInstance 3 3).findMerkleCollision () 5 (fun _ => 2) (fun _ => 2)
      ![4, 6, 8] ![4, 6, 9]).map (fun c => (c.tweak, c.first, c.second)) =
      some (.inr (3, 0), .inr (.inl (8, 283)), .inr (.inl (9, 283))) := by rfl

/-- Height zero still returns the distinct raw vectors' leaf collision. -/
theorem height_zero :
    ((witnessInstance 0 0).findMerkleCollision () 0 (fun _ => 2) (fun _ => 3)
      Fin.elim0 Fin.elim0).map (fun c => c.tweak) = some (.inr (0, 0)) := by decide

end GXMSS.MerkleWitnessProbe
