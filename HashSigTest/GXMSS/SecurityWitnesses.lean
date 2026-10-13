/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.HashWitnesses
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.TCRSimulation
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Chain
public import HashSig.GXMSS.HashInstance
public import HashSig.GXMSS.Chain
public import HashSig.GXMSS.Merkle
public import HashSig.GXMSS.Encoding.Incomparable

/-!
# Deterministic security witness audit root

Imports the accepted foundations for the corresponding proof modules.
-/

public section

namespace GXMSS.SecurityWitnessProbe

#check @Reductions.tcrEval_run_of_fresh
#check @Reductions.tcrFullChain_run
#check @Reductions.tcrFullChain_fallback_irrelevant
#check @Reductions.endpointTargets_length
#check @Reductions.chainTarget_mem_endpointTargets
#check @Reductions.tcrEndpoints_run_empty
#check @Reductions.tcrChainSetup_run
#check @Reductions.merkleTargets_length
#check @Reductions.merkleTargets_tweaks_nodup
#check @HashInstance.mem_merkleOpeningQueries_honest_shape
#check @Reductions.merkleOpeningTarget_mem_merkleTargets
#check @Reductions.tcrMerkleRoot_run
#check @Reductions.merkleOpeningTarget_mem_registeredHistory
#check @Reductions.tcrKeySetup_run
#check @Reductions.mem_honestOpeningTargets
#check @Reductions.TCRKeyState.keys_eq
#check @Reductions.tcrKeySetup_keys_run
#check @Reductions.tcrKeySetup_observe_run
#check @Reductions.tcrKeySetup_observe_evalDist
#check @Reductions.chainProblem_capacity
#check @Reductions.merkleProblem_capacity
#check @Reductions.registeredIndex_spec
#check @Reductions.chainTarget_registeredIndex_spec
#check @Reductions.merkleOpeningTarget_registeredIndex_spec

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

/-- Two starts merge at paper position three, whose finite tweak coordinate is two. -/
theorem aligned : (witnessInstance 3 3).findChainCollision () 5 0 2 3 8 9 = some 0 := by decide

/-- The designated value is reached at position two from predecessor four. -/
theorem cut_preimage :
    (witnessInstance 3 3).findChainCut () 5 0 0 2 3 4 6 = some (.inl 4) := by decide

/-- At cut two, values four and five merge strictly after the cut, at position three. -/
theorem cut_collision :
    (witnessInstance 3 3).findChainCut () 5 0 0 2 3 4 10 = some (.inr 0) := by decide

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

/-- Empty vectors admit no unequal coordinate. -/
theorem empty_coordinate : Security.findUnequalCoordinate (H := ℕ) Fin.elim0 Fin.elim0 = none := by
  decide

/-- The first actual digest difference is selected. -/
theorem digest_coordinate : Security.findUnequalCoordinate ![3, 4, 5] ![3, 9, 5] = some 1 := by
  decide

/-- The second word first falls below the first word at coordinate one. -/
theorem smaller_coordinate :
    Security.findSmallerCoordinate (radix := 4) ![1, 3, 0] ![2, 1, 1] = some 1 := by decide

end GXMSS.SecurityWitnessProbe
