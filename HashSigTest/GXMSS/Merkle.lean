/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Merkle
import all HashSig.GXMSS.Merkle
public import HashSigTest.GXMSS.Chain

/-!
# Merkle foundation probes

Registered audit root for the corresponding deterministic or probability foundations.
-/

public section

namespace GXMSS.MerkleProbe

/-- Index two has siblings three, zero and one from leaf level upward. -/
theorem siblings_two : Merkle.siblingAddresses 2 3 = ![(0, 3), (1, 0), (2, 1)] := by decide

/-- Index five has siblings four, three and zero from leaf level upward. -/
theorem siblings_five : Merkle.siblingAddresses 5 3 = ![(0, 4), (1, 3), (2, 0)] := by decide

/-- Verification of index two hashes under these parent tweaks. -/
theorem parents_two : Merkle.parentAddresses 2 3 = ![(1, 1), (2, 0), (3, 0)] := by decide

/-- Verification of index five hashes under these parent tweaks. -/
theorem parents_five : Merkle.parentAddresses 5 3 = ![(1, 2), (2, 1), (3, 0)] := by decide

/-- The actual engine returns leaf-first sibling addresses for index two. -/
theorem engine_siblings_two :
    PerfectMerkleTree.authPath (fun i => (0, i)) (fun z i _ _ => (z, i)) 2 3 =
      [(0, 3), (1, 0), (2, 1)] := rfl

/-- The actual engine returns leaf-first sibling addresses for index five. -/
theorem engine_siblings_five :
    PerfectMerkleTree.authPath (fun i => (0, i)) (fun z i _ _ => (z, i)) 5 3 =
      [(0, 4), (1, 3), (2, 0)] := rfl

/-- All height-three construction calls, including hashed leaves, in left/right order. -/
theorem engine_all_calls :
    PerfectMerkleTree.merkleRoot (fun i => [(0, i)])
      (fun z i l r => l ++ r ++ [(z, i)]) 3 0 =
        [(0, 0), (0, 1), (1, 0), (0, 2), (0, 3), (1, 1), (2, 0),
          (0, 4), (0, 5), (1, 2), (0, 6), (0, 7), (1, 3), (2, 1), (3, 0)] := rfl

/-- The zero-height construction still makes its sole leaf-hash call. -/
theorem engine_zero_call :
    PerfectMerkleTree.merkleRoot (fun i => [(0, i)])
      (fun z i l r => l ++ r ++ [(z, i)]) 0 0 = [(0, 0)] := rfl

/-- The actual adapter calls all eight vector hashes and seven ordered pair hashes. -/
theorem adapter_all_calls :
    (ChainProbe.traceInstance 3 3).merkleRoot () (fun _ _ => []) =
      [2000, 0, 0, 2000, 0, 1, 3000, 1, 0,
        2000, 0, 2, 2000, 0, 3, 3000, 1, 1, 3000, 2, 0,
        2000, 0, 4, 2000, 0, 5, 3000, 1, 2,
        2000, 0, 6, 2000, 0, 7, 3000, 1, 3, 3000, 2, 1, 3000, 3, 0] := by decide

/-- Recovery at index two has current-child order left, right, left. -/
theorem adapter_recovery_two :
    (ChainProbe.traceInstance 3 3).recoverRoot () 2 (fun _ => []) ![[9000], [9001], [9002]] =
      [9001, 2000, 0, 2, 9000, 3000, 1, 1, 3000, 2, 0, 9002, 3000, 3, 0] := by decide

/-- Recovery at index five has current-child order right, left, right. -/
theorem adapter_recovery_five :
    (ChainProbe.traceInstance 3 3).recoverRoot () 5 (fun _ => []) ![[9000], [9001], [9002]] =
      [9002, 9000, 2000, 0, 5, 3000, 1, 2, 9001, 3000, 2, 1, 3000, 3, 0] := by decide

/-- Height-zero recovery performs its sole vector hash and no pair hashes. -/
theorem adapter_recovery_zero :
    (ChainProbe.traceInstance 0 3).recoverRoot () 0 (fun _ => []) Fin.elim0 = [2000, 0, 0] := by
  decide

/-- Height-zero construction preserves the vector input and hashes it once. -/
theorem adapter_root_zero :
    (ChainProbe.traceInstance 0 3).merkleRoot () (fun _ _ => [91]) =
      [91, 2000, 0, 0] := by decide

/-- Finite parent-address helpers preserve the index-two convention. -/
theorem finite_parents_two :
    (fun z : Fin 3 =>
      let address := Merkle.parentAddress (h := 3) 2 z
      let level := address.1
      let index := address.2
      (level.val, index.val)) =
      ![(1, 1), (2, 0), (3, 0)] := by decide

/-- Finite parent-address helpers preserve the index-five convention. -/
theorem finite_parents_five :
    (fun z : Fin 3 =>
      let address := Merkle.parentAddress (h := 3) 5 z
      let level := address.1
      let index := address.2
      (level.val, index.val)) =
      ![(1, 2), (2, 1), (3, 0)] := by decide

/-- There is no pair-hash agreement obligation at height zero. -/
theorem zero_node_agreement {Y : Type*} (f g : Fin 1 → Fin 1 → Y → Y → Y) :
    Merkle.NodeHashAgreement 0 f g := by
  intro z t hz
  have hp := hz.1
  have bounds := hz.2
  have hle := bounds.1
  omega

variable {PP T X H : Type} {h w v : ℕ}

/-- Chain completion and honest Merkle recovery compose without caller-side range proofs. -/
theorem completed_chains_recover (P : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) (digits : Fin v → Fin (2 ^ w)) (e : Fin (2 ^ h)) :
    P.recoverRoot pp e
      (fun i => P.chain pp e i (digits i) (2 ^ w - 1 - (digits i).val)
        (P.chain pp e i 0 (digits i) (starts e i)))
      (P.authPath pp (fun ep i => P.chain pp ep i 0 (2 ^ w - 1) (starts ep i)) e) =
        P.merkleRoot pp (fun ep i => P.chain pp ep i 0 (2 ^ w - 1) (starts ep i)) := by
  simp_rw [HashInstance.chain_complete_digit]
  exact P.recoverRoot_authPath pp
    (fun ep i => P.chain pp ep i 0 (2 ^ w - 1) (starts ep i)) e

/-- Empty endpoint vectors need no positivity or inhabited-digest assumption. -/
theorem empty_vectors_recover (P : HashInstance PP T X H h w 0) (pp : PP)
    (e : Fin (2 ^ h)) :
    P.recoverRoot pp e Fin.elim0 (P.authPath pp (fun _ => Fin.elim0) e) =
      P.merkleRoot pp (fun _ => Fin.elim0) :=
  P.recoverRoot_authPath pp (fun _ => Fin.elim0) e

end GXMSS.MerkleProbe
