/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Xmss
public import VCVio.CryptoFoundations.MerkleTree.Perfect.SimulateQ

/-!
# Perfect-Merkle Compatibility for SLH-DSA

The oracle-parametric SLH-DSA layer uses `PerfectMerkleTree`, whose authentication paths are
length-indexed vectors. The original executable specification uses `SLHDSA.Merkle` and lists.
This module proves that their deterministic roots, path generation, and path folding agree after
erasing the vector length proof.
-/

@[expose] public section

namespace SLHDSA.Merkle

open PerfectMerkleTree

variable {Y : Type}

/-- The perfect-tree root is the legacy SLH-DSA Merkle root under the coordinate adapter. -/
@[simp]
theorem treeHash_eq_merkleRoot (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (height index : ℕ) :
    treeHash leaf (fun address => nodeHash address.height address.index) height index =
      merkleRoot leaf nodeHash height index := by
  induction height generalizing index with
  | zero => rfl
  | succ height ih => simp [treeHash, merkleRoot, ih]

/-- Erasing the sized perfect-tree authentication path gives the legacy list path. -/
theorem authenticationPath_toList_eq_authPath
    (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) :
    ∀ (depth base index : ℕ),
      (authenticationPath leaf (fun address => nodeHash address.height address.index)
        base index depth).toList = authPath leaf nodeHash base index depth := by
  intro depth
  induction depth with
  | zero =>
      intro base index
      rfl
  | succ depth ih =>
      intro base index
      have legacyStep : authPath leaf nodeHash base index (depth + 1) =
          merkleRoot leaf nodeHash base (Merkle.sibling index) ::
            authPath leaf nodeHash (base + 1) (index / 2) depth := by
        simp only [authPath, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero,
          Nat.div_one, Nat.add_zero]
        refine congrArg _ (List.map_congr_left fun j _ => ?_)
        simp only [Function.comp_apply]
        have hb : base + (j + 1) = base + 1 + j := by omega
        have hd : index / 2 ^ (j + 1) = index / 2 / 2 ^ j := by
          rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
        rw [hb, hd]
      rw [legacyStep]
      simp only [authenticationPath, List.Vector.toList_cons]
      rw [treeHash_eq_merkleRoot, ih (base + 1) (index / 2)]
      rfl

/-- Folding a sized perfect-tree path agrees with folding its erased legacy list. -/
theorem climb_eq_climb (nodeHash : ℕ → ℕ → Y → Y → Y) :
    ∀ (depth base index : ℕ) (node : Y) (path : AuthenticationPath Y depth),
      PerfectMerkleTree.climb (fun address => nodeHash address.height address.index)
          base index depth node path =
        Merkle.climb nodeHash base index node path.toList := by
  intro depth
  induction depth with
  | zero =>
      intro base index node path
      rw [vector_eq_nil path]
      rfl
  | succ depth ih =>
      intro base index node path
      have hpath : path.toList = path.head :: path.tail.toList := by
        calc
          path.toList = (List.Vector.cons path.head path.tail).toList :=
            congrArg List.Vector.toList path.cons_head_tail.symm
          _ = path.head :: path.tail.toList := rfl
      rw [hpath]
      by_cases h : index % 2 = 0 <;>
        simp [PerfectMerkleTree.climb, Merkle.climb, h, ih]

end SLHDSA.Merkle
