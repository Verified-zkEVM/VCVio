/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Scheme
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# Ordered XMSS recovery views

The addressed Merkle climb recovers addressed XMSS nodes along arbitrary leaf-first paths.
The finite-family view exposes the same ordered parent hashes as a fold over path heights.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Merkle

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- An empty XMSS path returns its starting leaf without another oracle call. -/
theorem climb_nil (publicSeed : Digest) (address : Address) (index : Nat) (leaf : Digest) :
    climb (m := m) publicSeed address index leaf [] = pure leaf := by
  simp only [climb, PerfectMerkleTree.climbM_nil]

/-- Appending a sibling hashes the previous root and that sibling at the next height. -/
theorem climb_concat (publicSeed : Digest) (address : Address) (index : Nat) (leaf : Digest)
    (authentication : List Digest) (sibling : Digest) :
    climb (m := m) publicSeed address index leaf (authentication ++ [sibling]) = (do
      let value ← climb publicSeed address index leaf authentication
      let payload := if index / 2 ^ authentication.length % 2 = 0 then
        bytesBE n value ++ bytesBE n sibling
        else bytesBE n sibling ++ bytesBE n value
      Hashing.tweakable publicSeed
        (nodeAddress address (authentication.length + 1)
          (index / 2 ^ (authentication.length + 1))) payload : m Digest) := by
  simp only [climb, PerfectMerkleTree.climbM_concat]
  congr 1
  funext value
  split_ifs <;> rfl

variable [LawfulMonad m]

/-- An indexed XMSS path climbs through its ordered parent hashes. -/
theorem climb_eq_fold (publicSeed : Digest) (address : Address) (index : Nat)
    (leaf : Digest) {height : Nat} (authentication : Fin height → Digest) :
    climb (m := m) publicSeed address index leaf (List.ofFn authentication) =
      (List.finRange height).foldlM (fun value j => do
        let payload := if index / 2 ^ j.val % 2 = 0 then
          bytesBE n value ++ bytesBE n (authentication j)
          else bytesBE n (authentication j) ++ bytesBE n value
        Hashing.tweakable publicSeed (nodeAddress address (j.val + 1)
          (index / 2 ^ (j.val + 1))) payload) leaf := by
  rw [climb, PerfectMerkleTree.climbM_ofFn]
  apply congrArg (fun step : Digest → Fin height → m Digest =>
    (List.finRange height).foldlM step leaf)
  funext value j
  split_ifs <;> rfl

/-- XMSS recovery first recovers the WOTS+ key, then folds the supplied sibling path. -/
theorem publicKeyFromSignature_eq_fold (index : Fin (2 ^ subtreeHeight))
    (signature : XmssSignature) (message publicSeed : Digest) (address : Address) :
    publicKeyFromSignature (m := m) index signature message publicSeed address = (do
      let leaf ← Wots.publicKeyFromSignature signature.wots message publicSeed
        (wotsAddress address index.val)
      (List.finRange subtreeHeight).foldlM (fun value j => do
        let payload := if index.val / 2 ^ j.val % 2 = 0 then
          bytesBE n value ++ bytesBE n (signature.authentication j)
          else bytesBE n (signature.authentication j) ++ bytesBE n value
        Hashing.tweakable publicSeed
          (nodeAddress address (j.val + 1) (index.val / 2 ^ (j.val + 1))) payload) leaf :
      m Digest) := by
  simp only [publicKeyFromSignature, climb_eq_fold]

end SLHDSA.SHAKE128s.Merkle
