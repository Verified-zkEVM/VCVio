/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Evaluation
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Fors
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Merkle

/-!
# Honest signatures disclose canonical cells

The components of an honest signature are cells of the canonical graph's evaluation `value`: a
WOTS+ signature discloses, on each chain, the cell at the position the message's checksum
encoding selects (`wotsPosition`, `wots_sign_cells`); FORS secrets are the cells of their PRF
nodes (`fors_secret_cell`); the FORS public key recomputed from an honest signature is the cell of
the roots node (`fors_publicKey_cell`); and the public-key root is the cell of the top Merkle node
(`topRoot`, `keygen_root_cell`). Messages only select positions; the disclosed values are fixed by
the seeds.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CanonicalGraph

/-- Position zero is the PRF-derived secret; position fifteen is the chain endpoint. -/
def wotsPosition (key : WotsKey) (chain : Fin chains) (position : Fin w) : StructuralNode :=
  if hzero : position.val = 0 then .wotsPrf key chain
  else .wotsHash key chain ⟨position.val - 1, by have := position.isLt; omega⟩

/-- The root node of the top hypertree layer, whose cell is the public-key root. -/
def topRoot : StructuralNode :=
  .tree ⟨⟨layers - 1, by decide⟩, ⟨0, by decide⟩⟩
    ⟨subtreeHeight - 1, by decide⟩ ⟨0, by decide⟩

variable [HasQuery HashSpec Id]

/-- The cell at a WOTS+ chain position is the chain value at that position. -/
theorem value_wotsPosition (secretSeed publicSeed : Digest) (key : WotsKey)
    (chain : Fin chains) (position : Fin w) :
    value secretSeed publicSeed (.structural (wotsPosition key chain position)) =
      Wots.chain (m := Id) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 position.val
        (Hashing.derive (m := Id) publicSeed secretSeed
          (Wots.secretAddress key.address chain)) := by
  unfold wotsPosition
  split
  · rename_i hzero
    simp only [value, structuralValue, hzero, Wots.chain, pure]
  · rename_i hzero
    simp only [value, structuralValue]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ position.val)]

/-- A WOTS+ signature discloses, on each chain, the cell at the position the message selects. -/
theorem wots_sign_cells (message secretSeed publicSeed : Digest) (key : WotsKey) :
    Wots.sign (m := Id) message secretSeed publicSeed key.address =
      fun chain => value secretSeed publicSeed
        (.structural (wotsPosition key chain (Checksum.encode message chain))) := by
  simp only [Wots.sign, Correctness.sequenceFin_id, bind]
  funext chain
  exact (value_wotsPosition _ _ _ _ _).symm

/-- A FORS secret is the cell of its PRF node. -/
theorem fors_secret_cell (secretSeed publicSeed : Digest) (key : ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) :
    Fors.secret (m := Id) secretSeed publicSeed key.address index.val =
      value secretSeed publicSeed (.structural (.forsPrf key index)) := rfl

/-- Every selected FORS message authenticates the same canonical collection of roots. -/
theorem fors_publicKey_cell (indices : Fors.Indices) (secretSeed publicSeed : Digest)
    (key : ForsKey) :
    Fors.publicKeyFromSignature (m := Id)
        (Fors.sign (m := Id) indices secretSeed publicSeed key.address)
        indices publicSeed key.address =
      value secretSeed publicSeed (.structural (.forsRoots key)) :=
  Correctness.Fors.publicKeyFromSignature_sign _ _ _ _

/-- The public-key root is the cell of the top Merkle node. -/
theorem keygen_root_cell (secretSeed prfSeed publicSeed : Digest) :
    (Scheme.keygenInternal (m := Id) secretSeed prfSeed publicSeed).2.root =
      value secretSeed publicSeed (.structural topRoot) := rfl

end SlhDsaSecurity.CanonicalGraph
