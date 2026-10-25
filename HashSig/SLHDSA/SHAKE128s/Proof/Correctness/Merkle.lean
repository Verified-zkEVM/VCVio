/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Wots
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.BinaryPath

/-!
# XMSS subtree correctness

Correctness of an XMSS subtree under a fixed hash, including its actual path fold:
`publicKeyFromSignature_sign` shows that the root recovered from an honest XMSS signature is the
subtree root computed by `Merkle.node`.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Correctness.Merkle

variable [HasQuery HashSpec Id]

/-- Verifying an honest XMSS signature recovers the subtree root. -/
theorem publicKeyFromSignature_sign (message secretSeed publicSeed : Digest)
    (address : Address) (index : Fin (2 ^ subtreeHeight)) :
    SLHDSA.SHAKE128s.Merkle.publicKeyFromSignature (m := Id) index
        (SLHDSA.SHAKE128s.Merkle.sign (m := Id) message secretSeed publicSeed address index)
        message publicSeed address =
      SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed address subtreeHeight 0 := by
  simp only [SLHDSA.SHAKE128s.Merkle.sign, SLHDSA.SHAKE128s.Merkle.publicKeyFromSignature,
    sequenceFin_id, bind, pure, Wots.publicKeyFromSignature_sign, foldlM_id]
  have hpath := recover_path
    (SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed address)
    (fun height nodeIndex left right => Hashing.tweakable (m := Id) publicSeed
      (SLHDSA.SHAKE128s.Merkle.nodeAddress address height nodeIndex)
      (bytesBE n left ++ bytesBE n right))
    (fun _ _ => rfl) subtreeHeight index.val
  rw [Nat.div_eq_of_lt index.isLt] at hpath
  convert hpath using 1
  congr 1
  funext value j
  split <;> rfl

end SLHDSA.SHAKE128s.Correctness.Merkle
