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
# FORS correctness

Deterministic correctness of FORS under any fixed hash, run in `Id`: every authentication path
of an honest FORS signature reconstructs the root of its indexed tree, so
`Fors.publicKeyFromSignature_sign` recovers the compressed FORS public key.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Correctness.Fors

variable [HasQuery HashSpec Id]

/-- Recovering the FORS public key from an honest signature returns the compression of the
`forsTrees` tree roots. -/
theorem publicKeyFromSignature_sign (indices : SLHDSA.SHAKE128s.Fors.Indices)
    (secretSeed publicSeed : Digest) (address : Address) :
    SLHDSA.SHAKE128s.Fors.publicKeyFromSignature (m := Id)
        (SLHDSA.SHAKE128s.Fors.sign (m := Id) indices secretSeed publicSeed address)
        indices publicSeed address =
      Hashing.tweakable (m := Id) publicSeed
        { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
        (digestArrayBytes fun i : Fin forsTrees =>
          SLHDSA.SHAKE128s.Fors.node (m := Id) secretSeed publicSeed address forsHeight i.val) := by
  simp only [SLHDSA.SHAKE128s.Fors.sign, SLHDSA.SHAKE128s.Fors.publicKeyFromSignature,
    sequenceFin_id, bind, pure, foldlM_id]
  apply congrArg (fun roots : Fin forsTrees → Digest =>
    Hashing.tweakable (m := Id) publicSeed
      { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
      (digestArrayBytes roots))
  funext i
  have hpath := recover_path
    (SLHDSA.SHAKE128s.Fors.node (m := Id) secretSeed publicSeed address)
    (fun height nodeIndex left right => Hashing.tweakable (m := Id) publicSeed
      (SLHDSA.SHAKE128s.Fors.nodeAddress address height nodeIndex)
      (bytesBE n left ++ bytesBE n right))
    (fun _ _ => rfl) forsHeight (i.val * 2 ^ forsHeight + (indices i).val)
  rw [offset_div_pow _ _ _ _ (Nat.le_refl _), Nat.sub_self, pow_zero, Nat.mul_one,
    Nat.div_eq_of_lt (indices i).isLt, Nat.add_zero] at hpath
  convert hpath using 1
  congr 1
  funext value j
  have hj := j.isLt
  have heven := offset_even i.val forsHeight j.val hj
  rw [offset_div_pow _ _ _ _ (Nat.le_of_lt hj), xor_add_even _ _ heven]
  have hparity :
      (i.val * 2 ^ (forsHeight - j.val) + (indices i).val / 2 ^ j.val) % 2 =
        (indices i).val / 2 ^ j.val % 2 := by
    simp [Nat.add_mod, heven]
  rw [hparity]
  split <;> rfl

end SLHDSA.SHAKE128s.Correctness.Fors
