/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Wots
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.BinaryPath

/-! Every honest FORS path reconstructs its indexed tree root under any fixed hash. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Correctness.Fors

variable [HasQuery HashSpec Id]

theorem publicKeyFromSignature_sign (indices : SlhDsaSecurity.Fors.Indices)
    (secretSeed publicSeed : Digest) (address : Address) :
    SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id)
        (SlhDsaSecurity.Fors.sign (m := Id) indices secretSeed publicSeed address)
        indices publicSeed address =
      Hashing.tweakable (m := Id) publicSeed
        { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
        (digestArrayBytes fun i : Fin forsTrees =>
          SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address forsHeight i.val) := by
  simp only [SlhDsaSecurity.Fors.sign, SlhDsaSecurity.Fors.publicKeyFromSignature,
    sequenceFin_id, bind, pure, foldlM_id]
  apply congrArg (fun roots : Fin forsTrees → Digest =>
    Hashing.tweakable (m := Id) publicSeed
      { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
      (digestArrayBytes roots))
  funext i
  have hpath := recover_path
    (SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address)
    (fun height nodeIndex left right => Hashing.tweakable (m := Id) publicSeed
      (SlhDsaSecurity.Fors.nodeAddress address height nodeIndex)
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

end SlhDsaSecurity.Correctness.Fors
