/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-! Deterministic correctness of the standard WOTS+ algorithms under any fixed hash. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Correctness

@[simp] theorem sequenceFin_id {α : Type} (size : Nat) (f : Fin size → Id α) :
    sequenceFin size f = f := by
  induction size with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ size ih =>
      simp only [sequenceFin, ih, bind, pure]
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

namespace Wots

variable [HasQuery HashSpec Id]

/-- Splitting a chain preserves both the hash inputs and their order. -/
theorem chain_add (publicSeed : Digest) (address : Address)
    (start first second : Nat) (value : Digest) :
    SlhDsaSecurity.Wots.chain (m := Id) publicSeed address start (first + second) value =
      SlhDsaSecurity.Wots.chain (m := Id) publicSeed address (start + first) second
        (SlhDsaSecurity.Wots.chain (m := Id) publicSeed address start first value) := by
  induction first generalizing start value with
  | zero => rw [Nat.zero_add]; rfl
  | succ first ih =>
      have hstart : start + 1 + first = start + (first + 1) := by omega
      simpa only [Nat.succ_add, SlhDsaSecurity.Wots.chain, bind, hstart] using
        ih (start + 1)
          (Hashing.tweakable (m := Id) publicSeed
            { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value))

/-- Recovering the public key from an honest WOTS signature always succeeds. -/
theorem publicKeyFromSignature_sign (message secretSeed publicSeed : Digest)
    (address : Address) :
    SlhDsaSecurity.Wots.publicKeyFromSignature (m := Id)
        (SlhDsaSecurity.Wots.sign (m := Id) message secretSeed publicSeed address)
        message publicSeed address =
      SlhDsaSecurity.Wots.publicKey (m := Id) secretSeed publicSeed address := by
  simp only [SlhDsaSecurity.Wots.sign, SlhDsaSecurity.Wots.publicKeyFromSignature,
    SlhDsaSecurity.Wots.publicKey, sequenceFin_id, bind]
  congr 2
  funext i
  have digit_le : (Checksum.encode message i).val ≤ w - 1 := by
    have := (Checksum.encode message i).isLt
    simp only [w, winternitzBits] at *
    omega
  simpa only [Nat.zero_add, Nat.add_sub_of_le digit_le] using
    (chain_add publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
      0 (Checksum.encode message i).val (w - 1 - (Checksum.encode message i).val)
      (Hashing.derive (m := Id) publicSeed secretSeed
        (SlhDsaSecurity.Wots.secretAddress address i))).symm

end Wots
end SlhDsaSecurity.Correctness
