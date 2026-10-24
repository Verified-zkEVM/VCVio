/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Wots
public import HashSig.SLHDSA.SHAKE128s.Proof.ChecksumAntichain

/-!
# Honest WOTS signature values as chains

When a layer's canonical branch forces `sig.wots = Wots.sign forged` for a message `forged` that
differs from the honestly signed message `signed` at the same WOTS key, the checksum antichain
gives a chain on which the forged value is a strict chain-ancestor of the honestly revealed
value: advancing the forged value reaches the honest one. This file supplies the chain-arithmetic
ingredient of that witness: `chainAddress` names the per-chain address, and `sign_eq_chain`
writes each honest signature value as the chain started from the derived secret and advanced to
its message digit. No one-wayness is assumed here.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Extraction.WotsPreimage

variable [HasQuery HashSpec Id]

/-- The chain-step address of chain `i` for this WOTS key. -/
@[expose] def chainAddress (address : Address) (i : Fin chains) : Address :=
  { address with chainOrHeight := BitVec.ofNat 32 i.val }

/-- Each honest WOTS signature value is the chain started from the derived secret,
advanced to the message digit. -/
theorem sign_eq_chain (message secretSeed publicSeed : Digest) (address : Address)
    (i : Fin chains) :
    SlhDsaSecurity.Wots.sign (m := Id) message secretSeed publicSeed address i =
      SlhDsaSecurity.Wots.chain (m := Id) publicSeed (chainAddress address i)
        0 (Checksum.encode message i).val
        (Hashing.derive (m := Id) publicSeed secretSeed
          (SlhDsaSecurity.Wots.secretAddress address i)) := by
  simp only [SlhDsaSecurity.Wots.sign, Correctness.sequenceFin_id, bind, chainAddress]

end SlhDsaSecurity.Extraction.WotsPreimage
