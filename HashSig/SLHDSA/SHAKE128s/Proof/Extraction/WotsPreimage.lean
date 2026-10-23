/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Wots
public import HashSig.SLHDSA.SHAKE128s.Proof.ChecksumAntichain

/-! The WOTS one-wayness witness for a hypertree layer transition.

When a layer's canonical branch forces `sig.wots = Wots.sign forged` for a message
`forged` that differs from the honestly signed message `signed` at the same WOTS key,
the checksum antichain yields a chain where the forged value is a strict chain-ancestor
of the honestly revealed value: advancing the forged value reaches the honest one. This
is a pure chain-arithmetic witness, feeding the ROM preimage probability charge. No
one-wayness is assumed here. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Extraction.WotsPreimage

variable [HasQuery HashSpec Id]

/-- The chain-step address of chain `i` for this WOTS key. -/
def chainAddress (address : Address) (i : Fin chains) : Address :=
  { address with chainOrHeight := BitVec.ofNat 32 i.val }

/-- Each honest WOTS signature value is the chain started from the derived secret,
advanced to the message digit. -/
theorem sign_eq_chain (message secretSeed publicSeed : Digest) (address : Address) (i : Fin chains) :
    SlhDsaSecurity.Wots.sign (m := Id) message secretSeed publicSeed address i =
      SlhDsaSecurity.Wots.chain (m := Id) publicSeed (chainAddress address i)
        0 (Checksum.encode message i).val
        (Hashing.derive (m := Id) publicSeed secretSeed
          (SlhDsaSecurity.Wots.secretAddress address i)) := by
  simp only [SlhDsaSecurity.Wots.sign, Correctness.sequenceFin_id, bind, chainAddress]

end SlhDsaSecurity.Extraction.WotsPreimage
