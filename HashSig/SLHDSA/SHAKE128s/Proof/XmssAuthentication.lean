/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsProgram

/-!
# Ordered XMSS authentication views

The shared intrinsic Merkle path has the paper's finite-function view in every lawful
interpretation. XMSS signing evaluates this entire path before invoking WOTS+ signing.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Merkle

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]

/-- Reading an XMSS path pointwise collects its sibling roots in increasing height order. -/
theorem authenticationPath_eq_sequenceFin (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) :
    (fun (values : Vector Digest height) (j : Fin height) => values[j]) <$>
        authenticationPath (m := m) secretSeed publicSeed address height index =
      sequenceFin height (fun j => node secretSeed publicSeed address j.val
        (Nat.xor (index / 2 ^ j.val) 1)) := by
  unfold authenticationPath
  rw [PerfectMerkleTree.intrinsicAuthPathM_eq_ofFnM]
  have view := (sequenceFin_eq_ofFnM_get
    (fun j : Fin height => node (m := m) secretSeed publicSeed address j.val
      (PerfectMerkleTree.sibling (index / 2 ^ j.val)))).symm
  simpa only [node, PerfectMerkleTree.sibling_eq_xor] using view

/-- XMSS signing collects the sibling path before the message's WOTS+ signature. -/
theorem sign_eq_sequenceFin (message secretSeed publicSeed : Digest) (address : Address)
    (index : Fin (2 ^ subtreeHeight)) :
    sign (m := m) message secretSeed publicSeed address index = (do
      let authentication ← sequenceFin subtreeHeight fun j =>
        node secretSeed publicSeed address j.val (Nat.xor (index.val / 2 ^ j.val) 1)
      let wots ← Wots.sign message secretSeed publicSeed (wotsAddress address index.val)
      return { wots, authentication } : m XmssSignature) := by
  unfold sign
  rw [← authenticationPath_eq_sequenceFin, bind_map_left]

end SLHDSA.SHAKE128s.Merkle
