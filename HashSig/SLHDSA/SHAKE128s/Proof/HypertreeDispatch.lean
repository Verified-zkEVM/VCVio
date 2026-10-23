/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.HypertreeChain
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay

/-!
# Unfolding the seven-layer fault

`Extraction.HypertreeChain.HypertreeFault` is a recursion down the hypertree: at each layer
either the layer itself collides, or that layer's WOTS signature is the honest signature of a
message differing from the honest input threaded into it, or the fault lies further up. The
recursion is how the extraction chain is proved, and it is also the form the charges consume:
the signature at each layer is the component the forgery supplied, so every charge composition
can take the colliding query's cache entry as a hypothesis.

The two cases land on different sides of the security budget, which is why they are kept
apart rather than merged. A layer collision is a structural event: a query whose answer hits
an honest cell, charged at `2 ^ -128` on the structural class. A WOTS signature for a message
the honest chain never signed is a one-wayness witness — the adversary holds chain values
below what any signature revealed — and that is a secret-side event, charged on the input
half of the budget.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.HypertreeDispatch

open Extraction.HypertreeChain

section Accepted

variable [HasQuery HashSpec Id]

/-! ## The top of the structural chain

The seven-layer soundness theorem gives the statement the charge consumes directly: an
accepted hypertree signature either carries the genuine FORS public key — in which case the
forgery has to be explained on the FORS side, which is the business of `Extraction.Fors` — or
it exhibits one of the two faults, and each of those is charged.

Nothing in this step is probabilistic. It is the whole structural reduction of SLH-DSA
verification to events a random oracle can be charged for, with no assumption of collision
resistance or one-wayness anywhere: both are *conclusions* about the adversary's queries, not
hypotheses about the hash. -/

/-- **An accepted hypertree signature is the signer's own, or faulty.** The fault-free branch
pins every layer, not just the bottom message, which is what lets a forgery with no fault in it
be compared with the signature a request returned. -/
theorem cases_of_accepted_signed (secretSeed publicSeed : Digest) (pk : PublicKey)
    (tree : SlhDsaSecurity.Hypertree.TreeIndex) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (forsKey honestForsKey : Digest) (signature : HypertreeSignature)
    (hseed : pk.seed = publicSeed)
    (hroot : pk.root = honestNode secretSeed publicSeed (layers - 1) 0)
    (haccept : SlhDsaSecurity.Hypertree.verify (m := Id) forsKey signature pk tree leaf = true) :
    (forsKey = honestForsKey ∧
        signature = SlhDsaSecurity.Hypertree.signLayers (m := Id) secretSeed publicSeed layers 0
          tree.toNat leaf honestForsKey) ∨
      HypertreeFault secretSeed publicSeed layers signature 0 tree.toNat leaf forsKey
        honestForsKey :=
  verify_fault_or_fors_signed secretSeed publicSeed pk tree leaf forsKey honestForsKey
    signature hseed hroot haccept

/-- **An accepted hypertree signature is canonical or faulty.** -/
theorem cases_of_accepted (secretSeed publicSeed : Digest) (pk : PublicKey)
    (tree : SlhDsaSecurity.Hypertree.TreeIndex) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (forsKey honestForsKey : Digest) (signature : HypertreeSignature)
    (hseed : pk.seed = publicSeed)
    (hroot : pk.root = honestNode secretSeed publicSeed (layers - 1) 0)
    (haccept : SlhDsaSecurity.Hypertree.verify (m := Id) forsKey signature pk tree leaf = true) :
    forsKey = honestForsKey ∨
      HypertreeFault secretSeed publicSeed layers signature 0 tree.toNat leaf forsKey
        honestForsKey :=
  verify_fault_or_fors_canonical secretSeed publicSeed pk tree leaf forsKey honestForsKey
    signature hseed hroot haccept

end Accepted

/-! ## Walking down the layers

`Hypertree.rootFromSignature` is a recursion, one `Merkle.publicKeyFromSignature` per layer,
each fed the root the layer below produced. A collision sits at one particular layer, so
reaching its query means walking down to that layer — and the two directions of
`CacheReplay.queriesUnder_bind` and `queriesUnder_bind_right` are exactly the two steps of
that walk: descend into this layer, or step over it to the next.

Stepping over a layer advances the message to that layer's replayed root, which is what
`CacheReplay.run_eq_replay` identifies with the root the oracle run actually produced. -/

open CacheReplay in
/-- Descend into this layer. -/
theorem queriesUnder_rootFromSignature_head (cache : QueryCache HashSpec) (publicSeed : Digest)
    (remaining : Nat) (signatures : Fin (remaining + 1) → XmssSignature) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (probe : Bytes)
    (hquery : QueriesUnder cache
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf
        (signatures 0) message publicSeed (SlhDsaSecurity.Hypertree.address layer tree)) probe) :
    QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
        (remaining + 1) signatures layer tree leaf message) probe :=
  queriesUnder_bind cache _ _ probe hquery

open CacheReplay in
/-- Step over this layer to the next, advancing the message to this layer's replayed root. -/
theorem queriesUnder_rootFromSignature_tail (cache : QueryCache HashSpec) (publicSeed : Digest)
    (remaining : Nat) (signatures : Fin (remaining + 1) → XmssSignature) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (probe : Bytes)
    (hquery : QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
        remaining (fun i => signatures i.succ) (layer + 1)
        (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
        (simulateQ (replay cache)
          (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf
            (signatures 0) message publicSeed
            (SlhDsaSecurity.Hypertree.address layer tree)))) probe) :
    QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
        (remaining + 1) signatures layer tree leaf message) probe :=
  queriesUnder_bind_right cache _ _ probe hquery

end SlhDsaSecurity.HypertreeDispatch
