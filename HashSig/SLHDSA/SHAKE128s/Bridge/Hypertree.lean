/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.Xmss
public import HashSig.SLHDSA.SHAKE128s.Bridge.Fors

/-!
# The paper's hypertree programs are FIPS 205's, query for query

Continuing `HashSig.SLHDSA.SHAKE128s.Bridge.Xmss`: each hypertree program of the paper model, with
its answers relabelled by `answerEquiv`, is the corresponding FIPS 205 program over the typed
interface mapped through `encImpl FIPS205.params`, with its output read back (`digestEquiv.symm`
for a node, `xmssFamily` for the layer signatures). Seeds are paper digests, other nodes and
signatures FIPS 205 values; secrets come from the oracle-secret provider of
`SLHDSA.Security.romScheme`.

Both signers walk the layers upward along the same positions: the paper's layer, tree and
`Hypertree.nextLeaf` are FIPS 205's `LayerPosition.next`. At `d = 7` the FIPS 205 signer is entered
with `recoverFinal = (d == 1) = false`, so neither recovers the root of the top layer's signature.

## Main statements

* `simulateQ_relabel_signLayers`, `simulateQ_relabel_hypertreeSign`: the paper's
  `Hypertree.signLayers` is `signFromPositionWithSecret` with `recoverFinal = false`, and
  `Hypertree.sign` at the digest split of an `H_msg` answer is `signWithSecretM`.
* `simulateQ_relabel_rootFromSignature`, `simulateQ_relabel_hypertreeVerify`: the paper's
  `Hypertree.rootFromSignature` is `recoverFromPositionWith`, and `Hypertree.verify` at the digest
  split is `GeneralHypertree.verifyM`.
* `simulateQ_relabel_keygenRoot`: the root key generation publishes, `Merkle.node` of the top XMSS
  tree, is `rootWithSecretM`.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Bridge

open SLHDSA SLHDSA.Security GeneralHypertree

/-- Programs of the paper model. -/
local notation "PaperComp" => OracleComp OracleWorld
/-- Programs of FIPS 205 over the typed interface. -/
local notation "TypedComp" => OracleComp (unifSpec + hashSpec FIPS205.core)
/-- Run a paper program in the FIPS 205 single-oracle world. -/
local notation "𝓡" => simulateQ (relabel answerEquiv)
/-- Run a program of the typed interface in the FIPS 205 single-oracle world. -/
local notation "𝓔" => simulateQ (encImpl FIPS205.params)

/-! ## Layer signatures -/

/-- The paper's family of XMSS signatures of a FIPS 205 vector of them, layer by layer. -/
@[expose] def xmssFamily {k : ℕ} (v : Vector (XmssSig FIPS205.params.params FIPS205.core) k) :
    Fin k → XmssSignature :=
  fun i => xmssOfCore (v[i.val]'i.isLt)

/-- Prepending a signature to the vector prepends its reading to the family. -/
theorem xmssFamily_insertIdx {k : ℕ} (v : Vector (XmssSig FIPS205.params.params FIPS205.core) k)
    (s : XmssSig FIPS205.params.params FIPS205.core) :
    xmssFamily (v.insertIdx 0 s) = Fin.cases (xmssOfCore s) (xmssFamily v) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [xmssFamily, Vector.insertIdx_zero]
  | succ i => simp [xmssFamily, Vector.insertIdx_zero, Vector.getElem_append_right]

/-- The first signature of the family is the reading of the vector's head. -/
theorem xmssFamily_zero {k : ℕ} (v : Vector (XmssSig FIPS205.params.params FIPS205.core) (k + 1)) :
    xmssFamily v 0 = xmssOfCore v.head := by
  simp [xmssFamily, Vector.head]

/-- The family after its first signature is the family of the vector's tail. -/
theorem xmssFamily_succ {k : ℕ} (v : Vector (XmssSig FIPS205.params.params FIPS205.core) (k + 1)) :
    (fun i : Fin k => xmssFamily v i.succ) = xmssFamily v.tail := by
  funext i
  simp only [xmssFamily, Vector.tail, Fin.val_succ, Vector.getElem_extract, Vector.getElem_cast]
  congr 2
  omega

/-! ## Signing -/

/-- **Hypertree signing from a position** (Algorithm 12): the paper's `Hypertree.signLayers` over
the remaining `layers` layers from the layer, tree and leaf of `pos` is FIPS 205's
`signFromPositionWithSecret` with the public-hash callbacks, the oracle-secret provider and no
recovery of the top layer's root. Each layer signs, then recovers the root signed at the next
layer. -/
theorem simulateQ_relabel_signLayers (secretSeed publicSeed : Digest) :
    ∀ (layers : ℕ) (pos : LayerPosition FIPS205.params)
      (h : pos.layer.val + layers = FIPS205.params.params.d) (msg : FIPS205.core.Y),
    𝓡 (Hypertree.signLayers secretSeed publicSeed layers pos.layer.val pos.tree.val
        ⟨pos.leaf.val, pos.leaf.isLt⟩ (digestEquiv.symm msg) :
          PaperComp (Fin layers → XmssSignature)) =
      xmssFamily <$> 𝓔 (signFromPositionWithSecret FIPS205.core
        (PublicHash.f FIPS205.core (digestEquiv publicSeed))
        (PublicHash.tl FIPS205.core (digestEquiv publicSeed))
        (PublicHash.h FIPS205.core (digestEquiv publicSeed))
        (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
          (digestEquiv secretSeed)) false pos layers h msg : TypedComp _)
  | 0, pos, h, _ => by
    have := pos.layer.isLt
    omega
  | 1, pos, _, msg => by
    rw [Hypertree.signLayers, signFromPositionWithSecret]
    simp only [Bool.false_eq_true, ite_false]
    rw [LayerPosition.toAdrs_eq pos]
    refine ForsBridge.bind_bridge
      (simulateQ_relabel_merkleSign msg secretSeed publicSeed _ ⟨pos.leaf.val, pos.leaf.isLt⟩)
      fun sig => ?_
    exact ForsBridge.pure_bridge _ _ _ (by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0)
  | k + 2, pos, h, msg => by
    rw [Hypertree.signLayers, signFromPositionWithSecret]
    simp only []
    rw [LayerPosition.toAdrs_eq pos]
    refine ForsBridge.bind_bridge
      (simulateQ_relabel_merkleSign msg secretSeed publicSeed _ ⟨pos.leaf.val, pos.leaf.isLt⟩)
      fun sig => ?_
    refine ForsBridge.bind_bridge
      (simulateQ_relabel_merklePublicKeyFromSignature ⟨pos.leaf.val, pos.leaf.isLt⟩ sig msg
        publicSeed _) fun root => ?_
    refine ForsBridge.bind_bridge
      (simulateQ_relabel_signLayers secretSeed publicSeed (k + 1) (pos.next (by omega))
        (by simp only [LayerPosition.next_layer_val]; omega) root) fun rest => ?_
    exact ForsBridge.pure_bridge _ _ _ (xmssFamily_insertIdx rest sig)

/-- The paper's leaf index of an answer, as FIPS 205's layer-zero position reads it. -/
theorem leafIndex_toFin_eq (h : HashOutput) :
    (MessageDigest.leafIndex h).toFin =
      ⟨(LayerPosition.initial FIPS205.params (parts h)).leaf.val,
        (LayerPosition.initial FIPS205.params (parts h)).leaf.isLt⟩ :=
  Fin.ext (by rw [initial_leaf_val_parts, BitVec.val_toFin])

/-- **Hypertree signing** (Algorithm 12): the paper's `Hypertree.sign` at the tree and leaf
indices of an `H_msg` answer `h` is FIPS 205's `signWithSecretM` at the digest split of `h`, with
the oracle-secret provider. -/
theorem simulateQ_relabel_hypertreeSign (h : HashOutput) (msg : FIPS205.core.Y)
    (secretSeed publicSeed : Digest) :
    𝓡 (Hypertree.sign (digestEquiv.symm msg) secretSeed publicSeed (MessageDigest.treeIndex h)
        (MessageDigest.leafIndex h).toFin : PaperComp HypertreeSignature) =
      xmssFamily <$> 𝓔 (signWithSecretM FIPS205.core
        (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
          (digestEquiv secretSeed)) msg (digestEquiv publicSeed) (parts h) : TypedComp _) := by
  rw [Hypertree.sign, leafIndex_toFin_eq, ← initial_tree_val_parts h]
  have key := simulateQ_relabel_signLayers secretSeed publicSeed layers
    (LayerPosition.initial FIPS205.params (parts h)) rfl msg
  unfold signWithSecretM signWithSecret
  simp only [show (FIPS205.params.params.d == 1) = false from rfl]
  exact key

/-! ## Verification -/

/-- **Hypertree root recovery from a position** (Algorithm 13): the paper's
`Hypertree.rootFromSignature` over the remaining `layers` layers from the layer, tree and leaf of
`pos` is FIPS 205's `recoverFromPositionWith` with the public-hash callbacks. -/
theorem simulateQ_relabel_rootFromSignature (publicSeed : Digest) :
    ∀ (layers : ℕ) (pos : LayerPosition FIPS205.params)
      (h : pos.layer.val + layers = FIPS205.params.params.d) (msg : FIPS205.core.Y)
      (sigs : Vector (XmssSig FIPS205.params.params FIPS205.core) layers),
    𝓡 (Hypertree.rootFromSignature publicSeed layers (xmssFamily sigs) pos.layer.val pos.tree.val
        ⟨pos.leaf.val, pos.leaf.isLt⟩ (digestEquiv.symm msg) : PaperComp Digest) =
      digestEquiv.symm <$> 𝓔 (recoverFromPositionWith FIPS205.params FIPS205.core
        (PublicHash.f FIPS205.core (digestEquiv publicSeed))
        (PublicHash.tl FIPS205.core (digestEquiv publicSeed))
        (PublicHash.h FIPS205.core (digestEquiv publicSeed))
        (digestEquiv publicSeed) pos layers h msg sigs : TypedComp _)
  | 0, pos, h, _, _ => by
    have := pos.layer.isLt
    omega
  | 1, pos, _, msg, sigs => by
    rw [Hypertree.rootFromSignature]
    simp only [Hypertree.rootFromSignature, bind_pure, recoverFromPositionWith]
    rw [LayerPosition.toAdrs_eq pos, xmssFamily_zero]
    exact simulateQ_relabel_merklePublicKeyFromSignature ⟨pos.leaf.val, pos.leaf.isLt⟩
      sigs.head msg publicSeed _
  | k + 2, pos, h, msg, sigs => by
    rw [Hypertree.rootFromSignature]
    simp only [recoverFromPositionWith]
    rw [LayerPosition.toAdrs_eq pos, xmssFamily_zero]
    refine ForsBridge.bind_bridge
      (simulateQ_relabel_merklePublicKeyFromSignature ⟨pos.leaf.val, pos.leaf.isLt⟩ sigs.head msg
        publicSeed _) fun root => ?_
    rw [xmssFamily_succ]
    exact simulateQ_relabel_rootFromSignature publicSeed (k + 1) (pos.next (by omega))
      (by simp only [LayerPosition.next_layer_val]; omega) root sigs.tail

/-- **Hypertree root recovery** at the tree and leaf indices of an `H_msg` answer `h` is FIPS
205's `pkFromSigM` at the digest split of `h`. -/
theorem simulateQ_relabel_hypertreeRoot (h : HashOutput) (msg : FIPS205.core.Y)
    (sigs : HtSigCore FIPS205.params.params FIPS205.core) (publicSeed : Digest) :
    𝓡 (Hypertree.rootFromSignature publicSeed layers (xmssFamily sigs) 0
        (MessageDigest.treeIndex h).toNat (MessageDigest.leafIndex h).toFin
        (digestEquiv.symm msg) : PaperComp Digest) =
      digestEquiv.symm <$> 𝓔 (pkFromSigM FIPS205.params FIPS205.core msg sigs
        (digestEquiv publicSeed) (parts h) : TypedComp _) := by
  rw [leafIndex_toFin_eq, ← initial_tree_val_parts h]
  exact simulateQ_relabel_rootFromSignature publicSeed FIPS205.params.params.d _ rfl msg sigs

/-- **Hypertree verification** (Algorithm 13): the paper's `Hypertree.verify` at the tree and
leaf indices of an `H_msg` answer `h` is FIPS 205's `verifyM` at the digest split of `h`, against
the public key's root. -/
theorem simulateQ_relabel_hypertreeVerify (h : HashOutput) (msg : FIPS205.core.Y)
    (sigs : HtSigCore FIPS205.params.params FIPS205.core) (pk : PublicKey) :
    𝓡 (Hypertree.verify (digestEquiv.symm msg) (xmssFamily sigs) pk (MessageDigest.treeIndex h)
        (MessageDigest.leafIndex h).toFin : PaperComp Bool) =
      𝓔 (verifyM FIPS205.params FIPS205.core msg sigs (digestEquiv pk.seed) (parts h)
        (digestEquiv pk.root) : TypedComp Bool) := by
  rw [Hypertree.verify, simulateQ_bind, simulateQ_relabel_hypertreeRoot, bind_map_left]
  simp only [verifyM, simulateQ_bind, simulateQ_pure]
  refine bind_congr fun root => ?_
  have hb : (digestEquiv.symm root == pk.root) = decide (root = digestEquiv pk.root) :=
    Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, decide_eq_true_iff, Equiv.symm_apply_eq])
  rw [hb]

/-! ## Key generation -/

/-- **The public root** (Algorithm 18): the root key generation publishes, the paper's
`Merkle.node` of the top layer's tree `0`, is FIPS 205's `rootWithSecretM` with the oracle-secret
provider. -/
theorem simulateQ_relabel_keygenRoot (secretSeed publicSeed : Digest) :
    𝓡 (Merkle.node secretSeed publicSeed (Hypertree.address (layers - 1) 0) subtreeHeight 0 :
        PaperComp Digest) =
      digestEquiv.symm <$> 𝓔 (rootWithSecretM FIPS205.core
        (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
          (digestEquiv secretSeed)) (digestEquiv publicSeed) : TypedComp _) := by
  rw [simulateQ_relabel_merkleRoot, toAdrs_address_top]
  rfl

end SlhDsaSecurity.Bridge
