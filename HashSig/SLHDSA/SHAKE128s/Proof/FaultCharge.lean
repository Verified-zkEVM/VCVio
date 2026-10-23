/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.MerkleCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.WotsCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.PathEntry
public import HashSig.SLHDSA.SHAKE128s.Proof.WotsEntry
public import HashSig.SLHDSA.SHAKE128s.Proof.HypertreeDispatch
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierNaturality

/-!
# Charging a hypertree fault

`Extraction.HypertreeChain.HypertreeFault` is what an accepted forgery yields when its recovered
FORS key is not the honest one: at some layer either that layer collides, or that layer's WOTS
signature is the honest signature of a message the honest chain never signed. The first kind is
a structural event the random oracle pays for; the second is a one-wayness witness and belongs
to the input half of the budget. This file separates them, charging the first and naming the
second.

`WotsResidue` is the second kind, kept as a recursion mirroring `HypertreeFault`'s own so that
the signature at each layer is still the component the forgery supplied and the message is still
the one that layer was fed. Nothing here is existentially quantified away; a predicate that has
forgotten the forgery is satisfiable by building a signature, which is the trap the flattened
`SomeWotsWitness` fell into.

Charging the first kind is the composition the four charge files were written for. What it needs
beyond the collision itself is *the colliding query's cache entry*, which is why the theorem
takes `hcached`: every input the verifier's hypertree recovery consults is in the cache. That is
not an assumption about the adversary — `CacheReplay.cached_of_queriesUnder` supplies it for any
run whose final cache is the one being replayed, which is the situation the game bridge leaves.
Without it the charge cannot even be stated: under `CacheReplay.replayQuery` an uncached input
answers `default`, so equalities among uncached inputs are free and prove nothing.

Three things take work.

* **Locating the query.** The collision names a byte input; the charge wants it in the cache; and
  `cached_of_queriesUnder` wants to know the verifier consults it. The route down is
  `HypertreeDispatch.queriesUnder_rootFromSignature_head` to this layer, then into the layer's
  Merkle recovery — `PathEntry` for an authentication step, `CacheReplay.queriesUnder_compression`
  for the WOTS compression, and `WotsEntry.queriesUnder_chain` for a chain step, the last two
  reached by stepping over the earlier chains of a `sequenceFin`.

* **Naming the honest endpoints.** `WotsCharge.deviatingCollision_of_compressionCollision_canonical`
  states the honest side of the compression as the canonical graph's chain-top cells, while
  `Extraction.Wots.CompressionCollision` states it as the endpoints of the canonical signature.
  They agree because advancing from the signed digit to the top is advancing from the derived
  secret all the way (`Correctness.Wots.chain_add`); that is `endpoints_sign_eq_cells`.

* **Bounding the coordinates.** The charges are indexed by `CanonicalGraph.Tree`, whose layer and
  tree coordinates are `Fin layers` and `Fin (2 ^ (totalHeight - subtreeHeight))`, while
  `HypertreeFault` carries bare naturals. The induction therefore carries the two bounds. Both are
  preserved by the step and both hold at the top of the hypertree, which
  `deviatingCollision_or_residue_of_top_fault` records.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.FaultCharge

open CacheReplay Extraction CanonicalGraph

/-! ## Where a layer's queries are

A layer's verification is one `Merkle.publicKeyFromSignature`: a WOTS recovery, then a fold up
the authentication path. The three collision shapes sit at three places in it, and each needs its
own descent — into the path fold (`PathEntry.queriesUnder_pathInput`), into the compression call
that ends the WOTS recovery, and into one chain of that recovery. -/

/-- The verifier's Merkle recovery is the WOTS recovery followed by the path fold whose steps
`PathEntry` names. -/
theorem merkle_eq_wots_bind_fold (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) :
    (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) index signature
        message publicSeed address) =
      (SlhDsaSecurity.Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature.wots
        message publicSeed (SlhDsaSecurity.Merkle.wotsAddress address index.val)) >>=
        fun leaf => (List.finRange subtreeHeight).foldlM (m := OracleComp HashSpec)
          (fun value j => Hashing.shortHash
            (PathEntry.pathInput publicSeed (SlhDsaSecurity.Merkle.nodeAddress address)
              index.val (Extraction.Merkle.siblings signature) value j)) leaf := by
  refine congrArg (Bind.bind _) (funext fun leaf => ?_)
  refine congrArg (fun body => (List.finRange subtreeHeight).foldlM
    (m := OracleComp HashSpec) body leaf) (funext fun value => funext fun j => ?_)
  simp only [PathEntry.pathInput, Hashing.tweakable, BinaryPath.pairBytes, BinaryPath.ordered,
    Extraction.Merkle.siblings, dite_eq_left j.isLt, Fin.eta]
  split <;> rfl

/-- The replay implementation agrees with the replay instance, by definition. -/
theorem replay_agrees (cache : QueryCache HashSpec) (input : Bytes) :
    CacheReplay.replay cache input =
      (@query _ HashSpec Id (CacheReplay.replayQuery cache) input : Id HashOutput) := rfl

/-- **Every component of a `sequenceFin` is reached**: step over the earlier ones, descend
into this one. -/
theorem queriesUnder_sequenceFin {α : Type} (cache : QueryCache HashSpec) :
    ∀ (size : Nat) (f : Fin size → OracleComp HashSpec α) (i : Fin size) (probe : Bytes),
      QueriesUnder cache (f i) probe → QueriesUnder cache (sequenceFin size f) probe := by
  intro size
  induction size with
  | zero => intro _ i; exact Fin.elim0 i
  | succ size ih =>
    intro f i probe hquery
    induction i using Fin.cases with
    | zero => exact queriesUnder_bind cache _ _ probe hquery
    | succ j =>
      refine queriesUnder_bind_right cache (f 0) _ probe ?_
      exact queriesUnder_bind cache _ _ probe (ih (fun i => f i.succ) j probe hquery)

/-- The replayed endpoints of a WOTS recovery are the extraction's. -/
theorem simulateQ_endpoints (cache : QueryCache HashSpec) (signature : WotsSignature)
    (message publicSeed : Digest) (address : Address) :
    (simulateQ (CacheReplay.replay cache)
        (sequenceFin chains fun i =>
          SlhDsaSecurity.Wots.chain (m := OracleComp HashSpec) publicSeed
            { address with chainOrHeight := BitVec.ofNat 32 i.val }
            (Checksum.encode message i).val (w - 1 - (Checksum.encode message i).val)
            (signature i)) : Id (Fin chains → Digest)) =
      @Extraction.Wots.endpoints (CacheReplay.replayQuery cache) signature message publicSeed
        address := by
  rw [VerifierNaturality.sequenceFin_simulate (CacheReplay.replay cache)]
  rw [Correctness.sequenceFin_id]
  funext i
  exact @VerifierNaturality.chain_simulate Id Id.instMonad _ (CacheReplay.replay cache)
    (CacheReplay.replayQuery cache) (replay_agrees cache) _ _ _ _ _

/-- **The compression call of a WOTS recovery consults the extraction's endpoint bytes.** -/
theorem queriesUnder_wots_compression (cache : QueryCache HashSpec)
    (signature : WotsSignature) (message publicSeed : Digest) (address : Address) :
    QueriesUnder cache
      (SlhDsaSecurity.Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature message
        publicSeed address)
      (Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
        (digestArrayBytes (@Extraction.Wots.endpoints (CacheReplay.replayQuery cache)
          signature message publicSeed address))) := by
  rw [← simulateQ_endpoints cache signature message publicSeed address]
  exact queriesUnder_compression cache _ publicSeed _ digestArrayBytes

/-- **Every chain step of a WOTS recovery consults the chain's own partial value.** -/
theorem queriesUnder_wots_chain (cache : QueryCache HashSpec) (signature : WotsSignature)
    (message publicSeed : Digest) (address : Address) (chainIndex : Fin chains) (offset : Nat)
    (hoffset : offset < w - 1 - (Checksum.encode message chainIndex).val) :
    QueriesUnder cache
      (SlhDsaSecurity.Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature message
        publicSeed address)
      (Hashing.tweakableInput publicSeed
        { { address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } with
          hashOrIndex :=
            BitVec.ofNat 32 ((Checksum.encode message chainIndex).val + offset) }
        (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
          { address with chainOrHeight := BitVec.ofNat 32 chainIndex.val }
          (Checksum.encode message chainIndex).val offset (signature chainIndex)))) :=
  queriesUnder_bind cache _ _ _
    (queriesUnder_sequenceFin cache chains _ chainIndex _
      (WotsEntry.queriesUnder_chain cache publicSeed
        { address with chainOrHeight := BitVec.ofNat 32 chainIndex.val }
        (w - 1 - (Checksum.encode message chainIndex).val) offset
        (Checksum.encode message chainIndex).val (signature chainIndex) hoffset))

/-! ## Inside the layer

`Merkle.publicKeyFromSignature` binds the WOTS recovery to the path fold, so the WOTS sites are
reached by descending into the prefix and the path sites by stepping over it. Stepping over it
fixes the fold's leaf to the replayed WOTS public key, which is exactly the leaf
`Extraction.Hypertree.LayerCollision` states its path collision about. -/

/-- Descend into this layer's WOTS recovery. -/
theorem queriesUnder_merkle_wots (cache : QueryCache HashSpec)
    (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) (probe : Bytes)
    (hquery : QueriesUnder cache
      (SlhDsaSecurity.Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature.wots
        message publicSeed (SlhDsaSecurity.Merkle.wotsAddress address index.val)) probe) :
    QueriesUnder cache
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) index signature
        message publicSeed address) probe :=
  queriesUnder_bind cache _ _ probe hquery

/-- **Every step of this layer's authentication path consults its input**, at the running
value the extraction's `BinaryPath.value` names. -/
theorem queriesUnder_merkle_path (cache : QueryCache HashSpec)
    (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) (step : Fin subtreeHeight) :
    QueriesUnder cache
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) index signature
        message publicSeed address)
      (PathEntry.pathInput publicSeed (SlhDsaSecurity.Merkle.nodeAddress address) index.val
        (Extraction.Merkle.siblings signature)
        (BinaryPath.value
          (PathEntry.pathCombine cache publicSeed (SlhDsaSecurity.Merkle.nodeAddress address))
          index.val
          (@SlhDsaSecurity.Wots.publicKeyFromSignature Id _ (CacheReplay.replayQuery cache)
            signature.wots message publicSeed
            (SlhDsaSecurity.Merkle.wotsAddress address index.val))
          (Extraction.Merkle.siblings signature) step.val)
        step) := by
  rw [merkle_eq_wots_bind_fold]
  refine queriesUnder_bind_right cache _ _ _ ?_
  rw [show (simulateQ (CacheReplay.replay cache)
      (SlhDsaSecurity.Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature.wots
        message publicSeed (SlhDsaSecurity.Merkle.wotsAddress address index.val)) :
        Id Digest) =
      @SlhDsaSecurity.Wots.publicKeyFromSignature Id _ (CacheReplay.replayQuery cache)
        signature.wots message publicSeed
        (SlhDsaSecurity.Merkle.wotsAddress address index.val) from
    @VerifierNaturality.wots_simulate Id Id.instMonad _ (CacheReplay.replay cache)
      (CacheReplay.replayQuery cache) (replay_agrees cache) _ _ _ _]
  exact PathEntry.queriesUnder_pathInput cache publicSeed _ index.val _ _ step

/-! ## The honest endpoints are the graph's chain tops -/

/-- The extraction's endpoints of the *canonical* WOTS signature are the canonical graph's
chain-top cells: advancing from the signed digit to the top is advancing from the derived
secret all the way. -/
theorem endpoints_sign_eq_cells (cache : QueryCache HashSpec)
    (secretSeed publicSeed message : Digest) (key : WotsKey) :
    @Extraction.Wots.endpoints (CacheReplay.replayQuery cache)
        (@SlhDsaSecurity.Wots.sign Id Id.instMonad (CacheReplay.replayQuery cache) message
          secretSeed publicSeed key.address)
        message publicSeed key.address =
      fun chainIndex => @value (CacheReplay.replayQuery cache) secretSeed publicSeed
        (.structural (.wotsHash key chainIndex ⟨w - 2, by decide⟩)) := by
  funext chainIndex
  have hdigit : (Checksum.encode message chainIndex).val < w :=
    (Checksum.encode message chainIndex).isLt
  have hsplit : (Checksum.encode message chainIndex).val +
      (w - 1 - (Checksum.encode message chainIndex).val) = w - 1 := by
    simp only [w, winternitzBits] at hdigit ⊢
    omega
  have htop : @value (CacheReplay.replayQuery cache) secretSeed publicSeed
      (.structural (.wotsHash key chainIndex ⟨w - 2, by decide⟩)) =
      @SlhDsaSecurity.Wots.chain Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0 (w - 1)
        (@Hashing.derive Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed secretSeed
          (SlhDsaSecurity.Wots.secretAddress key.address chainIndex)) := by
    have h := @value_wotsPosition (CacheReplay.replayQuery cache) secretSeed publicSeed key
      chainIndex ⟨w - 1, by decide⟩
    rwa [show wotsPosition key chainIndex ⟨w - 1, by decide⟩ =
      .wotsHash key chainIndex ⟨w - 2, by decide⟩ from by
        simp only [wotsPosition, w, winternitzBits]; rfl] at h
  rw [htop]
  simp only [Extraction.Wots.endpoints]
  rw [show (@SlhDsaSecurity.Wots.sign Id Id.instMonad (CacheReplay.replayQuery cache) message
        secretSeed publicSeed key.address) chainIndex =
      @SlhDsaSecurity.Wots.chain Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0
        (Checksum.encode message chainIndex).val
        (@Hashing.derive Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed secretSeed
          (SlhDsaSecurity.Wots.secretAddress key.address chainIndex)) from by
      rw [@wots_sign_cells (CacheReplay.replayQuery cache) message secretSeed publicSeed key]
      exact @value_wotsPosition (CacheReplay.replayQuery cache) secretSeed publicSeed key
        chainIndex (Checksum.encode message chainIndex)]
  have hadd := @Correctness.Wots.chain_add (CacheReplay.replayQuery cache) publicSeed
    { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0
    (Checksum.encode message chainIndex).val
    (w - 1 - (Checksum.encode message chainIndex).val)
    (@Hashing.derive Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed secretSeed
      (SlhDsaSecurity.Wots.secretAddress key.address chainIndex))
  rw [hsplit, Nat.zero_add] at hadd
  exact hadd.symm

/-! ## A layer collision is charged -/

/-- **Each of the three shapes of a layer collision is a deviating collision.** -/
theorem deviatingCollision_of_layerCollision {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec)
    (location : Tree) (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest)
    (xsig : XmssSignature)
    (hcached : ∀ probe, QueriesUnder cache
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf xsig
        message publicSeed location.address) probe → cache probe ≠ none)
    (hcollision : @Extraction.Hypertree.LayerCollision (CacheReplay.replayQuery cache)
      secretSeed publicSeed message location.layer.val location.tree.val leaf xsig)
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  rcases hcollision with ⟨j, hj, hpath⟩ | hcompression | ⟨chainIndex, offset, hoffset, hchain⟩
  · -- A collision on the authentication path.
    obtain ⟨output, hout⟩ := Option.ne_none_iff_exists'.mp
      (hcached _ (queriesUnder_merkle_path cache leaf xsig message publicSeed location.address
        ⟨j, hj⟩))
    have hbound : leaf.val / 2 ^ (j + 1) < 2 ^ (subtreeHeight - (j + 1)) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (j + 1)), ← pow_add,
        show subtreeHeight - (j + 1) + (j + 1) = subtreeHeight from by omega]
      exact leaf.isLt
    exact MerkleCharge.deviatingCollision_of_pathBranch secretSeed publicSeed cache location
      leaf.val leaf.isLt _ (Extraction.Merkle.siblings xsig) ⟨j, hj⟩ hpath result output hcache
      hbound hout
  · -- A collision at the WOTS public-key compression.
    obtain ⟨output, hout⟩ := Option.ne_none_iff_exists'.mp
      (hcached _ (queriesUnder_merkle_wots cache leaf xsig message publicSeed location.address _
        (queriesUnder_wots_compression cache xsig.wots message publicSeed
          (SlhDsaSecurity.Merkle.wotsAddress location.address leaf.val))))
    obtain ⟨hinputs, hjoins⟩ := hcompression
    refine WotsCharge.deviatingCollision_of_compressionCollision_canonical secretSeed publicSeed
      cache ⟨location, leaf⟩ _ ?_ ?_ result output hcache hout
    · rw [← endpoints_sign_eq_cells cache secretSeed publicSeed message ⟨location, leaf⟩]
      exact hinputs
    · rw [← endpoints_sign_eq_cells cache secretSeed publicSeed message ⟨location, leaf⟩]
      exact hjoins
  · -- A collision inside one of the WOTS chains.
    have hdigit := (Checksum.encode message chainIndex).isLt
    have hposition : (Checksum.encode message chainIndex).val + offset < w - 1 := by
      simp only [w, winternitzBits] at hdigit hoffset ⊢
      omega
    obtain ⟨output, hout⟩ := Option.ne_none_iff_exists'.mp
      (hcached _ (queriesUnder_merkle_wots cache leaf xsig message publicSeed location.address _
        (queriesUnder_wots_chain cache xsig.wots message publicSeed
          (SlhDsaSecurity.Merkle.wotsAddress location.address leaf.val) chainIndex offset
          hoffset)))
    exact WotsCharge.deviatingCollision_of_chainBranch secretSeed publicSeed message cache
      ⟨location, leaf⟩ chainIndex (xsig.wots chainIndex) offset hoffset hchain result output
      hcache hposition hout

/-! ## What the collision cases leave behind -/

section Residue

variable [HasQuery HashSpec Id]

/-- The one-wayness residue of a hypertree fault: some layer's WOTS signature is the honest
signature of a message differing from the honest input threaded into that layer. The recursion
mirrors `Extraction.HypertreeChain.HypertreeFault`'s own, so the signature at each layer is
still the component the forgery supplied and the message is still the one that layer was fed.
-/
def WotsResidue (secretSeed publicSeed : Digest) :
    (remaining : Nat) → (Fin remaining → XmssSignature) → (layer tree : Nat) →
      SlhDsaSecurity.Hypertree.LeafIndex → (message expectedInput : Digest) → Prop
  | 0, _, _, _, _, _, _ => False
  | remaining + 1, signatures, layer, tree, leaf, message, expectedInput =>
    ((signatures 0).wots = SlhDsaSecurity.Wots.sign (m := Id) message secretSeed publicSeed
        (Extraction.Hypertree.wotsAddress layer tree leaf) ∧ message ≠ expectedInput) ∨
    WotsResidue secretSeed publicSeed remaining (fun i => signatures i.succ) (layer + 1)
      (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0) message
        publicSeed (SlhDsaSecurity.Hypertree.address layer tree))
      (Extraction.HypertreeChain.honestNode secretSeed publicSeed layer tree)

end Residue

/-! ## The fault, charged

The induction walks down the segment exactly as `HypertreeFault` does. At each layer the
collision case is discharged by `deviatingCollision_of_layerCollision`, reaching the layer's
own queries through `HypertreeDispatch.queriesUnder_rootFromSignature_head`; the WOTS case is
kept; and the remaining case steps over the layer, which advances the message to this layer's
replayed root — the same value `HypertreeFault` threads, by the naturality of
`Merkle.publicKeyFromSignature`.

The layer and tree indices have to be *bounded* for the collision case: the charges are
indexed by `CanonicalGraph.Tree`, whose coordinates are `Fin layers` and
`Fin (2 ^ (totalHeight - subtreeHeight))`, while `HypertreeFault` carries bare naturals. Both
bounds are preserved by the step — the layer rises by one against a fixed total, the tree
index only shrinks — and both hold at the call `HypertreeDispatch.cases_of_accepted` makes,
where the segment is all `layers` layers and the tree index comes from a `TreeIndex`. -/

/-- **A hypertree fault is a charged structural collision or a WOTS one-wayness residue.** -/
theorem deviatingCollision_or_residue_of_fault {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message expectedInput : Digest),
      layer + remaining ≤ layers → tree < 2 ^ (totalHeight - subtreeHeight) →
      (∀ probe, QueriesUnder cache
        (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
          remaining signatures layer tree leaf message) probe → cache probe ≠ none) →
      ∀ result : α × QueryCache HashSpec, result.2 = cache →
      @Extraction.HypertreeChain.HypertreeFault (CacheReplay.replayQuery cache) secretSeed
        publicSeed remaining signatures layer tree leaf message expectedInput →
      StructuralTerm.DeviatingCollision publicSeed
          (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result ∨
        @WotsResidue (CacheReplay.replayQuery cache) secretSeed publicSeed remaining signatures
          layer tree leaf message expectedInput := by
  intro remaining
  induction remaining with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ hfault
    exact hfault.elim
  | succ remaining ih =>
    intro signatures layer tree leaf message expectedInput hlayer htree hcached result hcache
      hfault
    unfold Extraction.HypertreeChain.HypertreeFault at hfault
    rcases hfault with hcollision | hwots | hrest
    · refine Or.inl (deviatingCollision_of_layerCollision secretSeed publicSeed cache
        ⟨⟨layer, by omega⟩, ⟨tree, htree⟩⟩ leaf message (signatures 0) ?_ hcollision result
        hcache)
      intro probe hprobe
      exact hcached probe (@HypertreeDispatch.queriesUnder_rootFromSignature_head
        cache publicSeed remaining signatures layer tree leaf
        message probe hprobe)
    · exact Or.inr (Or.inl hwots)
    · have hstep : ∀ probe, QueriesUnder cache
          (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
            remaining (fun i => signatures i.succ) (layer + 1) (tree / 2 ^ subtreeHeight)
            (SlhDsaSecurity.Hypertree.nextLeaf tree)
            (@SlhDsaSecurity.Merkle.publicKeyFromSignature Id Id.instMonad
              (CacheReplay.replayQuery cache) leaf (signatures 0) message publicSeed
              (SlhDsaSecurity.Hypertree.address layer tree))) probe → cache probe ≠ none := by
        intro probe hprobe
        refine hcached probe (@HypertreeDispatch.queriesUnder_rootFromSignature_tail
          cache publicSeed remaining signatures layer tree leaf
          message probe ?_)
        rwa [@VerifierNaturality.merkle_simulate Id Id.instMonad _ (CacheReplay.replay cache)
          (CacheReplay.replayQuery cache) (replay_agrees cache) leaf (signatures 0) message
          publicSeed (SlhDsaSecurity.Hypertree.address layer tree)]
      rcases ih (fun i => signatures i.succ) (layer + 1) (tree / 2 ^ subtreeHeight)
        (SlhDsaSecurity.Hypertree.nextLeaf tree) _ _ (by omega)
        (lt_of_le_of_lt (Nat.div_le_self _ _) htree) hstep result hcache hrest with hdev | hres
      · exact Or.inl hdev
      · exact Or.inr (Or.inr hres)

/-- **The fault of a whole hypertree signature is charged.** The two bounds hold at the top of
the hypertree, which is the only place `HypertreeDispatch.cases_of_accepted` produces a fault:
the segment is all `layers` layers, and the tree index is a `TreeIndex`. -/
theorem deviatingCollision_or_residue_of_top_fault {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec)
    (signature : HypertreeSignature) (tree : SlhDsaSecurity.Hypertree.TreeIndex)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message expectedInput : Digest)
    (hcached : ∀ probe, QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed layers
        signature 0 tree.toNat leaf message) probe → cache probe ≠ none)
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache)
    (hfault : @Extraction.HypertreeChain.HypertreeFault (CacheReplay.replayQuery cache)
      secretSeed publicSeed layers signature 0 tree.toNat leaf message expectedInput) :
    StructuralTerm.DeviatingCollision publicSeed
        (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result ∨
      @WotsResidue (CacheReplay.replayQuery cache) secretSeed publicSeed layers signature 0
        tree.toNat leaf message expectedInput :=
  deviatingCollision_or_residue_of_fault secretSeed publicSeed cache layers signature 0
    tree.toNat leaf message expectedInput (by omega) tree.isLt hcached result hcache hfault

end SlhDsaSecurity.FaultCharge
