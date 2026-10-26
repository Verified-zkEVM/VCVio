/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareGame
public import HashSig.SLHDSA.SHAKE128s.Proof.RedrawCell

/-!
# The assembled signature reads only the released cells

`ShareSigner.cellSig` replays the walk's warm cache; this file says that the signature it
assembles is a function of the cells available once its digest is served, at the digits the
table's own signed cells reveal (`cellSig_congr`). Two tables that agree there assemble the same
signature, whatever their other cells — the secret seed included.

The climb is `signLayers_congr_cells`, with availability read at `ShareCells.revealedOf`: the
climb visits only keys of the hypertree, where the digit `revealedOf` reads is the one the
climb's own message encodes, so the induction goes through with the invariant stated against the
table's cells.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.ShareSignCongr

open CanonicalGraph RedrawCell ShareGame

/-- **The walk's warm cache is the table's union cache over nothing.** -/
theorem warm_eq_unionCache (setup : Setup) :
    setup.warm = unionCache setup.publicSeed setup.table ∅ := by
  ext input
  rw [unionCache, QueryCache.ofFn_apply, openCache_total]
  cases h : Programming.cacheFrom setup.publicSeed setup.table.1
    (fullOutput setup.table.1 setup.table.2) Programming.order ∅ input with
  | none => rw [Setup.warm, h]; rfl
  | some answer => rw [Setup.warm, h]

/-- The digit a key one layer up reveals is the one the root of the subtree below encodes. -/
theorem revealedOf_succ (cells : Cells) (layer : Nat) (hl : layer < layers)
    (hnext : layer + 1 < layers) (tree : Nat)
    (htree : tree < 2 ^ (totalHeight - subtreeHeight))
    (hdiv : tree / 2 ^ subtreeHeight < 2 ^ (totalHeight - subtreeHeight)) (chain : Fin chains) :
    ShareCells.revealedOf cells
        ⟨⟨⟨layer + 1, hnext⟩, ⟨tree / 2 ^ subtreeHeight, hdiv⟩⟩, Hypertree.nextLeaf tree⟩ chain =
      (Checksum.encode
        (cells (.structural (HonestProbes.subtreeRootNode ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩)))
        chain).val := by
  have hsum : (tree / 2 ^ subtreeHeight) * 2 ^ subtreeHeight + tree % 2 ^ subtreeHeight = tree := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod tree (2 ^ subtreeHeight)
  have hrange : (tree / 2 ^ subtreeHeight) * 2 ^ subtreeHeight +
      (Hypertree.nextLeaf tree).val < 2 ^ (totalHeight - subtreeHeight) := by
    change (tree / 2 ^ subtreeHeight) * 2 ^ subtreeHeight + tree % 2 ^ subtreeHeight < _
    rw [hsum]
    exact htree
  have hfin : (⟨(tree / 2 ^ subtreeHeight) * 2 ^ subtreeHeight + (Hypertree.nextLeaf tree).val,
      hrange⟩ : Fin (2 ^ (totalHeight - subtreeHeight))) = ⟨tree, htree⟩ :=
    Fin.ext (by simpa [Hypertree.nextLeaf] using hsum)
  unfold ShareCells.revealedOf ShareCells.messageNode
  simp only [dite_eq_left hl, dite_eq_left hrange, hfin]

/-- The digit a bottom-layer key reveals is the one its FORS public key encodes. -/
theorem revealedOf_zero (cells : Cells) (hl : 0 < layers) (tree : Nat)
    (htree : tree < 2 ^ (totalHeight - subtreeHeight)) (leaf : Hypertree.LeafIndex)
    (chain : Fin chains) :
    ShareCells.revealedOf cells ⟨⟨⟨0, hl⟩, ⟨tree, htree⟩⟩, leaf⟩ chain =
      (Checksum.encode (cells (.structural (.forsRoots ⟨⟨tree, htree⟩, leaf⟩))) chain).val := rfl

/-- **The climb reads only cells the signatures have released**, at the table's digits. -/
theorem signLayers_congr_cells (publicSeed : Digest) (cache : QueryCache HashSpec)
    (left right : Cells × Padding)
    (signed : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (hagree : ∀ node, Available (ShareCells.revealedOf left.1) signed node →
        left.1 node = right.1 node) :
    ∀ (remaining layer tree : Nat) (leaf : Hypertree.LeafIndex)
      (htree : tree < 2 ^ (totalHeight - subtreeHeight)) (message : Digest),
      layer + remaining ≤ layers →
      (∀ (hl : layer < layers) (chain : Fin chains),
        ShareCells.revealedOf left.1 ⟨⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩, leaf⟩ chain =
          (Checksum.encode message chain).val) →
      @Hypertree.signLayers Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache))
          (left.1 Node.secretSeed) publicSeed remaining layer tree leaf message =
        @Hypertree.signLayers Id _ (CacheReplay.replayQuery (unionCache publicSeed right cache))
          (right.1 Node.secretSeed) publicSeed remaining layer tree leaf message := by
  have hrevealed := ShareCells.revealedOf_le left.1
  intro remaining
  induction remaining with
  | zero => intro layer tree leaf htree message _ _; rfl
  | succ remaining ih =>
    intro layer tree leaf htree message hbound hmessage
    have hl : layer < layers := by omega
    have hdiv : tree / 2 ^ subtreeHeight < 2 ^ (totalHeight - subtreeHeight) :=
      lt_of_le_of_lt (Nat.div_le_self _ _) htree
    have hhead : @Merkle.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache))
          message (left.1 Node.secretSeed) publicSeed (Hypertree.address layer tree) leaf =
        @Merkle.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed right cache))
          message (right.1 Node.secretSeed) publicSeed (Hypertree.address layer tree) leaf := by
      change @Merkle.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache))
          message (left.1 Node.secretSeed) publicSeed
          (⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩ : Tree).address leaf =
        @Merkle.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed right cache))
          message (right.1 Node.secretSeed) publicSeed
          (⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩ : Tree).address leaf
      refine xmssSignature_eq (funext fun chain => ?_) (funext fun level => ?_)
      · rw [HonestProbes.merkle_sign_wots_cell (tree := ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩),
          HonestProbes.merkle_sign_wots_cell (tree := ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩),
          replayCells_unionCache, replayCells_unionCache]
        exact hagree _ (GraphStakes.available_wotsPosition _ signed _ chain _
          (hmessage hl chain).symm)
      · rw [HonestProbes.merkle_sign_authentication_cell (tree := ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩),
          HonestProbes.merkle_sign_authentication_cell (tree := ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩),
          replayCells_unionCache, replayCells_unionCache]
        exact hagree _ (available_of_alwaysAvailable _ signed hrevealed
          (alwaysAvailable_merkleNode _ _ _ _))
    have hrootLeft : @Merkle.node Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache))
          (left.1 Node.secretSeed) publicSeed (Hypertree.address layer tree) subtreeHeight 0 =
        left.1 (.structural (HonestProbes.subtreeRootNode ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩)) := by
      change @Merkle.node Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache))
          (left.1 Node.secretSeed) publicSeed
          (⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩ : Tree).address subtreeHeight 0 = _
      rw [HonestProbes.subtree_root_cell _ _ _ ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩,
        replayCells_unionCache]
    have hroot : @Merkle.node Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache))
          (left.1 Node.secretSeed) publicSeed (Hypertree.address layer tree) subtreeHeight 0 =
        @Merkle.node Id _ (CacheReplay.replayQuery (unionCache publicSeed right cache))
          (right.1 Node.secretSeed) publicSeed (Hypertree.address layer tree) subtreeHeight 0 := by
      rw [hrootLeft]
      change _ = @Merkle.node Id _ (CacheReplay.replayQuery (unionCache publicSeed right cache))
          (right.1 Node.secretSeed) publicSeed
          (⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩ : Tree).address subtreeHeight 0
      rw [HonestProbes.subtree_root_cell _ _ _ ⟨⟨layer, hl⟩, ⟨tree, htree⟩⟩,
        replayCells_unionCache]
      exact hagree _ (available_of_alwaysAvailable _ signed hrevealed
        (alwaysAvailable_merkleNode _ _ _ _))
    funext index
    refine Fin.cases ?_ (fun below => ?_) index
    · rw [HonestProbes.signLayers_head, HonestProbes.signLayers_head]
      exact hhead
    · rw [HonestProbes.signLayers_tail, HonestProbes.signLayers_tail, ← hroot]
      refine congrFun (ih (layer + 1) (tree / 2 ^ subtreeHeight) (Hypertree.nextLeaf tree) hdiv _
        (by omega) fun hnext chain => ?_) below
      rw [revealedOf_succ left.1 layer hl hnext tree htree hdiv chain, hrootLeft]

/-- **The assembled signature reads only the released cells.** Two setups at one public seed
whose tables agree on every cell available at `signed` — which must release the FORS secrets
this digest selects — assemble the same signature, whatever their secret seeds and `SK.prf`. -/
theorem cellSig_congr (publicSeed prfLeft prfRight : Digest) (left right : Cells × Padding)
    (signed : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (hagree : ∀ node, Available (ShareCells.revealedOf left.1) signed node →
        left.1 node = right.1 node)
    (randomizer : Digest) (digest : HashOutput)
    (hsigned : ∀ tree : Fin forsTrees,
      HonestProbes.forsSecretIndex (MessageDigest.forsIndices digest) tree ∈
        signed (SplitCharged.forsKeyOfDigest digest)) :
    ShareSigner.cellSig (Setup.warm ⟨prfLeft, publicSeed, left⟩)
        (Setup.sk ⟨prfLeft, publicSeed, left⟩) randomizer digest =
      ShareSigner.cellSig (Setup.warm ⟨prfRight, publicSeed, right⟩)
        (Setup.sk ⟨prfRight, publicSeed, right⟩) randomizer digest := by
  have hrevealed := ShareCells.revealedOf_le left.1
  have hdisclose : ∀ node,
      ForsDiscloses (SplitCharged.forsKeyOfDigest digest) (MessageDigest.forsIndices digest)
          node → left.1 node = right.1 node := by
    rintro node (⟨tree, rfl⟩ | ⟨tree, level, rfl⟩)
    · exact hagree _ (hsigned tree)
    · exact hagree _ (available_of_alwaysAvailable _ signed hrevealed trivial)
  have hroots : left.1 (.structural (.forsRoots (SplitCharged.forsKeyOfDigest digest))) =
      right.1 (.structural (.forsRoots (SplitCharged.forsKeyOfDigest digest))) :=
    hagree _ (available_of_alwaysAvailable _ signed hrevealed trivial)
  have hforsKey : ∀ table : Cells × Padding,
      @Fors.publicKeyFromSignature Id _
          (CacheReplay.replayQuery (unionCache publicSeed table ∅))
          (@Fors.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed table ∅))
            (MessageDigest.forsIndices digest) (table.1 Node.secretSeed) publicSeed
            (SplitCharged.forsKeyOfDigest digest).address)
          (MessageDigest.forsIndices digest) publicSeed
          (SplitCharged.forsKeyOfDigest digest).address =
        table.1 (.structural (.forsRoots (SplitCharged.forsKeyOfDigest digest))) := by
    intro table
    rw [@CanonicalGraph.fors_publicKey_cell
      (CacheReplay.replayQuery (unionCache publicSeed table ∅)) (MessageDigest.forsIndices digest)
      (table.1 Node.secretSeed) publicSeed (SplitCharged.forsKeyOfDigest digest),
      value_unionCache]
  unfold ShareSigner.cellSig ShareSigner.signAfter
  rw [warm_eq_unionCache, warm_eq_unionCache]
  simp only [Setup.sk, Setup.secretSeed, Setup.pk]
  simp only [bind, pure]
  simp only [← SplitCharged.forsKeyOfDigest_address]
  refine signature_mk_eq rfl ?_ ?_
  · exact fors_sign_congr publicSeed ∅ left right (SplitCharged.forsKeyOfDigest digest)
      (MessageDigest.forsIndices digest) hdisclose
  · change @Hypertree.signLayers Id _ (CacheReplay.replayQuery (unionCache publicSeed left ∅))
        (left.1 Node.secretSeed) publicSeed layers 0 (MessageDigest.treeIndex digest).toNat
        (MessageDigest.leafIndex digest).toFin _ =
      @Hypertree.signLayers Id _ (CacheReplay.replayQuery (unionCache publicSeed right ∅))
        (right.1 Node.secretSeed) publicSeed layers 0 (MessageDigest.treeIndex digest).toNat
        (MessageDigest.leafIndex digest).toFin _
    rw [hforsKey left, hforsKey right, ← hroots]
    refine signLayers_congr_cells publicSeed ∅ left right signed hagree layers 0 _ _
      (MessageDigest.treeIndex digest).isLt _ (by omega) fun hl chain => ?_
    rw [revealedOf_zero]
    rfl

end SLHDSA.SHAKE128s.ShareSignCongr
