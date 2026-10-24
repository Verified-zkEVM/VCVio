/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheAvailability
public import HashSig.SLHDSA.SHAKE128s.Proof.HonestMessage

/-!
# The split's branches, at the events that charge them

`SplitCharged.cases_of_win_charged` leaves a win as one of three facts about the forgery, each
stated in the vocabulary the extraction produced. None of the three is yet the event a charge is
stated against. This file moves all three.

**The structural branch** is already the structural term's event, up to which cells it is stated
at: the extraction names the cells the run's own final cache computes, and the charge names the
walk's. They are the same cells — the walk's entries survive the tail — so the move is a
rewrite.

**The WOTS branch** is the substantial one. The residue leaves the forgery holding a chain value
at a position strictly below the digit the honest key at that layer discloses, and the record of
claims already has an entry at every layer and chain. `sensitive_of_residue` identifies them:
the layer the residue stops at, the chain it names, and the position it reaches are exactly the
coordinates `ClaimedProbes.forgedSteps` computes, so the entry the record already holds is
sensitive.

Two coordinate reconciliations carry that. The first is the key: the residue's accumulators name
the layer, subtree and leaf it has reached, and `ClaimedProbes.forgedKey` is that triple read as
a `CanonicalGraph.WotsKey`. The second is the digit, and it splits on the layer. Above the
bottom, the message the honest key signs is the honest node one layer down, which is
`HonestMessage.honestRevealed_eq`. At the bottom there is no layer below, and the message is the
honest FORS public key — which is the graph's own cell at the `forsRoots` node of the FORS key
the digest selects, so the two names for it coincide definitionally.

**The FORS branch** forks, and nothing here decides which way. The forgery holds the honest
secret at each of the fourteen positions its digest selects; a position either is in the
disclosed set, which is the coverage event, or it is not, and then the secret it claims is the
graph's cell at a node the signatures leave unavailable. Both sides are already recorded — the
one as a cached message digest, the other as an entry of the record of claims.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.SplitRouted

open Security CanonicalGraph WotsResidueReduction

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

/-! ## The structural branch -/

/-- **The structural event, at the cells the charge is stated against.** The extraction names
the cells this run's final cache computes; they are the walk's own. -/
theorem deviatingCollision_at_walk_cells (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hdeviating : StructuralTerm.DeviatingCollision walk.1.1.2.2
      (@value (CacheReplay.replayQuery result.2) walk.1.1.1 walk.1.1.2.2) result) :
    StructuralTerm.DeviatingCollision walk.1.1.2.2 walk.1.2 result := by
  rwa [WarmedCharges.value_replay_eq_walk_cells adversary hwalk hresult] at hdeviating

/-! ## The bottom layer's honest message

The message the honest key at the bottom layer signs is the FORS public key the genuine secrets
produce, and that is the graph's cell at the `forsRoots` node of the FORS key the digest
selects. Both names unfold to the same tweakable hash of the same fourteen canonical roots. -/

variable [HasQuery HashSpec Id]

/-- **At the bottom layer the honest message is that cell.** -/
theorem honestMessage_zero (secretSeed publicSeed : Digest) (key : WotsKey)
    (hlayer : key.tree.layer.val = 0) :
    GraphStakes.honestMessage secretSeed publicSeed key =
      value secretSeed publicSeed (.structural (.forsRoots ⟨key.tree.tree, key.leaf⟩)) := by
  rw [GraphStakes.honestMessage, hlayer]

/-! ## The WOTS branch

The residue's accumulators name a layer, a subtree and a leaf; read as a key those are
`ClaimedProbes.forgedKey`, and the digit the forgery's message encodes there is the position
`ClaimedProbes.forgedSteps` records. So the entry the record already holds at that layer and
chain is the canonical input of a node whose staked cell no signature discloses. -/

omit [HasQuery HashSpec Id] in
/-- The coordinates of the key the residue reaches after `i` steps. -/
theorem forgedKey_coords (tree : Fin (2 ^ (totalHeight - subtreeHeight)))
    (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex) (layer : Fin layers) :
    (ClaimedProbes.forgedKey tree leaf layer).tree.layer.val = layer.val ∧
      (ClaimedProbes.forgedKey tree leaf layer).tree.tree.val = treeAt tree.val layer.val ∧
      (ClaimedProbes.forgedKey tree leaf layer).leaf = leafAt leaf tree.val layer.val :=
  ⟨rfl, rfl, rfl⟩

/-- **The digit the honest key at that layer discloses**, whichever layer the residue stopped
at: the message the residue threads for the honest side is the message the key really signs. -/
theorem honestRevealed_eq_revealedAt (secretSeed publicSeed : Digest)
    (tree : Fin (2 ^ (totalHeight - subtreeHeight)))
    (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex) (layer : Fin layers) (chain : Fin chains) :
    GraphStakes.honestRevealed secretSeed publicSeed
        (ClaimedProbes.forgedKey tree leaf layer) chain =
      (Checksum.encode (revealedAt secretSeed publicSeed
        (value secretSeed publicSeed (.structural (.forsRoots ⟨tree, leaf⟩))) 0 tree.val
        layer.val) chain).val := by
  obtain ⟨hlayer, htree, hleaf⟩ := forgedKey_coords tree leaf layer
  cases hstep : layer.val with
  | zero =>
    have hkey : (⟨(ClaimedProbes.forgedKey tree leaf layer).tree.tree,
        (ClaimedProbes.forgedKey tree leaf layer).leaf⟩ : ForsKey) = ⟨tree, leaf⟩ := by
      have hfirst : (ClaimedProbes.forgedKey tree leaf layer).tree.tree = tree :=
        Fin.val_injective (by rw [htree, hstep, treeAt])
      have hsecond : (ClaimedProbes.forgedKey tree leaf layer).leaf = leaf := by
        rw [hleaf, hstep, leafAt]
      rw [hfirst, hsecond]
    rw [GraphStakes.honestRevealed,
      honestMessage_zero secretSeed publicSeed _ (by rw [hlayer, hstep]), hkey]
    simp only [revealedAt]
  | succ j =>
    exact HonestMessage.honestRevealed_eq secretSeed publicSeed
      (value secretSeed publicSeed (.structural (.forsRoots ⟨tree, leaf⟩))) 0 tree.val leaf j
      (ClaimedProbes.forgedKey tree leaf layer)
      (by rw [hlayer, hstep, layerAt_eq]; omega) (by rw [htree, hstep])
      (by rw [hleaf, hstep]) chain

/-- **The residue names a claim the record already holds, and it is sensitive.** -/
theorem sensitive_of_residue {State : Type} (secretSeed publicSeed : Digest)
    (signedAt : State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight))) (state : State)
    (cells : Cells) (hcells : value secretSeed publicSeed = cells)
    (tree : Fin (2 ^ (totalHeight - subtreeHeight)))
    (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex) (signature : Signature) (recovered : Digest)
    (hresidue : FaultCharge.WotsResidue secretSeed publicSeed layers signature.hypertree 0
      tree.val leaf recovered
      (value secretSeed publicSeed (.structural (.forsRoots ⟨tree, leaf⟩)))) :
    ∃ (layer : Fin layers) (chain : Fin chains),
      SensitiveQuery.Sensitive (GraphStakes.stakes publicSeed)
        (GraphStakes.unavailableAt (GraphStakes.honestRevealed secretSeed publicSeed) signedAt)
        cells state
        (GraphStakes.inputOf publicSeed
          (GraphStakes.wotsHashNode (ClaimedProbes.forgedKey tree leaf layer) chain
            (ClaimedProbes.forgedSteps publicSeed signature tree.val leaf recovered layer chain))
          ((signature.hypertree layer).wots chain)) := by
  obtain ⟨layer, chain, hheld, hdigit⟩ :=
    exists_held_value_of_residue secretSeed publicSeed layers signature.hypertree 0 tree.val leaf
      recovered _ (holds_early_chain_value_of_residue secretSeed publicSeed layers
        signature.hypertree 0 tree.val leaf recovered _ hresidue)
  obtain ⟨hlayer, htree, hleaf⟩ := forgedKey_coords tree leaf layer
  refine ⟨layer, chain, ClaimedProbes.sensitive_forgedClaim publicSeed _ signedAt
    (GraphStakes.honestRevealed_le secretSeed publicSeed) cells state _ chain layers
    signature.hypertree 0 tree.val leaf recovered layer.val _ ?_ ?_⟩
  · rw [honestRevealed_eq_revealedAt secretSeed publicSeed tree leaf layer chain]
    exact hdigit
  · rw [hheld, ← hcells]
    refine (heldValue_eq_cell secretSeed publicSeed
      (ClaimedProbes.forgedKey tree leaf layer).tree
      (ClaimedProbes.forgedKey tree leaf layer).leaf _ chain).symm.trans ?_ |>.symm
    rw [hlayer, htree, hleaf, layerAt_eq, Nat.zero_add]

/-! ## The FORS branch

The third branch says the forgery holds the honest FORS secret at every position its digest
selects. Position by position there are only two possibilities, and the fork is decided by
nothing but whether the position is in the disclosed set: either it is, which is the coverage
event, or it is not, and then the secret the forgery claims is the graph's own cell at a node
the signatures leave unavailable — a sensitive candidate, and one the record of claims already
holds. -/

omit [HasQuery HashSpec Id] in
/-- **The FORS disclosure, position by position: the coverage event, or a sensitive claim.** -/
theorem signed_or_sensitive_of_secrets {State : Type} (secretSeed publicSeed : Digest)
    (revealed : WotsKey → Fin chains → Nat)
    (signedAt : State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight))) (state : State)
    (cache : QueryCache HashSpec) (cells : Cells)
    (hcells : @value (CacheReplay.replayQuery cache) secretSeed publicSeed = cells)
    (key : ForsKey) (indices : SLHDSA.SHAKE128s.Fors.Indices) (signature : ForsSignature)
    (hsecrets : ∀ tree : Fin forsTrees, (signature tree).secret =
      @SLHDSA.SHAKE128s.Fors.secret Id Id.instMonad (CacheReplay.replayQuery cache)
        secretSeed publicSeed key.address (Extraction.Fors.leafIndex indices tree))
    (tree : Fin forsTrees) :
    GraphStakes.forsIndex indices tree ∈ signedAt state key ∨
      SensitiveQuery.Sensitive (GraphStakes.stakes publicSeed)
        (GraphStakes.unavailableAt revealed signedAt) cells state
        (GraphStakes.inputOf publicSeed
          (GraphStakes.forsLeafNode key (GraphStakes.forsIndex indices tree))
          ((signature tree).secret)) := by
  classical
  obtain ⟨hcell, -⟩ := GraphStakes.forsSecret_signed_or_not_obtainable publicSeed revealed
    signedAt cache secretSeed key indices signature state hsecrets tree
  by_cases hsigned : GraphStakes.forsIndex indices tree ∈ signedAt state key
  · exact Or.inl hsigned
  · exact Or.inr (GraphStakes.sensitive_forsClaim publicSeed revealed signedAt cells state key
      (GraphStakes.forsIndex indices tree) ((signature tree).secret) hsigned
      (by rw [hcell, hcells]))

end SLHDSA.SHAKE128s.SplitRouted
