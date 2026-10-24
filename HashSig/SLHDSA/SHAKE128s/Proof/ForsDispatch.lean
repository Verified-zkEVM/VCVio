/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsLeafCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.MerkleCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.PathEntry

/-!
# The FORS side of the forgery decomposition, dispatched

`Extraction.Fors.publicKey_canonical_decomposition` says a FORS signature reproducing the
genuine FORS public key either collides at the root compression, or, for every one of the
fourteen trees, collides on that tree's authentication path or reproduces the canonical
secret leaf. `Extraction.Fors.recoveredLeaf_canonical_secret_or_collision` then splits the
second branch again: the revealed secret is the honest one, or there is a collision at the
leaf's own compression call.

`ForsCollision` below bundles the three collision shapes, `forsCollision_or_canonical_secrets`
produces it from the decomposition, and `deviatingCollision_of_forsCollision` charges it: each
shape is handed to the composition already proved for it.

* the root compression goes to `ForsCharge.deviatingCollision_of_compressionCollision_canonical`;
* a leaf goes to `ForsLeafCharge.deviatingCollision_of_leafCollision_canonical`;
* a tree path is charged here. `MerkleCharge` proves the Merkle counterpart but is not generic in
  the node shape, so `deviatingCollision_of_pathCollision`
  and `deviatingCollision_of_pathCollision_canonical` here follow it line for line with
  `Fors.nodeAddress` in place of `Merkle.nodeAddress` and the `forsTree` nodes in place of the
  `tree` nodes. Only the two arithmetic facts about `BinaryPath.canonicalPair` are shared
  verbatim — those are already generic in `nodes`.

The index bookkeeping (which canonical-graph node a given FORS index names) is carried in
hypotheses, together with the cache entries, which `CacheReplay` and `PathEntry` supply from the
verifier's own run.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ForsDispatch

open CanonicalGraph Extraction

/-! ## A two-child node, charged

`CollisionToDeviating.deviatingCollision_of_tree_pair` is the pair-shaped join, but it names
the Merkle `tree` node and its `merkleChild`ren explicitly. The FORS trees have the same shape
at a different constructor, so the join is restated here over an arbitrary parent with an
arbitrary pair of children; the proof is `CollisionToDeviating`'s own, with the two generic
ingredients it already exports. -/

/-- **A collision at a two-child node is a charged structural event.** -/
theorem deviatingCollision_of_pair {α : Type} (publicSeed : Digest) (cells : Cells)
    (parent : StructuralNode) (left right : Node) (actualLeft actualRight : Digest)
    (hchildren : parent.children = [left, right])
    (hdistinct : left ≠ right)
    (hne : (actualLeft, actualRight) ≠ (cells left, cells right))
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hentry : result.2 (Hashing.tweakableInput publicSeed parent.address
        (BinaryPath.pairBytes (actualLeft, actualRight))) = some output)
    (hvalue : Hashing.truncate output = cells (.structural parent)) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨candidates, hleft, hright, hdeviates⟩ :=
    CollisionToDeviating.exists_deviating_child cells left right actualLeft actualRight
      hne hdistinct
  refine ⟨candidates, parent, output, ?_, ?_, hvalue⟩
  · obtain ⟨child, hmember, hdiffers⟩ := hdeviates
    exact ⟨child, by rw [hchildren]; exact hmember, hdiffers⟩
  · rw [canonicalInput, hchildren, CollisionToDeviating.childBytes_pair, hleft, hright]
    exact hentry

/-! ## A FORS tree-path collision, charged

The FORS counterpart of `MerkleCharge.deviatingCollision_of_pathCollision`, with the same three
facts meeting: `BinaryPath.canonical_step` makes the collision's shared value the honest node
above the path position, `CacheReplay.tweakable_replayQuery` makes it a cache entry's
truncation, and the pair join turns a differing child pair into the charged event. -/

/-- **A FORS path collision is a charged structural event.** -/
theorem deviatingCollision_of_pathCollision {α : Type} (publicSeed : Digest) (cells : Cells)
    (cache : QueryCache HashSpec) (address : Address) (nodes : Nat → Nat → Digest)
    (index height : Nat) (leaf : Digest) (siblings : Nat → Digest)
    (parent : StructuralNode) (left right : Node)
    -- the combination rule the extraction uses, answered from this cache
    (combine : Nat → Nat → Digest → Digest → Digest)
    (hcombine : ∀ h i l r, combine h i l r =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
        (SlhDsaSecurity.Fors.nodeAddress address h i) (BinaryPath.pairBytes (l, r)))
    (hnodes : ∀ h i, nodes (h + 1) i =
      combine (h + 1) i (nodes h (2 * i)) (nodes h (2 * i + 1)))
    -- how this path position sits in the canonical graph
    (haddress : parent.address =
      SlhDsaSecurity.Fors.nodeAddress address (height + 1) (index / 2 ^ (height + 1)))
    (hchildren : parent.children = [left, right])
    (hdistinct : left ≠ right)
    (hparentCell : cells (.structural parent) = nodes (height + 1) (index / 2 ^ (height + 1)))
    (hleftCell : cells left = (BinaryPath.canonicalPair nodes index height).1)
    (hrightCell : cells right = (BinaryPath.canonicalPair nodes index height).2)
    -- the collision, and the cache entry its own query left behind
    (hcollision : BinaryPath.Collision nodes combine index leaf siblings height)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
        (BinaryPath.pairBytes
          (BinaryPath.ordered index height
            (BinaryPath.value combine index leaf siblings height) (siblings height)))) =
      some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hdiffers, hjoins⟩ := hcollision
  set actual := BinaryPath.ordered index height
    (BinaryPath.value combine index leaf siblings height) (siblings height) with hactualDef
  -- The canonical pair recombines to the honest node, so the shared value is that node.
  have hcanonical := BinaryPath.canonical_step nodes combine hnodes index height
  -- The shared value is also the truncation of the cached answer at the actual pair.
  have hactual : combine (height + 1) (index / 2 ^ (height + 1)) actual.1 actual.2 =
      Hashing.truncate output := by
    rw [hcombine, ← haddress]
    exact CacheReplay.tweakable_replayQuery cache publicSeed _ _ output hentry
  refine deviatingCollision_of_pair publicSeed cells parent left right actual.1 actual.2
    hchildren hdistinct ?_ result output ?_ ?_
  · -- The actual pair differs from the honest one.
    rw [hleftCell, hrightCell]
    exact fun hsame =>
      hdiffers (Prod.ext (congrArg Prod.fst hsame) (congrArg Prod.snd hsame))
  · rw [hcache]
    exact hentry
  · -- and its answer truncates to the parent's honest cell.
    rw [hparentCell, ← hcanonical, ← hjoins]
    exact hactual.symm

/-! ## Without the graph-side bookkeeping

Exactly as on the Merkle side: a FORS tree node's children are its two `forsChild`ren, its
address is `Fors.nodeAddress` at its own height, and the children's honest cells are the
canonical pair — the last by `MerkleCharge.canonicalPair_fst`/`_snd`, which are already stated
for an arbitrary `nodes`. -/

/-- A FORS tree node's child cell is the honest node one height down, at twice the index. -/
theorem value_forsChild (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : ForsKey) (height : Fin (forsHeight + 1)) (hpos : 0 < height.val)
    (index : Fin (forsTrees * 2 ^ (forsHeight - height.val))) (side : Fin 2) :
    @value (CacheReplay.replayQuery cache) secretSeed publicSeed
        (.structural (forsChild key height hpos index side)) =
      @SlhDsaSecurity.Fors.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
        key.address (height.val - 1) (2 * index.val + side.val) := rfl

/-- **A FORS path collision is charged, with the graph-side bookkeeping discharged.** -/
theorem deviatingCollision_of_pathCollision_canonical {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (key : ForsKey)
    (index : Nat) (pathHeight : Fin forsHeight)
    (hbound : index / 2 ^ (pathHeight.val + 1) <
      forsTrees * 2 ^ (forsHeight - (pathHeight.val + 1)))
    (leaf : Digest) (siblings : Nat → Digest)
    (combine : Nat → Nat → Digest → Digest → Digest)
    (hcombine : ∀ h i l r, combine h i l r =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
        (SlhDsaSecurity.Fors.nodeAddress key.address h i) (BinaryPath.pairBytes (l, r)))
    (hnodes : ∀ h i,
      @SlhDsaSecurity.Fors.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
          key.address (h + 1) i =
        combine (h + 1) i
          (@SlhDsaSecurity.Fors.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
            key.address h (2 * i))
          (@SlhDsaSecurity.Fors.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
            key.address h (2 * i + 1)))
    (hcollision : BinaryPath.Collision
      (@SlhDsaSecurity.Fors.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
        key.address)
      combine index leaf siblings pathHeight.val)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
        (StructuralNode.forsTree key ⟨pathHeight.val + 1, Nat.succ_lt_succ pathHeight.isLt⟩
          ⟨index / 2 ^ (pathHeight.val + 1), hbound⟩).address
        (BinaryPath.pairBytes
          (BinaryPath.ordered index pathHeight.val
            (BinaryPath.value combine index leaf siblings pathHeight.val)
            (siblings pathHeight.val)))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  have hlt : pathHeight.val + 1 < forsHeight + 1 := Nat.succ_lt_succ pathHeight.isLt
  have hpos : 0 < (⟨pathHeight.val + 1, hlt⟩ : Fin (forsHeight + 1)).val := Nat.succ_pos _
  refine deviatingCollision_of_pathCollision publicSeed
    (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) cache key.address
    (@SlhDsaSecurity.Fors.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
      key.address)
    index pathHeight.val leaf siblings
    (.forsTree key ⟨pathHeight.val + 1, hlt⟩ ⟨index / 2 ^ (pathHeight.val + 1), hbound⟩)
    (.structural (forsChild key ⟨pathHeight.val + 1, hlt⟩ hpos
      ⟨index / 2 ^ (pathHeight.val + 1), hbound⟩ 0))
    (.structural (forsChild key ⟨pathHeight.val + 1, hlt⟩ hpos
      ⟨index / 2 ^ (pathHeight.val + 1), hbound⟩ 1))
    combine hcombine hnodes rfl ?_ ?_ rfl ?_ ?_ hcollision result output hcache hentry
  · -- The two children are the node's children list.
    rfl
  · -- Distinct sides name distinct nodes.
    intro hsame
    have hval := congrArg (fun node : Node => match node with
      | .structural (.forsTree _ _ idx) => idx.val
      | _ => 0) hsame
    simp [forsChild] at hval
  · -- The left child's honest cell is the canonical pair's first component.
    rw [value_forsChild, MerkleCharge.canonicalPair_fst]
    simp
  · -- and the right child's is the second.
    rw [value_forsChild, MerkleCharge.canonicalPair_snd]
    simp

/-! ## The path branch as the extraction hands it over

`Extraction.Fors.root_eq_canonical_or_collision` reports the path collision with the
combination written out as the tweakable hash at `Fors.nodeAddress`, the nodes being the
honest FORS nodes of this tree and the leaf the compression of the revealed secret. Both
hypotheses the canonical lemma still carries are then definitional. -/

/-- **The path branch of a FORS tree collision is charged.** -/
theorem deviatingCollision_of_pathBranch {α : Type} (secretSeed publicSeed : Digest)
    (cache : QueryCache HashSpec) (key : ForsKey) (index : Nat) (leaf : Digest)
    (siblings : Nat → Digest) (pathHeight : Fin forsHeight)
    (hbound : index / 2 ^ (pathHeight.val + 1) <
      forsTrees * 2 ^ (forsHeight - (pathHeight.val + 1)))
    (hcollision : BinaryPath.Collision
      (@SlhDsaSecurity.Fors.node Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
        key.address)
      (fun height nodeIndex left right =>
        @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
          (SlhDsaSecurity.Fors.nodeAddress key.address height nodeIndex)
          (BinaryPath.pairBytes (left, right)))
      index leaf siblings pathHeight.val)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
        (StructuralNode.forsTree key ⟨pathHeight.val + 1, Nat.succ_lt_succ pathHeight.isLt⟩
          ⟨index / 2 ^ (pathHeight.val + 1), hbound⟩).address
        (BinaryPath.pairBytes
          (BinaryPath.ordered index pathHeight.val
            (BinaryPath.value
              (fun height nodeIndex left right =>
                @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
                  (SlhDsaSecurity.Fors.nodeAddress key.address height nodeIndex)
                  (BinaryPath.pairBytes (left, right)))
              index leaf siblings pathHeight.val)
            (siblings pathHeight.val)))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  refine deviatingCollision_of_pathCollision_canonical secretSeed publicSeed cache key index
    pathHeight hbound leaf siblings _ ?_ ?_ hcollision result output hcache hentry
  · intro h i l r
    rfl
  · intro h i
    rfl

/-! ## The three shapes, bundled

The companion of `Extraction.Hypertree.LayerCollision` for the FORS side: the three ways a
FORS verification that reaches the genuine public key can fault. The second and third are
reported per tree, since the decomposition splits the fourteen trees independently. -/

variable [HasQuery HashSpec Id]

/-- A concrete collision inside one FORS verification: at the root compression, on one tree's
authentication path, or at one tree's revealed leaf. -/
@[expose] def ForsCollision (secretSeed publicSeed : Digest) (address : Address)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature) : Prop :=
  let nodes : Nat → Nat → Digest :=
    SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address
  let combine : Nat → Nat → Digest → Digest → Digest := fun height nodeIndex left right =>
    Hashing.tweakable (m := Id) publicSeed
      (SlhDsaSecurity.Fors.nodeAddress address height nodeIndex)
      (BinaryPath.pairBytes (left, right))
  Extraction.Fors.CompressionCollision
      (Extraction.Fors.recoveredRoot signature indices publicSeed address)
      (Extraction.Fors.canonicalRoots secretSeed publicSeed address) publicSeed address ∨
    ∃ i : Fin forsTrees,
      (∃ j < forsHeight, BinaryPath.Collision nodes combine
          (Extraction.Fors.leafIndex indices i)
          (Extraction.Fors.recoveredLeaf signature indices publicSeed address i)
          (Extraction.Fors.siblings signature i) j) ∨
        Extraction.Fors.LeafCollision secretSeed publicSeed address
          (Extraction.Fors.leafIndex indices i) (signature i).secret

/-! ## The FORS dichotomy

The decomposition settles each tree in both of its parts — the recovered leaf and the twelve
siblings — so a signature with no collision anywhere is the signature `Fors.sign` writes, not
merely one whose secrets agree with it. Reading it that way is what lets a canonical FORS part
be compared with the part a signing request returned. -/

omit [HasQuery HashSpec Id] in
/-- The honest authentication index, as the extraction names it and as the signer computes it:
the sibling of the selected leaf at that height, offset by the tree. -/
theorem fors_auth_index (indices : SlhDsaSecurity.Fors.Indices) (i : Fin forsTrees)
    (j : Fin forsHeight) :
    Nat.xor (Extraction.Fors.leafIndex indices i / 2 ^ j.val) 1 =
      i.val * 2 ^ (forsHeight - j.val) + Nat.xor ((indices i).val / 2 ^ j.val) 1 := by
  rw [Extraction.Fors.leafIndex, Correctness.offset_div_pow _ _ _ _ (le_of_lt j.isLt),
    Correctness.xor_add_even _ _ (Correctness.offset_even i.val forsHeight j.val j.isLt)]

/-- The honest FORS signature, tree by tree. -/
theorem sign_apply (indices : SlhDsaSecurity.Fors.Indices) (secretSeed publicSeed : Digest)
    (address : Address) (i : Fin forsTrees) :
    SlhDsaSecurity.Fors.sign (m := Id) indices secretSeed publicSeed address i =
      { secret := SlhDsaSecurity.Fors.secret (m := Id) secretSeed publicSeed address
          (Extraction.Fors.leafIndex indices i),
        authentication := fun j => SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed
          address j.val (Nat.xor (Extraction.Fors.leafIndex indices i / 2 ^ j.val) 1) } := by
  simp only [SlhDsaSecurity.Fors.sign, Correctness.sequenceFin_id, bind, pure,
    Extraction.Fors.leafIndex, ForsTreeSignature.mk.injEq, true_and]
  funext j
  rw [← fors_auth_index indices i j]
  rfl

/-- **The FORS dichotomy.** A FORS signature reaching the genuine FORS public key either
contains one of the three collisions, or it *is* the honest FORS signature at those indices —
secrets and authentication paths alike. No collision resistance is assumed. -/
theorem forsCollision_or_canonical_signature (secretSeed publicSeed : Digest) (address : Address)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (hpk : SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id) signature indices publicSeed
        address =
      Hashing.tweakable (m := Id) publicSeed (Extraction.Fors.rootAddress address)
        (digestArrayBytes (Extraction.Fors.canonicalRoots secretSeed publicSeed address))) :
    ForsCollision secretSeed publicSeed address indices signature ∨
      signature = SlhDsaSecurity.Fors.sign (m := Id) indices secretSeed publicSeed address := by
  classical
  rcases Extraction.Fors.publicKey_canonical_decomposition secretSeed publicSeed address indices
      signature hpk with hcomp | htrees
  · exact Or.inl (Or.inl hcomp)
  by_cases hcanonical : ∀ i : Fin forsTrees,
      (signature i).secret = SlhDsaSecurity.Fors.secret (m := Id) secretSeed publicSeed address
          (Extraction.Fors.leafIndex indices i) ∧
        ∀ j, (signature i).authentication j =
          SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address j.val
            (Nat.xor (Extraction.Fors.leafIndex indices i / 2 ^ j.val) 1)
  · refine Or.inr (funext fun i => ?_)
    obtain ⟨hsecret, hauth⟩ := hcanonical i
    rw [sign_apply]
    cases hsignature : signature i
    rw [hsignature] at hsecret hauth
    exact congrArg₂ ForsTreeSignature.mk hsecret (funext hauth)
  · obtain ⟨i, hi⟩ := not_forall.mp hcanonical
    have htree := htrees i
    dsimp only at htree
    rcases htree with ⟨hleaf, hauth⟩ | hpath
    · rcases Extraction.Fors.recoveredLeaf_canonical_secret_or_collision secretSeed publicSeed
        address indices signature i hleaf with hsecret | hleafCollision
      · exact absurd ⟨hsecret, hauth⟩ hi
      · exact Or.inl (Or.inr ⟨i, Or.inr hleafCollision⟩)
    · exact Or.inl (Or.inr ⟨i, Or.inl hpath⟩)

/-- The dichotomy, read only for the revealed secrets. -/
theorem forsCollision_or_canonical_secrets (secretSeed publicSeed : Digest) (address : Address)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (hpk : SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id) signature indices publicSeed
        address =
      Hashing.tweakable (m := Id) publicSeed (Extraction.Fors.rootAddress address)
        (digestArrayBytes (Extraction.Fors.canonicalRoots secretSeed publicSeed address))) :
    ForsCollision secretSeed publicSeed address indices signature ∨
      ∀ i : Fin forsTrees, (signature i).secret =
        SlhDsaSecurity.Fors.secret (m := Id) secretSeed publicSeed address
          (Extraction.Fors.leafIndex indices i) :=
  (forsCollision_or_canonical_signature secretSeed publicSeed address indices signature hpk).imp
    id fun hsign i => by rw [hsign, sign_apply]

/-! ## The index bookkeeping that is discharged

The one arithmetic fact the dispatch needs about FORS indices: the global leaf index of tree
`i` stays inside the rectangle of nodes at every height, which is what the canonical graph's
`Fin` bounds demand. `Correctness.offset_div_pow` splits the division across the tree offset,
and the rest is the leaf index being below `2 ^ forsHeight`. -/

omit [HasQuery HashSpec Id] in
/-- The global leaf index of FORS tree `i`, shifted down by `level`, lies inside the rectangle of
nodes at that height. -/
theorem leafIndex_div_lt (indices : SlhDsaSecurity.Fors.Indices) (i : Fin forsTrees)
    (level : Nat) (hlevel : level ≤ forsHeight) :
    Extraction.Fors.leafIndex indices i / 2 ^ level < forsTrees * 2 ^ (forsHeight - level) := by
  rw [Extraction.Fors.leafIndex, Correctness.offset_div_pow _ _ _ _ hlevel]
  have hpow : (2 : Nat) ^ level * 2 ^ (forsHeight - level) = 2 ^ forsHeight := by
    rw [← pow_add]
    congr 1
    omega
  have hlt : (indices i).val < 2 ^ level * 2 ^ (forsHeight - level) := by
    rw [hpow]
    exact (indices i).isLt
  have hleaf : (indices i).val / 2 ^ level < 2 ^ (forsHeight - level) :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)
  have hstep : i.val * 2 ^ (forsHeight - level) + (indices i).val / 2 ^ level <
      i.val * 2 ^ (forsHeight - level) + 2 ^ (forsHeight - level) :=
    Nat.add_lt_add_left hleaf _
  have hfit : i.val * 2 ^ (forsHeight - level) + 2 ^ (forsHeight - level) ≤
      forsTrees * 2 ^ (forsHeight - level) := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul i.isLt (Nat.le_refl _)
  exact Nat.lt_of_lt_of_le hstep hfit

/-! ## The dispatch

Each shape to its own charge. The cache entries come from `CacheReplay`: the root compression
is a prefix followed by one hash, so `CacheReplay.queriesUnder_compression` reaches it; a
revealed leaf is a bare tweakable call, so `CacheReplay.queriesUnder_tweakable_self` does; and
a tree path is a fold, which is what `PathEntry.queriesUnder_pathInput` is for — hence the path
hypothesis below is phrased with `PathEntry.pathInput` and `PathEntry.pathCombine`, as that
lemma delivers it. -/

omit [HasQuery HashSpec Id] in
/-- **A FORS collision is a charged structural event.** -/
theorem deviatingCollision_of_forsCollision {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (key : ForsKey)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (hcollision : @ForsCollision (CacheReplay.replayQuery cache) secretSeed publicSeed
      key.address indices signature)
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache)
    -- the root compression's own query
    (hcompressionEntry : cache (Hashing.tweakableInput publicSeed
      (StructuralNode.forsRoots key).address
      (digestArrayBytes (@Extraction.Fors.recoveredRoot (CacheReplay.replayQuery cache)
        signature indices publicSeed key.address))) ≠ none)
    -- every path step's own query
    (hpathEntry : ∀ (i : Fin forsTrees) (step : Fin forsHeight),
      cache (PathEntry.pathInput publicSeed (SlhDsaSecurity.Fors.nodeAddress key.address)
        (Extraction.Fors.leafIndex indices i) (Extraction.Fors.siblings signature i)
        (BinaryPath.value
          (PathEntry.pathCombine cache publicSeed
            (SlhDsaSecurity.Fors.nodeAddress key.address))
          (Extraction.Fors.leafIndex indices i)
          (@Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) signature indices
            publicSeed key.address i)
          (Extraction.Fors.siblings signature i) step.val) step) ≠ none)
    -- every revealed leaf's own query
    (hleafEntry : ∀ i : Fin forsTrees, cache (Hashing.tweakableInput publicSeed
      (SlhDsaSecurity.Fors.nodeAddress key.address 0 (Extraction.Fors.leafIndex indices i))
      (bytesBE n (signature i).secret)) ≠ none) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  simp only [ForsCollision] at hcollision
  rcases hcollision with hcomp | ⟨i, hpath | hleaf⟩
  · -- The root compression.
    obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcompressionEntry
    exact ForsCharge.deviatingCollision_of_compressionCollision_canonical secretSeed publicSeed
      cache key _ hcomp result output hcache houtput
  · -- One tree's authentication path.
    obtain ⟨step, hstep, hcollision⟩ := hpath
    obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hpathEntry i ⟨step, hstep⟩)
    exact deviatingCollision_of_pathBranch secretSeed publicSeed cache key
      (Extraction.Fors.leafIndex indices i)
      (@Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) signature indices
        publicSeed key.address i)
      (Extraction.Fors.siblings signature i) ⟨step, hstep⟩
      (leafIndex_div_lt indices i (step + 1) hstep) hcollision result output hcache houtput
  · -- One tree's revealed leaf.
    obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hleafEntry i)
    have hindex : Extraction.Fors.leafIndex indices i < forsTrees * 2 ^ forsHeight := by
      simpa using leafIndex_div_lt indices i 0 (Nat.zero_le _)
    exact ForsLeafCharge.deviatingCollision_of_leafCollision_canonical secretSeed publicSeed
      cache key ⟨Extraction.Fors.leafIndex indices i, hindex⟩ (signature i).secret hleaf
      result output hcache houtput

end SlhDsaSecurity.ForsDispatch
