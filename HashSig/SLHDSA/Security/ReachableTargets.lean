/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.GeneralScheme
public import HashSig.SLHDSA.Security.Architecture

/-!
# Reachable SLH-DSA target coordinates

This module enumerates the layer-indexed XMSS trees and WOTS instances in a validated SLH-DSA
hypertree.  The coordinates reuse `LayerPosition`, the owner of the FIPS 205 tree/leaf bounds,
rather than introducing a second reachability model.  Their cardinalities are proved equal to
the `xmssTreeCount` and `wotsInstanceCount` parameters used by the security games.

The address lists remain structural `Adrs` values.  A concrete primitive maps them to its
`AdrsKey` only after proving injectivity on the listed reachable family; no global injectivity of
compressed SHA-2 addresses is assumed here.

## References

- NIST FIPS 205, Algorithms 10--13
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
-/

@[expose] public section

namespace SLHDSA.Security

/-! ## Typed tree and leaf coordinates -/

/-- A reachable XMSS tree, with the exact tree bound determined by its hypertree layer. -/
structure LayerTreeCoord (vp : ValidatedParams) where
  /-- Hypertree layer, starting at zero. -/
  layer : Fin vp.params.d
  /-- Tree at this layer. -/
  tree : Fin (2 ^ layerTreeHeight vp layer.val)
deriving Repr, DecidableEq, Fintype

namespace LayerTreeCoord

/-- Forget the leaf of a canonical position and retain its containing XMSS tree. -/
def ofPosition {vp : ValidatedParams} (pos : LayerPosition vp) : LayerTreeCoord vp :=
  ⟨pos.layer, pos.tree⟩

end LayerTreeCoord

/-- The product representation of a reachable layer position.  This equivalence is the explicit
owner bridge used to enumerate the existing dependent structure. -/
def layerPositionEquiv (vp : ValidatedParams) :
    LayerPosition vp ≃
      (Σ layer : Fin vp.params.d,
        Fin (2 ^ layerTreeHeight vp layer.val) × Fin (2 ^ vp.params.hp)) where
  toFun pos := ⟨pos.layer, pos.tree, pos.leaf⟩
  invFun coord := ⟨coord.1, coord.2.1, coord.2.2⟩
  left_inv pos := by cases pos; rfl
  right_inv coord := by cases coord; rfl

/-- Reachable layer positions form a finite type because all three FIPS coordinates are bounded. -/
instance (vp : ValidatedParams) : Fintype (LayerPosition vp) :=
  Fintype.ofEquiv _ (layerPositionEquiv vp).symm

/-- The target-count exponent agrees with the canonical `LayerPosition` exponent. -/
theorem treesAtLayer_eq_layerTreeHeight (vp : ValidatedParams) (layer : Fin vp.params.d) :
    treesAtLayer vp.params layer = 2 ^ layerTreeHeight vp layer.val := by
  unfold treesAtLayer
  congr 1
  simp only [layerTreeHeight]
  have hsub : vp.params.d - layer.val - 1 = vp.params.d - (layer.val + 1) := by omega
  rw [hsub, Nat.mul_comm]

/-- Enumerate every reachable XMSS tree exactly once. -/
def allXmssTrees (vp : ValidatedParams) : List (LayerTreeCoord vp) :=
  (List.finRange vp.params.d).flatMap fun layer =>
    (List.finRange (2 ^ layerTreeHeight vp layer.val)).map fun tree => ⟨layer, tree⟩

/-- Enumerate every reachable WOTS instance exactly once, using the canonical position type. -/
def allWotsInstances (vp : ValidatedParams) : List (LayerPosition vp) :=
  (allXmssTrees vp).flatMap fun coord =>
    (List.finRange (2 ^ vp.params.hp)).map fun leaf =>
      ⟨coord.layer, coord.tree, leaf⟩

@[simp]
theorem allXmssTrees_nodup (vp : ValidatedParams) : (allXmssTrees vp).Nodup :=
    by
  rw [allXmssTrees, List.nodup_flatMap]
  constructor
  · intro layer _
    exact (List.nodup_finRange _).map_on (by
      intro tree _ tree' _ hcoord
      exact Fin.ext (congrArg (fun coord : LayerTreeCoord vp => coord.tree.val) hcoord))
  · have hlayers : List.Pairwise (fun a b : Fin vp.params.d => a ≠ b)
        (List.finRange vp.params.d) :=
      List.nodup_iff_pairwise_ne.mp (List.nodup_finRange _)
    apply hlayers.imp
    intro layer layer' hne
    change List.Disjoint _ _
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    obtain ⟨tree, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨tree', _, rfl⟩ := List.mem_map.mp hb
    apply hne
    exact congrArg (fun coord : LayerTreeCoord vp => coord.layer) hab

@[simp]
theorem allWotsInstances_nodup (vp : ValidatedParams) : (allWotsInstances vp).Nodup :=
    by
  rw [allWotsInstances, List.nodup_flatMap]
  constructor
  · intro coord _
    exact (List.nodup_finRange _).map_on (by
      intro leaf _ leaf' _ hpos
      exact Fin.ext (congrArg (fun pos : LayerPosition vp => pos.leaf.val) hpos))
  · have htrees : List.Pairwise (fun a b : LayerTreeCoord vp => a ≠ b)
        (allXmssTrees vp) :=
      List.nodup_iff_pairwise_ne.mp (allXmssTrees_nodup vp)
    apply htrees.imp
    intro coord coord' hne
    change List.Disjoint _ _
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    obtain ⟨leaf, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨leaf', _, rfl⟩ := List.mem_map.mp hb
    apply hne
    cases coord with
    | mk layer tree =>
      cases coord' with
      | mk layer' tree' =>
        have hlayer : layer = layer' :=
          congrArg (fun pos : LayerPosition vp => pos.layer) hab
        subst layer'
        have htree : tree = tree' := Fin.ext
          (congrArg (fun pos : LayerPosition vp => pos.tree.val) hab)
        subst tree'
        rfl

/-- The typed XMSS-tree enumeration realizes the game architecture's tree count exactly. -/
@[simp]
theorem allXmssTrees_length (vp : ValidatedParams) :
    (allXmssTrees vp).length = xmssTreeCount vp.params := by
  simp only [allXmssTrees, List.length_flatMap, List.length_map,
    List.length_finRange]
  change ((List.finRange vp.params.d).map
    (fun layer => 2 ^ layerTreeHeight vp layer.val)).sum = xmssTreeCount vp.params
  rw [← List.sum_toFinset _ (List.nodup_finRange vp.params.d)]
  rw [List.toFinset_finRange]
  unfold xmssTreeCount
  apply Finset.sum_congr rfl
  intro layer _
  symm
  exact treesAtLayer_eq_layerTreeHeight vp layer

/-- The typed WOTS-instance enumeration realizes the game architecture's instance count exactly. -/
@[simp]
theorem allWotsInstances_length (vp : ValidatedParams) :
    (allWotsInstances vp).length = wotsInstanceCount vp.params := by
  calc
    (allWotsInstances vp).length =
        (allXmssTrees vp).length * 2 ^ vp.params.hp := by
      simp [allWotsInstances]
    _ = xmssTreeCount vp.params * 2 ^ vp.params.hp := by
      rw [allXmssTrees_length]
    _ = wotsInstanceCount vp.params := by
      unfold wotsInstanceCount xmssTreeCount
      exact Finset.sum_mul Finset.univ (treesAtLayer vp.params) (2 ^ vp.params.hp)

namespace LayerTreeCoord

/-- The base address of a reachable XMSS tree. -/
def toAdrs {vp : ValidatedParams} (coord : LayerTreeCoord vp) : Adrs :=
  (Adrs.zero.setLayerAddress coord.layer.val).setTreeAddress coord.tree.val

@[simp]
theorem toAdrs_layer {vp : ValidatedParams} (coord : LayerTreeCoord vp) :
    coord.toAdrs.layer = coord.layer.val := rfl

@[simp]
theorem toAdrs_tree {vp : ValidatedParams} (coord : LayerTreeCoord vp) :
    coord.toAdrs.tree = coord.tree.val := rfl

@[simp]
theorem ofPosition_toAdrs {vp : ValidatedParams} (pos : LayerPosition vp) :
    (ofPosition pos).toAdrs = pos.toAdrs := rfl

end LayerTreeCoord

/-! ## Perfect-tree internal nodes -/

/-- Internal nodes of a perfect binary tree, listed bottom-up as `(height, index)` pairs. -/
def perfectInternalCoords : ℕ → List (ℕ × ℕ)
  | 0 => []
  | h + 1 =>
      (List.range (2 ^ h)).map (fun i => (1, i)) ++
        (perfectInternalCoords h).map (fun zi => (zi.1 + 1, zi.2))

/-- A perfect binary tree of height `h` has exactly `2^h - 1` internal coordinates. -/
@[simp]
theorem perfectInternalCoords_length (h : ℕ) :
    (perfectInternalCoords h).length = 2 ^ h - 1 := by
  induction h with
  | zero => simp [perfectInternalCoords]
  | succ h ih =>
      simp [perfectInternalCoords, ih, pow_succ]
      omega

theorem perfectInternalCoords_height_pos {h : ℕ} {zi : ℕ × ℕ}
    (hmem : zi ∈ perfectInternalCoords h) : 0 < zi.1 := by
  induction h with
  | zero => simp [perfectInternalCoords] at hmem
  | succ h ih =>
      simp only [perfectInternalCoords, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨i, _, rfl⟩ | ⟨zi, hzi, rfl⟩
      · simp
      · exact Nat.succ_pos zi.1

/-- An internal coordinate's height never exceeds its perfect-tree height. -/
theorem perfectInternalCoords_height_le {h : ℕ} {zi : ℕ × ℕ}
    (hmem : zi ∈ perfectInternalCoords h) : zi.1 ≤ h := by
  induction h generalizing zi with
  | zero => simp [perfectInternalCoords] at hmem
  | succ h ih =>
      simp only [perfectInternalCoords, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨i, _, rfl⟩ | ⟨zi, hzi, rfl⟩
      · exact Nat.succ_le_succ (Nat.zero_le h)
      · exact Nat.succ_le_succ (ih hzi)

/-- At height `z`, a perfect tree of height `h` has `2^(h-z)` node positions. -/
theorem perfectInternalCoords_index_lt {h : ℕ} {zi : ℕ × ℕ}
    (hmem : zi ∈ perfectInternalCoords h) : zi.2 < 2 ^ (h - zi.1) := by
  induction h generalizing zi with
  | zero => simp [perfectInternalCoords] at hmem
  | succ h ih =>
      simp only [perfectInternalCoords, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨i, hi, rfl⟩ | ⟨zi, hzi, rfl⟩
      · simpa using hi
      · simpa only [Nat.succ_sub_succ_eq_sub] using ih hzi

/-- Internal perfect-tree coordinates are never repeated. -/
theorem perfectInternalCoords_nodup (h : ℕ) :
    (perfectInternalCoords h).Nodup := by
  induction h with
  | zero => simp [perfectInternalCoords]
  | succ h ih =>
      rw [perfectInternalCoords, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact List.nodup_range.map (fun _ _ hpair => Prod.mk.inj hpair |>.2)
      · exact ih.map (fun _ _ hpair => by
          have hfst := congrArg Prod.fst hpair
          have hsnd := congrArg Prod.snd hpair
          exact Prod.ext (Nat.succ.inj hfst) hsnd)
      · intro x hxLeft y hxRight hxy
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hxLeft
        obtain ⟨zi, hzi, rfl⟩ := List.mem_map.mp hxRight
        have hheight := congrArg Prod.fst hxy
        have hpos := perfectInternalCoords_height_pos hzi
        simp only at hheight
        omega

/-! ## Bottom-layer FORS coordinates -/

/-- A reachable layer-zero position, where an SLH-DSA signature places its FORS instance. -/
structure BottomPosition (vp : ValidatedParams) where
  /-- XMSS tree at layer zero. -/
  tree : Fin (2 ^ layerTreeHeight vp 0)
  /-- XMSS leaf, which is also the FORS key-pair address. -/
  leaf : Fin (2 ^ vp.params.hp)
deriving Repr, DecidableEq, Fintype

namespace BottomPosition

/-- View a bottom position through the canonical layer-position API. -/
def toLayerPosition {vp : ValidatedParams} (pos : BottomPosition vp) : LayerPosition vp where
  layer := ⟨0, vp.valid.d_pos⟩
  tree := pos.tree
  leaf := pos.leaf

/-- Turn the indices parsed by Algorithm 19 into their typed bottom position. -/
def ofDigestParts (vp : ValidatedParams) (parts : DigestParts vp.params) : BottomPosition vp where
  tree := ⟨parts.idxTree.val, by
    simpa [layerTreeHeight, vp.valid.h_eq_layers, Nat.sub_mul] using parts.idxTree.isLt⟩
  leaf := parts.idxLeaf

/-- The base FORS address consumed by `GeneralScheme.signInternalM` and `verifyInternalM`. -/
def forsAdrs {vp : ValidatedParams} (pos : BottomPosition vp) : Adrs :=
  ((pos.toLayerPosition.toAdrs.setTypeAndClear .forsTree).setKeyPairAddress pos.leaf.val)

@[simp]
theorem forsAdrs_ofDigestParts (vp : ValidatedParams) (parts : DigestParts vp.params) :
    (ofDigestParts vp parts).forsAdrs = parts.forsAdrs := by
  rfl

@[simp]
theorem forsAdrs_tree {vp : ValidatedParams} (pos : BottomPosition vp) :
    pos.forsAdrs.tree = pos.tree.val := rfl

@[simp]
theorem forsAdrs_keyPair {vp : ValidatedParams} (pos : BottomPosition vp) :
    pos.forsAdrs.getKeyPairAddress = pos.leaf.val := rfl

end BottomPosition

/-- Enumerate every possible FORS instance position at layer zero exactly once. -/
def allBottomPositions (vp : ValidatedParams) : List (BottomPosition vp) :=
  (List.finRange (2 ^ layerTreeHeight vp 0)).flatMap fun tree =>
    (List.finRange (2 ^ vp.params.hp)).map fun leaf => ⟨tree, leaf⟩

@[simp]
theorem allBottomPositions_nodup (vp : ValidatedParams) :
    (allBottomPositions vp).Nodup := by
  rw [allBottomPositions, List.nodup_flatMap]
  constructor
  · intro tree _
    exact (List.nodup_finRange _).map_on (by
      intro leaf _ leaf' _ hpos
      exact Fin.ext (congrArg (fun pos : BottomPosition vp => pos.leaf.val) hpos))
  · have htrees : List.Pairwise
        (fun a b : Fin (2 ^ layerTreeHeight vp 0) => a ≠ b)
        (List.finRange (2 ^ layerTreeHeight vp 0)) :=
      List.nodup_iff_pairwise_ne.mp (List.nodup_finRange _)
    apply htrees.imp
    intro tree tree' hne
    change List.Disjoint _ _
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    obtain ⟨leaf, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨leaf', _, rfl⟩ := List.mem_map.mp hb
    apply hne
    exact congrArg (fun pos : BottomPosition vp => pos.tree) hab

/-- The layer-zero position space has exactly `2^h` elements. -/
@[simp]
theorem allBottomPositions_length (vp : ValidatedParams) :
    (allBottomPositions vp).length = 2 ^ vp.params.h := by
  calc
    (allBottomPositions vp).length =
        2 ^ layerTreeHeight vp 0 * 2 ^ vp.params.hp := by
      simp [allBottomPositions]
    _ = 2 ^ (layerTreeHeight vp 0 + vp.params.hp) := by rw [pow_add]
    _ = 2 ^ vp.params.h := by
      congr 1
      unfold layerTreeHeight
      simp only [Nat.zero_add]
      have hdpos := vp.valid.d_pos
      have hd : vp.params.d - 1 + 1 = vp.params.d := by omega
      calc
        (vp.params.d - 1) * vp.params.hp + vp.params.hp =
            (vp.params.d - 1 + 1) * vp.params.hp := by
          rw [Nat.add_mul, one_mul]
        _ = vp.params.d * vp.params.hp := by rw [hd]
        _ = vp.params.h := vp.valid.h_eq_layers.symm

/-! ## FORS target ledgers -/

/-- Every arity-one FORS leaf target over every reachable bottom-layer position. -/
def forsLeafAddresses (vp : ValidatedParams) : List Adrs :=
  (((allBottomPositions vp).product (List.finRange vp.params.k)).product
    (List.finRange vp.params.t)).map fun coord =>
      forsNodeAdrs coord.1.1.forsAdrs 0 (coord.1.2.val * vp.params.t + coord.2.val)

/-- Every arity-two FORS internal-node target over every reachable bottom-layer position. -/
def forsTreeAddresses (vp : ValidatedParams) : List Adrs :=
  (((allBottomPositions vp).product (List.finRange vp.params.k)).product
    (perfectInternalCoords vp.params.a)).map fun coord =>
      forsNodeAdrs coord.1.1.forsAdrs coord.2.1
        (coord.1.2.val * 2 ^ (vp.params.a - coord.2.1) + coord.2.2)

/-- Every arity-`k` FORS-root-compression target over all bottom-layer positions. -/
def forsRootAddresses (vp : ValidatedParams) : List Adrs :=
  (allBottomPositions vp).map fun pos => forsPkAdrs pos.forsAdrs

@[simp]
theorem forsLeafAddresses_length (vp : ValidatedParams) :
    (forsLeafAddresses vp).length = targetCount vp.params .forsF := by
  rw [forsLeafAddresses, List.length_map]
  calc
    (((allBottomPositions vp).product (List.finRange vp.params.k)).product
        (List.finRange vp.params.t)).length =
        ((allBottomPositions vp).product (List.finRange vp.params.k)).length *
          (List.finRange vp.params.t).length := List.length_product _ _
    _ = ((allBottomPositions vp).length * (List.finRange vp.params.k).length) *
          (List.finRange vp.params.t).length := by
      congr 1
      exact List.length_product _ _
    _ = targetCount vp.params .forsF := by simp [targetCount, Params.t]

@[simp]
theorem forsTreeAddresses_length (vp : ValidatedParams) :
    (forsTreeAddresses vp).length = targetCount vp.params .forsH := by
  rw [forsTreeAddresses, List.length_map]
  calc
    (((allBottomPositions vp).product (List.finRange vp.params.k)).product
        (perfectInternalCoords vp.params.a)).length =
        ((allBottomPositions vp).product (List.finRange vp.params.k)).length *
          (perfectInternalCoords vp.params.a).length := List.length_product _ _
    _ = ((allBottomPositions vp).length * (List.finRange vp.params.k).length) *
          (perfectInternalCoords vp.params.a).length := by
      congr 1
      exact List.length_product _ _
    _ = targetCount vp.params .forsH := by simp [targetCount]

@[simp]
theorem forsRootAddresses_length (vp : ValidatedParams) :
    (forsRootAddresses vp).length = targetCount vp.params .forsTl := by
  simp [forsRootAddresses, targetCount]

/-- FORS leaf targets are structurally duplicate-free before concrete address encoding. -/
theorem forsLeafAddresses_nodup (vp : ValidatedParams) :
    (forsLeafAddresses vp).Nodup := by
  have hcoords := ((allBottomPositions_nodup vp).product
    (List.nodup_finRange vp.params.k)).product (List.nodup_finRange vp.params.t)
  apply hcoords.map_on
  intro c _ d _ hadrs
  rcases c with ⟨⟨⟨ctree, cleaf⟩, cfors⟩, cnode⟩
  rcases d with ⟨⟨⟨dtree, dleaf⟩, dfors⟩, dnode⟩
  have hbottomTree : ctree = dtree := Fin.ext (by
    simpa [forsNodeAdrs, BottomPosition.forsAdrs, BottomPosition.toLayerPosition,
      LayerPosition.toAdrs, Adrs.getKeyPairAddress, Adrs.setTreeHeight,
      Adrs.setTreeIndex, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
      Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.zero] using
        congrArg Adrs.tree hadrs)
  subst dtree
  have hbottomLeaf : cleaf = dleaf := Fin.ext (by
    simpa [forsNodeAdrs, BottomPosition.forsAdrs, BottomPosition.toLayerPosition,
      LayerPosition.toAdrs, Adrs.getKeyPairAddress, Adrs.setTreeHeight,
      Adrs.setTreeIndex, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
      Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.zero] using
        congrArg Adrs.word1 hadrs)
  subst dleaf
  have hglobal : cfors.val * vp.params.t + cnode.val =
      dfors.val * vp.params.t + dnode.val := by
    simpa [forsNodeAdrs, BottomPosition.forsAdrs, BottomPosition.toLayerPosition,
      LayerPosition.toAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.setKeyPairAddress, Adrs.setTypeAndClear] using congrArg Adrs.word3 hadrs
  have htpos : 0 < vp.params.t := by unfold Params.t; positivity
  have hfors : cfors = dfors := Fin.ext (by
    have hdiv := congrArg (fun x => x / vp.params.t) hglobal
    simpa [Nat.add_comm, Nat.add_mul_div_right, Nat.div_eq_of_lt,
      cnode.isLt, dnode.isLt, htpos] using hdiv)
  subst dfors
  have hnode : cnode = dnode := Fin.ext (by
    have hmod := congrArg (fun x => x % vp.params.t) hglobal
    simpa [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt,
      cnode.isLt, dnode.isLt] using hmod)
  subst dnode
  rfl

/-- FORS internal-node targets are structurally duplicate-free before concrete encoding. -/
theorem forsTreeAddresses_nodup (vp : ValidatedParams) :
    (forsTreeAddresses vp).Nodup := by
  have hcoords := ((allBottomPositions_nodup vp).product
    (List.nodup_finRange vp.params.k)).product
      (perfectInternalCoords_nodup vp.params.a)
  apply hcoords.map_on
  intro c hc d hd hadrs
  rcases c with ⟨⟨⟨ctree, cleaf⟩, cfors⟩, cnode⟩
  rcases d with ⟨⟨⟨dtree, dleaf⟩, dfors⟩, dnode⟩
  have hbottomTree : ctree = dtree := Fin.ext (by
    simpa [forsNodeAdrs, BottomPosition.forsAdrs, BottomPosition.toLayerPosition,
      LayerPosition.toAdrs, Adrs.getKeyPairAddress, Adrs.setTreeHeight,
      Adrs.setTreeIndex, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
      Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.zero] using
        congrArg Adrs.tree hadrs)
  subst dtree
  have hbottomLeaf : cleaf = dleaf := Fin.ext (by
    simpa [forsNodeAdrs, BottomPosition.forsAdrs, BottomPosition.toLayerPosition,
      LayerPosition.toAdrs, Adrs.getKeyPairAddress, Adrs.setTreeHeight,
      Adrs.setTreeIndex, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
      Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.zero] using
        congrArg Adrs.word1 hadrs)
  subst dleaf
  have hheight : cnode.1 = dnode.1 := by
    simpa [forsNodeAdrs, BottomPosition.forsAdrs, BottomPosition.toLayerPosition,
      LayerPosition.toAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.setKeyPairAddress, Adrs.setTypeAndClear] using congrArg Adrs.word2 hadrs
  have hglobal : cfors.val * 2 ^ (vp.params.a - cnode.1) + cnode.2 =
      dfors.val * 2 ^ (vp.params.a - dnode.1) + dnode.2 := by
    simpa [forsNodeAdrs, BottomPosition.forsAdrs, BottomPosition.toLayerPosition,
      LayerPosition.toAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.setKeyPairAddress, Adrs.setTypeAndClear] using congrArg Adrs.word3 hadrs
  rw [hheight] at hglobal
  have hcPair :
      BottomPosition.mk ctree cleaf ∈ allBottomPositions vp ∧
        cnode ∈ perfectInternalCoords vp.params.a := by
    simpa [forsTreeAddresses, List.product] using hc
  have hdPair :
      BottomPosition.mk ctree cleaf ∈ allBottomPositions vp ∧
        dnode ∈ perfectInternalCoords vp.params.a := by
    simpa [forsTreeAddresses, List.product] using hd
  have hcMembership : cnode ∈ perfectInternalCoords vp.params.a := hcPair.2
  have hdMembership : dnode ∈ perfectInternalCoords vp.params.a := hdPair.2
  have hcBound := perfectInternalCoords_index_lt hcMembership
  have hdBound := perfectInternalCoords_index_lt hdMembership
  have hcBound' : cnode.2 < 2 ^ (vp.params.a - dnode.1) := by
    simpa [hheight] using hcBound
  have hpow : 0 < 2 ^ (vp.params.a - dnode.1) := by positivity
  have hfors : cfors = dfors := Fin.ext (by
    have hdiv := congrArg (fun x => x / 2 ^ (vp.params.a - dnode.1)) hglobal
    simpa [Nat.add_comm, Nat.add_mul_div_right, Nat.div_eq_of_lt,
      hcBound', hdBound, hpow] using hdiv)
  subst dfors
  have hnodeIndex : cnode.2 = dnode.2 := by
    have hmod := congrArg (fun x => x % 2 ^ (vp.params.a - dnode.1)) hglobal
    simpa [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt,
      hcBound', hdBound] using hmod
  have hnode : cnode = dnode := Prod.ext hheight hnodeIndex
  subst dnode
  rfl

/-- FORS root-compression targets are structurally duplicate-free before concrete encoding. -/
theorem forsRootAddresses_nodup (vp : ValidatedParams) :
    (forsRootAddresses vp).Nodup := by
  apply (allBottomPositions_nodup vp).map_on
  intro c _ d _ hadrs
  cases c with
  | mk ctree cleaf =>
    cases d with
    | mk dtree dleaf =>
      have htree : ctree = dtree := Fin.ext (by
        simpa [forsRootAddresses, forsPkAdrs, BottomPosition.forsAdrs,
          BottomPosition.toLayerPosition, LayerPosition.toAdrs,
          Adrs.getKeyPairAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
          Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.zero] using
            congrArg Adrs.tree hadrs)
      subst dtree
      have hleaf : cleaf = dleaf := Fin.ext (by
        simpa [forsRootAddresses, forsPkAdrs, BottomPosition.forsAdrs,
          BottomPosition.toLayerPosition, LayerPosition.toAdrs,
          Adrs.getKeyPairAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
          Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.zero] using
            congrArg Adrs.word1 hadrs)
      subst dleaf
      rfl

/-! ## XMSS and WOTS address ledgers -/

/-- Every internal node of every reachable XMSS tree. -/
def xmssNodeAddresses (vp : ValidatedParams) : List Adrs :=
  ((allXmssTrees vp).product (perfectInternalCoords vp.params.hp)).map fun coord =>
    xmssNodeAdrs coord.1.toAdrs coord.2.1 coord.2.2

/-- The XMSS internal-node ledger realizes the `xmssH` role's target count exactly. -/
@[simp]
theorem xmssNodeAddresses_length (vp : ValidatedParams) :
    (xmssNodeAddresses vp).length = targetCount vp.params .xmssH := by
  calc
    (xmssNodeAddresses vp).length =
        (allXmssTrees vp).length * (perfectInternalCoords vp.params.hp).length := by
      rw [xmssNodeAddresses, List.length_map]
      exact List.length_product _ _
    _ = xmssTreeCount vp.params * (2 ^ vp.params.hp - 1) := by simp
    _ = targetCount vp.params .xmssH := rfl

/-- XMSS internal-node addresses are structurally duplicate-free before concrete encoding. -/
theorem xmssNodeAddresses_nodup (vp : ValidatedParams) :
    (xmssNodeAddresses vp).Nodup := by
  have hcoords := (allXmssTrees_nodup vp).product
    (perfectInternalCoords_nodup vp.params.hp)
  apply hcoords.map_on
  intro a _ b _ hadrs
  rcases a with ⟨⟨aLayer, aTree⟩, aNode⟩
  rcases b with ⟨⟨bLayer, bTree⟩, bNode⟩
  apply Prod.ext
  · have hlayer : aLayer = bLayer := Fin.ext (by
      simpa [xmssNodeAdrs, LayerTreeCoord.toAdrs, Adrs.setTreeHeight,
        Adrs.setTreeIndex, Adrs.setTypeAndClear, Adrs.setTreeAddress,
        Adrs.setLayerAddress, Adrs.zero] using congrArg Adrs.layer hadrs)
    subst bLayer
    have htree : aTree = bTree := Fin.ext (by
      simpa [xmssNodeAdrs, LayerTreeCoord.toAdrs, Adrs.setTreeHeight,
        Adrs.setTreeIndex, Adrs.setTypeAndClear, Adrs.setTreeAddress,
        Adrs.setLayerAddress, Adrs.zero] using congrArg Adrs.tree hadrs)
    subst bTree
    rfl
  · apply Prod.ext
    · simpa [xmssNodeAdrs, LayerTreeCoord.toAdrs, Adrs.setTreeHeight,
        Adrs.setTreeIndex, Adrs.setTypeAndClear] using congrArg Adrs.word2 hadrs
    · simpa [xmssNodeAdrs, LayerTreeCoord.toAdrs, Adrs.setTreeHeight,
        Adrs.setTreeIndex, Adrs.setTypeAndClear] using congrArg Adrs.word3 hadrs

/-- The base WOTS address belonging to a reachable canonical position. -/
def wotsInstanceAdrs {vp : ValidatedParams} (pos : LayerPosition vp) : Adrs :=
  wotsLeafAdrs pos.toAdrs pos.leaf.val

@[simp]
theorem wotsInstanceAdrs_layer {vp : ValidatedParams} (pos : LayerPosition vp) :
    (wotsInstanceAdrs pos).layer = pos.layer.val := rfl

@[simp]
theorem wotsInstanceAdrs_tree {vp : ValidatedParams} (pos : LayerPosition vp) :
    (wotsInstanceAdrs pos).tree = pos.tree.val := rfl

@[simp]
theorem wotsInstanceAdrs_keyPair {vp : ValidatedParams} (pos : LayerPosition vp) :
    (wotsInstanceAdrs pos).getKeyPairAddress = pos.leaf.val := rfl

/-- Distinct typed WOTS positions have distinct structured base addresses. -/
theorem wotsInstanceAdrs_injective (vp : ValidatedParams) :
    Function.Injective (wotsInstanceAdrs (vp := vp)) := by
  intro a b hadrs
  cases a with
  | mk aLayer aTree aLeaf =>
    cases b with
    | mk bLayer bTree bLeaf =>
      have hlayer : aLayer = bLayer := Fin.ext (by
        simpa [wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
          Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.setTreeAddress,
          Adrs.setLayerAddress, Adrs.zero] using congrArg Adrs.layer hadrs)
      subst bLayer
      have htree : aTree = bTree := Fin.ext (by
        simpa [wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
          Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.setTreeAddress,
          Adrs.setLayerAddress, Adrs.zero] using congrArg Adrs.tree hadrs)
      subst bTree
      have hleaf : aLeaf = bLeaf := Fin.ext (by
        simpa [wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
          Adrs.getKeyPairAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
          Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.zero] using
            congrArg Adrs.getKeyPairAddress hadrs)
      subst bLeaf
      rfl

/-- One structural base address for every reachable WOTS instance. -/
def wotsInstanceAddresses (vp : ValidatedParams) : List Adrs :=
  (allWotsInstances vp).map wotsInstanceAdrs

/-- The WOTS-instance address ledger has the exact all-layer instance count. -/
@[simp]
theorem wotsInstanceAddresses_length (vp : ValidatedParams) :
    (wotsInstanceAddresses vp).length = wotsInstanceCount vp.params := by
  simp [wotsInstanceAddresses]

/-- WOTS-instance base addresses are structurally duplicate-free before concrete encoding. -/
theorem wotsInstanceAddresses_nodup (vp : ValidatedParams) :
    (wotsInstanceAddresses vp).Nodup :=
  (allWotsInstances_nodup vp).map (wotsInstanceAdrs_injective vp)

/-! ## Concrete address encodings -/

variable {p : Params}

/-- Encode a reachable structural-address ledger with the primitive bundle's actual tweak map. -/
def encodeTargets (prims : Primitives p) (addresses : List Adrs) : List prims.AdrsKey :=
  addresses.map prims.adrsToKey

/-- On a structurally duplicate-free reachable ledger, encoded tweaks are duplicate-free exactly
when the concrete encoder is injective on that ledger. -/
theorem encodeTargets_nodup_iff_injOn (prims : Primitives p) (addresses : List Adrs)
    (haddresses : addresses.Nodup) :
    (encodeTargets prims addresses).Nodup ↔
      ∀ a ∈ addresses, ∀ b ∈ addresses,
        prims.adrsToKey a = prims.adrsToKey b → a = b := by
  simpa [encodeTargets] using
    List.nodup_map_iff_inj_on (f := prims.adrsToKey) haddresses

/-- Restricted encoder injectivity is sufficient to preserve a reachable ledger's distinctness. -/
theorem encodeTargets_nodup_of_injOn (prims : Primitives p) (addresses : List Adrs)
    (haddresses : addresses.Nodup)
    (hinj : ∀ a ∈ addresses, ∀ b ∈ addresses,
      prims.adrsToKey a = prims.adrsToKey b → a = b) :
    (encodeTargets prims addresses).Nodup :=
  (encodeTargets_nodup_iff_injOn prims addresses haddresses).2 hinj

end SLHDSA.Security
