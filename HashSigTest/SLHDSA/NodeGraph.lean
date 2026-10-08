/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.NodeGraph

/-!
# The canonical node graph at the FIPS 205 parameter sets

At every FIPS 205 parameter set, over the approved bundle, the node of `slhGraph` at the key of the
first XMSS node of height `1` (layer `0`, tree `0`, index `0`) has exactly two children: the
labels at the keys of the WOTS+ public-key compressions of leaves `0` and `1`. The first step of a
WOTS+ chain has exactly one child, the derivation at the key of its secret-key address, and every
later step has exactly one child, the label of the step before it. A FORS leaf has exactly one
child, the derivation at the key of its secret-key address; a FORS node at height `1` has exactly
two children, the labels of the two leaves below it; and a FORS roots compression has the labels of
the `k` tree roots, in tree order, as its children. At SLH-DSA-SHAKE-128s a WOTS+ public-key
compression has `35 = len` children. No derivation key is a node key, a non-secret-key address has
no derivation key, and the points of the graph are injective at every length.
-/

public section

namespace SLHDSA.NodeGraphTest

open Concrete Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- The position of leaf `leaf` of the reachable XMSS tree `coord`. -/
def leafPos (coord : LayerTreeCoord vp) (leaf : Fin (2 ^ vp.params.hp)) : LayerPosition vp :=
  ⟨coord.layer, coord.tree, leaf⟩

/-- Under the key discipline, the XMSS node at height `1` and index `0` of a reachable tree has
the WOTS+ public keys of leaves `0` and `1` as its children. -/
theorem slhGraph_ch_xmssNode_one (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) :
    (slhGraph core pkSeed).ch
        ⟨core.adrsToKey (xmssNodeAdrs coord.toAdrs 1 0), _,
          xmssNodeAdrs_mem_constructionAddresses coord Nat.one_pos vp.valid.hp_pos
            (by positivity), rfl⟩ =
      [.inr ⟨core.adrsToKey (wotsPkAdrs (wotsInstanceAdrs (leafPos coord ⟨0, by positivity⟩))),
          _, wotsPkAdrs_mem_constructionAddresses _, rfl⟩,
        .inr ⟨core.adrsToKey (wotsPkAdrs (wotsInstanceAdrs
            (leafPos coord ⟨1, Nat.one_lt_two_pow vp.valid.hp_pos.ne'⟩))),
          _, wotsPkAdrs_mem_constructionAddresses _, rfl⟩] := by
  have h₀ : childCell core (.inr (wotsPkAdrs (wotsLeafAdrs coord.toAdrs (2 * 0)))) = _ :=
    childCell_inr core (wotsPkAdrs_mem_constructionAddresses (leafPos coord ⟨0, by positivity⟩))
  have h₁ : childCell core (.inr (wotsPkAdrs (wotsLeafAdrs coord.toAdrs (2 * 0 + 1)))) = _ :=
    childCell_inr core (wotsPkAdrs_mem_constructionAddresses
      (leafPos coord ⟨1, Nat.one_lt_two_pow vp.valid.hp_pos.ne'⟩))
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed
    (nodeKeyOf_of_mem core (xmssNodeAdrs_mem_constructionAddresses coord Nat.one_pos
      vp.valid.hp_pos (by positivity))), childAdrs_xmssNodeAdrs_one,
    List.filterMap_cons_some h₀, List.filterMap_cons_some h₁, List.filterMap_nil]

/-- Under the key discipline, the first step of a WOTS+ chain has the derivation at its secret's
key as its only child. -/
theorem slhGraph_ch_wotsStep_zero (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) (i : Fin vp.params.len) :
    (slhGraph core pkSeed).ch
        ⟨core.adrsToKey ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress 0), _,
          wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i
            (Nat.sub_pos_of_lt (Nat.one_lt_two_pow vp.valid.lgw_pos.ne')), rfl⟩ =
      [.inl (.inl ⟨core.adrsToKey (wotsSkAdrs (wotsInstanceAdrs pos) i.val), _,
        Adrs.isSecretKey_wotsSkAdrs _ _, rfl⟩)] := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed
    (nodeKeyOf_of_mem core (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i
      (Nat.sub_pos_of_lt (Nat.one_lt_two_pow vp.valid.lgw_pos.ne')))),
    childAdrs_wotsChainAdrs_setHashAddress_zero,
    List.filterMap_cons_some (childCell_inl core (Adrs.isSecretKey_wotsSkAdrs _ _)),
    List.filterMap_nil]

/-- Under the key discipline, a WOTS+ public-key compression has `len` children. -/
theorem length_slhGraph_ch_wotsPk (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) :
    ((slhGraph core pkSeed).ch ⟨core.adrsToKey (wotsPkAdrs (wotsInstanceAdrs pos)), _,
      wotsPkAdrs_mem_constructionAddresses pos, rfl⟩).length = vp.params.len := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed
    (nodeKeyOf_of_mem core (wotsPkAdrs_mem_constructionAddresses pos)),
    ← List.length_map (f := some),
    map_some_filterMap_childCell core (wotsPkAdrs_mem_constructionAddresses pos),
    List.length_map, childAdrs_wotsPkAdrs, List.length_map, List.length_range]

/-- Under the key discipline, a later step of a WOTS+ chain has the previous step as its only
child. -/
theorem slhGraph_ch_wotsStep_succ (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) (i : Fin vp.params.len) {t : ℕ} (ht : t + 1 < vp.params.w - 1) :
    (slhGraph core pkSeed).ch
        ⟨core.adrsToKey ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress (t + 1)), _,
          wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i ht, rfl⟩ =
      [.inr ⟨core.adrsToKey ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress t), _,
        wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (Nat.lt_of_succ_lt ht),
        rfl⟩] := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed
    (nodeKeyOf_of_mem core (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i ht)),
    childAdrs_wotsChainAdrs_setHashAddress_succ,
    List.filterMap_cons_some (childCell_inr core
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (Nat.lt_of_succ_lt ht))),
    List.filterMap_nil]

/-- Under the key discipline, a FORS leaf has the derivation at its secret's key as its only
child. -/
theorem slhGraph_ch_forsLeaf (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : BottomPosition vp) (tree : Fin vp.params.k) {i : ℕ}
    (hi : i / 2 ^ vp.params.a = tree.val) :
    (slhGraph core pkSeed).ch
        ⟨core.adrsToKey (forsNodeAdrs pos.forsAdrs 0 i), _,
          forsLeafAdrs_mem_constructionAddresses pos tree hi, rfl⟩ =
      [.inl (.inl ⟨core.adrsToKey (forsSkAdrs pos.forsAdrs i), _,
        Adrs.isSecretKey_forsSkAdrs _ _, rfl⟩)] := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed
    (nodeKeyOf_of_mem core (forsLeafAdrs_mem_constructionAddresses pos tree hi)),
    childAdrs_forsNodeAdrs_zero,
    List.filterMap_cons_some (childCell_inl core (Adrs.isSecretKey_forsSkAdrs _ _)),
    List.filterMap_nil]

/-- An index whose half is `i` lies, at height `0`, in the FORS tree that index `i` lies in at
height `1`. -/
theorem div_two_pow_eq_of_div_two_eq {a i j : ℕ} (ha : 0 < a) (hj : j / 2 = i) :
    j / 2 ^ a = i / 2 ^ (a - 1) := by
  rw [← hj, Nat.div_div_eq_div_mul, ← pow_succ', Nat.sub_add_cancel ha]

/-- Under the key discipline, a FORS node at height `1` has the two leaves below it as its
children. -/
theorem slhGraph_ch_forsNode_one (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : BottomPosition vp) (tree : Fin vp.params.k) {i : ℕ}
    (hi : i / 2 ^ (vp.params.a - 1) = tree.val) :
    (slhGraph core pkSeed).ch
        ⟨core.adrsToKey (forsNodeAdrs pos.forsAdrs 1 i), _,
          forsTreeAdrs_mem_constructionAddresses pos tree Nat.one_pos vp.valid.a_pos hi, rfl⟩ =
      [.inr ⟨core.adrsToKey (forsNodeAdrs pos.forsAdrs 0 (2 * i)), _,
          forsLeafAdrs_mem_constructionAddresses pos tree
            ((div_two_pow_eq_of_div_two_eq vp.valid.a_pos (by omega)).trans hi), rfl⟩,
        .inr ⟨core.adrsToKey (forsNodeAdrs pos.forsAdrs 0 (2 * i + 1)), _,
          forsLeafAdrs_mem_constructionAddresses pos tree
            ((div_two_pow_eq_of_div_two_eq vp.valid.a_pos (by omega)).trans hi), rfl⟩] := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed
    (nodeKeyOf_of_mem core
      (forsTreeAdrs_mem_constructionAddresses pos tree Nat.one_pos vp.valid.a_pos hi)),
    childAdrs_forsNodeAdrs vp Nat.one_pos, Nat.sub_self,
    List.filterMap_cons_some (childCell_inr core (forsLeafAdrs_mem_constructionAddresses pos tree
      ((div_two_pow_eq_of_div_two_eq vp.valid.a_pos (by omega)).trans hi))),
    List.filterMap_cons_some (childCell_inr core (forsLeafAdrs_mem_constructionAddresses pos tree
      ((div_two_pow_eq_of_div_two_eq vp.valid.a_pos (by omega)).trans hi))),
    List.filterMap_nil]

/-- Under the key discipline, a FORS roots compression has the `k` tree roots, in tree order, as
its children. -/
theorem slhGraph_ch_forsPk (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : BottomPosition vp) :
    (slhGraph core pkSeed).ch
        ⟨core.adrsToKey (forsPkAdrs pos.forsAdrs), _,
          forsRootAdrs_mem_constructionAddresses pos, rfl⟩ =
      (List.finRange vp.params.k).map fun tree =>
        .inr ⟨core.adrsToKey (forsNodeAdrs pos.forsAdrs vp.params.a tree.val), _,
          forsTreeAdrs_mem_constructionAddresses pos tree vp.valid.a_pos le_rfl (by simp),
          rfl⟩ := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed
    (nodeKeyOf_of_mem core (forsRootAdrs_mem_constructionAddresses pos)),
    childAdrs_forsPkAdrs, ← List.map_coe_finRange_eq_range, List.map_map, List.filterMap_map]
  exact List.filterMap_eq_map_iff_forall_eq_some.2 fun tree _ => childCell_inr core
    (forsTreeAdrs_mem_constructionAddresses pos tree vp.valid.a_pos le_rfl (by simp))

/-- At every FIPS 205 parameter set, the XMSS node at height `1` and index `0` of tree `0` at
layer `0` has the WOTS+ public keys of leaves `0` and `1` as its children. -/
example (ps : FipsParameterSet) (pkSeed : (approvedPrimitives ps).core.PkSeed) :=
  slhGraph_ch_xmssNode_one (vp := ps.validatedParams) _ (keyDiscipline_approvedPrimitives ps)
    pkSeed ⟨⟨0, ps.validatedParams.valid.d_pos⟩, ⟨0, by positivity⟩⟩

/-- At every FIPS 205 parameter set, the first step of a WOTS+ chain has one child. -/
example (ps : FipsParameterSet) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (pos : LayerPosition ps.validatedParams) (i : Fin ps.validatedParams.params.len) :=
  slhGraph_ch_wotsStep_zero (vp := ps.validatedParams) _ (keyDiscipline_approvedPrimitives ps)
    pkSeed pos i

/-- At every FIPS 205 parameter set, a later step of a WOTS+ chain has one child. -/
example (ps : FipsParameterSet) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (pos : LayerPosition ps.validatedParams) (i : Fin ps.validatedParams.params.len) {t : ℕ}
    (ht : t + 1 < ps.validatedParams.params.w - 1) :=
  slhGraph_ch_wotsStep_succ (vp := ps.validatedParams) _ (keyDiscipline_approvedPrimitives ps)
    pkSeed pos i ht

/-- At every FIPS 205 parameter set, a FORS leaf has one child. -/
example (ps : FipsParameterSet) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (pos : BottomPosition ps.validatedParams) (tree : Fin ps.validatedParams.params.k) {i : ℕ}
    (hi : i / 2 ^ ps.validatedParams.params.a = tree.val) :=
  slhGraph_ch_forsLeaf (vp := ps.validatedParams) _ (keyDiscipline_approvedPrimitives ps)
    pkSeed pos tree hi

/-- At every FIPS 205 parameter set, a FORS node at height `1` has its two leaves as children. -/
example (ps : FipsParameterSet) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (pos : BottomPosition ps.validatedParams) (tree : Fin ps.validatedParams.params.k) {i : ℕ}
    (hi : i / 2 ^ (ps.validatedParams.params.a - 1) = tree.val) :=
  slhGraph_ch_forsNode_one (vp := ps.validatedParams) _ (keyDiscipline_approvedPrimitives ps)
    pkSeed pos tree hi

/-- At every FIPS 205 parameter set, a FORS roots compression has the `k` tree roots as
children. -/
example (ps : FipsParameterSet) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (pos : BottomPosition ps.validatedParams) :=
  slhGraph_ch_forsPk (vp := ps.validatedParams) _ (keyDiscipline_approvedPrimitives ps) pkSeed pos

/-- A non-secret-key address has no derivation key. -/
example {a : Adrs} (h : ¬ a.IsSecretKey) : prfKeyOf core a = none :=
  Option.eq_none_iff_forall_ne_some.2 fun _ hk => h ((prfKeyOf_eq_some_iff core).1 hk).1

/-- At SLH-DSA-SHAKE-128s a WOTS+ public-key compression has `35` children. -/
example (pkSeed : (approvedPrimitives .SLHDSA_SHAKE_128s).core.PkSeed)
    (pos : LayerPosition FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) :
    ((slhGraph (vp := FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) _ pkSeed).ch
      ⟨(approvedPrimitives .SLHDSA_SHAKE_128s).core.adrsToKey (wotsPkAdrs (wotsInstanceAdrs pos)),
        _, wotsPkAdrs_mem_constructionAddresses pos, rfl⟩).length = 35 :=
  (length_slhGraph_ch_wotsPk _ (keyDiscipline_approvedPrimitives _) pkSeed pos).trans (by decide)

/-- At every FIPS 205 parameter set no derivation key is a node key. -/
example (ps : FipsParameterSet) (k : PrfKey (vp := ps.validatedParams) (approvedPrimitives ps).core)
    (κ : NodeKey (vp := ps.validatedParams) (approvedPrimitives ps).core) : k.1 ≠ κ.1 :=
  prfKey_val_ne_nodeKey_val _ (keySeparated_approvedPrimitives ps) k κ

/-- At every FIPS 205 parameter set the points of the graph are injective at every length. -/
example (ps : FipsParameterSet) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    {κ κ' : NodeKey (vp := ps.validatedParams) (approvedPrimitives ps).core}
    {vs vs' : List (approvedPrimitives ps).core.Y}
    (h : (slhGraph _ pkSeed).pt κ vs = (slhGraph _ pkSeed).pt κ' vs') : κ = κ' ∧ vs = vs' :=
  slhGraph_pt_inj _ pkSeed h

end SLHDSA.NodeGraphTest
