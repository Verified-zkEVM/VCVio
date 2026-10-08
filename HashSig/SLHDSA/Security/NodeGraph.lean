/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ComponentTraces
public import HashSig.SLHDSA.Security.HonestEntryUnique
public import HashSig.SLHDSA.Security.SeedCoupling
public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel
import HashSig.SLHDSA.Security.AddressKeys

/-!
# The canonical node graph of SLH-DSA

Every tweakable-hash evaluation of honest SLH-DSA is a node of one fixed graph: its address
determines its children, and its value is the hash, at the public seed and the node's oracle key,
of its children's values. `slhGraph core pkSeed` is that graph as a
`CanonicalGraph (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y`, the input of the
canonical relabelling of `VCVio.OracleComp.QueryTracking.RandomOracle.Relabel`.

* **Nodes** are oracle keys, not addresses: `NodeKey core` is the set of keys `core.adrsToKey a`
  of the addresses `a` of the union ledger `constructionAddresses vp`, and `nodeAdrs core κ` is a
  ledger address with key `κ`.
* **Children** are read off the address type (`childAdrs`): `inl` a secret-key address, whose
  cell is the derivation at its key (`PrfKey core`), and `inr` the address of a child node, whose
  cell is that node's label.

  | node (type) | children |
  |---|---|
  | `WOTS_HASH` step at hash address `t` (0) | the secret if `t = 0`, else the step at `t - 1` |
  | `WOTS_PK` compression (1) | the `len` chain steps at hash address `w - 2` |
  | `TREE` node at height `z = 1` (2) | the WOTS+ public keys of leaves `2i`, `2i + 1` |
  | `TREE` node at height `z ≥ 2` (2) | the nodes `2i`, `2i + 1` at height `z - 1` |
  | `FORS_TREE` node at height `z` (3) | the secret at `z = 0`, else the nodes at `z - 1` |
  | `FORS_ROOTS` compression (4) | the `k` tree roots, at height `a` |

* **Points**: the point of `κ` at values `vs` is `T(PK.seed, κ, vs)`, the `thash` query at the
  public seed `pkSeed` and the key `κ`. The graph depends on the public seed only through its
  points: the children of a node do not depend on the public seed (`slhGraph_ch`).

Three facts make the graph the honest one.

* *Ledger closure* (`isSecretKey_of_inl_mem_childAdrs`,
  `mem_constructionAddresses_of_inr_mem_childAdrs`): a secret child is a secret-key address and a
  node child of a ledger address is a ledger address, so every structural child has a cell
  (`isSome_childCell_of_mem_childAdrs`) and the children of a node are exactly the cells of the
  structural children of its address (`map_some_slhGraph_ch`). This holds for every encoding.
* *Children at a key* (`slhGraph_ch_of_nodeKeyOf_eq_some`): where the encoding is injective on
  the in-range addresses (`CorePrimitives.KeyInjective`), under the FIPS 205 address widths
  (`CanonicalAddressBounds`), the children of the node at the key of a ledger address `a` are the
  cells of the structural children of `a` itself.
* *Separation* (`prfKey_val_ne_nodeKey_val`, `secretEncoding_enc_ne_slhGraph_pt`): under key
  separation (`CorePrimitives.KeySeparated`) no derivation key is a node key, so no encoded
  derivation is a node point.

The points are injective at every input length (`slhGraph_pt_inj`), with no hypothesis on the
encoding, so only node `κ` has points at key `κ`. The node keys `slhNodeKeys core pkSeed` place a
public query at node `κ` exactly when it is a `thash` query at `pkSeed` and `κ`, of any input
(`slhNodeKeys_node_thash_eq_some_iff`), and at no node otherwise
(`slhNodeKeys_node_eq_none_of_forall_ne_thash`).

`slhGraph` is exposed: the range of the public oracle at a node point is `core.Y` by `rfl`, and a
program querying a node point makes the `thash` query itself, with no cast. The other
definitions are reached through their equations.

## References

- NIST FIPS 205, §4.2 (ADRS and its type words), Algorithms 5--8 (WOTS+), 9--11 (XMSS), 14--17
  (FORS)
-/

public section

namespace SLHDSA.Security

/-! ## Structural children -/

section Children

variable (vp : ValidatedParams)

/-- The children of a tweakable-hash address, read off its type and fields: `inl` a secret-key
address, `inr` the address of a child node. A `WOTS_HASH` address at hash address `t` has the
secret at `t = 0` and the step at `t - 1` otherwise; a `WOTS_PK` address has the `len` chain steps
at hash address `w - 2`; a `TREE` address at height `z` and index `i` has the WOTS+ public keys of
leaves `2i`, `2i + 1` at `z = 1` and the nodes `2i`, `2i + 1` at height `z - 1` otherwise; a
`FORS_TREE` address has the secret at height `0` and the two nodes below otherwise; a `FORS_ROOTS`
address has the `k` tree roots, at height `a`. Other addresses have no children. -/
def childAdrs (a : Adrs) : List (Adrs ⊕ Adrs) :=
  match a.type with
  | 0 => if a.word3 = 0 then [.inl (wotsSkAdrs a a.word2)]
      else [.inr (a.setHashAddress (a.word3 - 1))]
  | 1 => (List.range vp.params.len).map fun i =>
      .inr ((wotsChainAdrs a i).setHashAddress (vp.params.w - 2))
  | 2 => if a.word2 = 1 then
        [.inr (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3))),
          .inr (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3 + 1)))]
      else [.inr (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3)),
        .inr (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1))]
  | 3 => if a.word2 = 0 then [.inl (forsSkAdrs a a.word3)]
      else [.inr (forsNodeAdrs a (a.word2 - 1) (2 * a.word3)),
        .inr (forsNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1))]
  | 4 => (List.range vp.params.k).map fun i => .inr (forsNodeAdrs a vp.params.a i)
  | _ => []

/-- The first WOTS+ chain step has the chain's secret as its child. -/
theorem childAdrs_wotsChainAdrs_setHashAddress_zero (b : Adrs) (i : ℕ) :
    childAdrs vp ((wotsChainAdrs b i).setHashAddress 0) = [.inl (wotsSkAdrs b i)] := by
  rfl

/-- A later WOTS+ chain step has the previous step as its child. -/
theorem childAdrs_wotsChainAdrs_setHashAddress_succ (b : Adrs) (i t : ℕ) :
    childAdrs vp ((wotsChainAdrs b i).setHashAddress (t + 1)) =
      [.inr ((wotsChainAdrs b i).setHashAddress t)] := by
  rfl

/-- A WOTS+ public-key compression has the `len` chain steps at hash address `w - 2` as its
children. -/
theorem childAdrs_wotsPkAdrs (b : Adrs) :
    childAdrs vp (wotsPkAdrs b) = (List.range vp.params.len).map fun i =>
      .inr ((wotsChainAdrs b i).setHashAddress (vp.params.w - 2)) := by
  rfl

/-- An XMSS node at height `1` has the WOTS+ public keys of its two leaves as its children. -/
theorem childAdrs_xmssNodeAdrs_one (b : Adrs) (i : ℕ) :
    childAdrs vp (xmssNodeAdrs b 1 i) =
      [.inr (wotsPkAdrs (wotsLeafAdrs b (2 * i))),
        .inr (wotsPkAdrs (wotsLeafAdrs b (2 * i + 1)))] := by
  rfl

/-- An XMSS node above height `1` has the two nodes below it as its children. -/
theorem childAdrs_xmssNodeAdrs {h : ℕ} (hh : 1 < h) (b : Adrs) (i : ℕ) :
    childAdrs vp (xmssNodeAdrs b h i) =
      [.inr (xmssNodeAdrs b (h - 1) (2 * i)), .inr (xmssNodeAdrs b (h - 1) (2 * i + 1))] := by
  simp only [childAdrs, xmssNodeAdrs_eq, hh.ne', ↓reduceIte]

/-- A FORS leaf has its secret as its child. -/
theorem childAdrs_forsNodeAdrs_zero (b : Adrs) (t : ℕ) :
    childAdrs vp (forsNodeAdrs b 0 t) = [.inl (forsSkAdrs b t)] := by
  rfl

/-- A FORS node above height `0` has the two nodes below it as its children. -/
theorem childAdrs_forsNodeAdrs {h : ℕ} (hh : 0 < h) (b : Adrs) (i : ℕ) :
    childAdrs vp (forsNodeAdrs b h i) =
      [.inr (forsNodeAdrs b (h - 1) (2 * i)), .inr (forsNodeAdrs b (h - 1) (2 * i + 1))] := by
  simp only [childAdrs, forsNodeAdrs_eq, hh.ne', ↓reduceIte]

/-- A FORS roots compression has the `k` tree roots as its children. -/
theorem childAdrs_forsPkAdrs (b : Adrs) :
    childAdrs vp (forsPkAdrs b) =
      (List.range vp.params.k).map fun i => .inr (forsNodeAdrs b vp.params.a i) := by
  rfl

variable {vp}

/-- Every secret child is a secret-key address. -/
theorem isSecretKey_of_inl_mem_childAdrs {a b : Adrs} (hb : .inl b ∈ childAdrs vp a) :
    b.IsSecretKey := by
  unfold childAdrs at hb
  split at hb <;> (try split_ifs at hb) <;>
    simp only [List.mem_cons, List.mem_map, List.mem_range, Sum.inl.injEq, reduceCtorEq,
      List.not_mem_nil, or_false, or_self, and_false, exists_const] at hb
  · exact hb ▸ Adrs.isSecretKey_wotsSkAdrs _ _
  · exact hb ▸ Adrs.isSecretKey_forsSkAdrs _ _

/-- `2 (T 2ⁿ + j) + e = T 2ⁿ⁺¹ + (2 j + e)`: the children of node `j` of tree `T` at one height,
indexed globally, are nodes `2 j + e` of tree `T` one height below. -/
private theorem two_mul_index (T j e n : ℕ) :
    2 * (T * 2 ^ n + j) + e = T * 2 ^ (n + 1) + (2 * j + e) := by
  rw [pow_succ]
  ring

/-- **Ledger closure.** Every node child of an address of the union ledger is in the union
ledger. -/
theorem mem_constructionAddresses_of_inr_mem_childAdrs {a b : Adrs}
    (ha : a ∈ constructionAddresses vp) (hb : .inr b ∈ childAdrs vp a) :
    b ∈ constructionAddresses vp := by
  have hw : 2 ≤ vp.params.w := Nat.one_lt_two_pow vp.valid.lgw_pos.ne'
  rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
  · -- FORS leaf: the only child is the secret
    simp only [forsLeafAddresses, List.mem_map] at h
    obtain ⟨_, -, rfl⟩ := h
    simp [childAdrs_forsNodeAdrs_zero] at hb
  · -- FORS internal node
    simp only [forsTreeAddresses, List.mem_map] at h
    obtain ⟨⟨⟨pos, tree⟩, z, j⟩, hmem, rfl⟩ := h
    obtain ⟨hz, hza, hj⟩ := mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2
    rw [childAdrs_forsNodeAdrs vp hz] at hb
    have hsub : vp.params.a - (z - 1) = vp.params.a - z + 1 := by omega
    have hchild : ∀ e, e ≤ 1 → forsNodeAdrs pos.forsAdrs (z - 1)
        (2 * (tree.val * 2 ^ (vp.params.a - z) + j) + e) ∈ constructionAddresses vp := by
      intro e he
      have hlt : 2 * j + e < 2 ^ (vp.params.a - (z - 1)) := by rw [hsub, pow_succ]; omega
      rw [two_mul_index, ← hsub]
      rcases (by omega : z = 1 ∨ 1 < z) with rfl | hz1
      · rw [mem_constructionAddresses_iff]
        refine Or.inl ?_
        simpa [Params.t] using
          mem_forsLeafAddresses vp pos tree ⟨2 * j + e, by simpa [Params.t] using hlt⟩
      · exact forsTreeAdrs_mem_constructionAddresses pos tree (by omega) (by omega)
          (by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
            zero_add])
    simp only [List.mem_cons, Sum.inr.injEq, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · simpa using hchild 0 (Nat.zero_le _)
    · exact hchild 1 le_rfl
  · -- FORS roots: the tree roots at height `a`
    simp only [forsRootAddresses, List.mem_map] at h
    obtain ⟨pos, -, rfl⟩ := h
    simp only [childAdrs_forsPkAdrs, List.mem_map, List.mem_range, Sum.inr.injEq] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    refine forsTreeAdrs_mem_constructionAddresses pos ⟨i, hi⟩ vp.valid.a_pos le_rfl ?_
    simp
  · -- WOTS+ chain step: the previous step
    simp only [wotsStepAddresses, List.mem_map] at h
    obtain ⟨⟨⟨pos, chain⟩, ⟨t, ht⟩⟩, -, rfl⟩ := h
    simp only [wotsStepAdrs] at hb
    rcases t with _ | t
    · simp [childAdrs_wotsChainAdrs_setHashAddress_zero] at hb
    · simp only [childAdrs_wotsChainAdrs_setHashAddress_succ, List.mem_singleton,
        Sum.inr.injEq] at hb
      exact hb ▸ wotsChainAdrs_setHashAddress_mem_constructionAddresses pos chain (by omega)
  · -- WOTS+ public-key compression: the chain tops
    simp only [wotsPkAddresses, List.mem_map] at h
    obtain ⟨pos, -, rfl⟩ := h
    simp only [childAdrs_wotsPkAdrs, List.mem_map, List.mem_range, Sum.inr.injEq] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact wotsChainAdrs_setHashAddress_mem_constructionAddresses pos ⟨i, hi⟩ (by omega)
  · -- XMSS internal node
    simp only [xmssNodeAddresses, List.mem_map] at h
    obtain ⟨⟨coord, z, j⟩, hmem, rfl⟩ := h
    obtain ⟨hz, hzh, hj⟩ := mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2
    rcases (by omega : z = 1 ∨ 1 < z) with rfl | hz1
    · rw [childAdrs_xmssNodeAdrs_one] at hb
      have hleaf : ∀ e, e ≤ 1 →
          wotsPkAdrs (wotsLeafAdrs coord.toAdrs (2 * j + e)) ∈ constructionAddresses vp := by
        intro e he
        have hlt : 2 * j + e < 2 ^ vp.params.hp := by
          have : vp.params.hp = vp.params.hp - 1 + 1 := by omega
          rw [this, pow_succ]
          omega
        exact wotsPkAdrs_mem_constructionAddresses ⟨coord.layer, coord.tree, ⟨2 * j + e, hlt⟩⟩
      simp only [List.mem_cons, Sum.inr.injEq, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hleaf 0 (Nat.zero_le _)
      · exact hleaf 1 le_rfl
    · rw [childAdrs_xmssNodeAdrs vp hz1] at hb
      have hsub : vp.params.hp - (z - 1) = vp.params.hp - z + 1 := by omega
      have hnode : ∀ e, e ≤ 1 →
          xmssNodeAdrs coord.toAdrs (z - 1) (2 * j + e) ∈ constructionAddresses vp := by
        intro e he
        exact xmssNodeAdrs_mem_constructionAddresses coord (by omega) (by omega)
          (by rw [hsub, pow_succ]; omega)
      simp only [List.mem_cons, Sum.inr.injEq, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hnode 0 (Nat.zero_le _)
      · exact hnode 1 le_rfl

end Children

/-! ## Node keys and cells -/

section Keys

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- The oracle keys of the addresses of the union ledger: the nodes of the SLH-DSA graph. -/
abbrev NodeKey : Type :=
  {κ : core.AdrsKey // ∃ a ∈ constructionAddresses vp, core.adrsToKey a = κ}

/-- A ledger address with key `κ`. Under key injectivity on the in-range addresses it is the only
one (`nodeAdrs_eq_of_adrsToKey_eq`). -/
noncomputable def nodeAdrs (κ : NodeKey core) : Adrs := Classical.choose κ.2

/-- The address of a node is in the union ledger. -/
theorem nodeAdrs_mem_constructionAddresses (κ : NodeKey core) :
    nodeAdrs core κ ∈ constructionAddresses vp :=
  (Classical.choose_spec κ.2).1

/-- The address of a node has the node's key. -/
@[simp]
theorem adrsToKey_nodeAdrs (κ : NodeKey core) : core.adrsToKey (nodeAdrs core κ) = κ.1 :=
  (Classical.choose_spec κ.2).2

/-- Under key injectivity on the in-range addresses and the FIPS 205 address widths, the address
of a node is every ledger address with its key. -/
theorem nodeAdrs_eq_of_adrsToKey_eq (hinj : core.KeyInjective vp)
    (hb : CanonicalAddressBounds vp.params) {κ : NodeKey core} {a : Adrs}
    (ha : a ∈ constructionAddresses vp) (hκ : core.adrsToKey a = κ.1) : nodeAdrs core κ = a :=
  hinj
    (addressFacts_of_mem_constructionAddresses hb (nodeAdrs_mem_constructionAddresses core κ))
    (addressFacts_of_mem_constructionAddresses hb ha) (by rw [adrsToKey_nodeAdrs, hκ])

/-- The derivation key of a secret-key address, and `none` at every other address. -/
def prfKeyOf (a : Adrs) : Option (PrfKey core) :=
  if h : a.IsSecretKey then some ⟨core.adrsToKey a, a, h, rfl⟩ else none

/-- The node key of a ledger address, and `none` at every other address. -/
def nodeKeyOf (a : Adrs) : Option (NodeKey core) :=
  if h : a ∈ constructionAddresses vp then some ⟨core.adrsToKey a, a, h, rfl⟩ else none

/-- The derivation key of a secret-key address is its oracle key. -/
theorem prfKeyOf_of_isSecretKey {a : Adrs} (h : a.IsSecretKey) :
    prfKeyOf core a = some ⟨core.adrsToKey a, a, h, rfl⟩ := by
  simp [prfKeyOf, h]

/-- The node key of a ledger address is its oracle key. -/
theorem nodeKeyOf_of_mem {a : Adrs} (h : a ∈ constructionAddresses vp) :
    nodeKeyOf core a = some ⟨core.adrsToKey a, a, h, rfl⟩ := by
  simp [nodeKeyOf, h]

/-- An address has derivation key `k` exactly when it is a secret-key address with key `k`. -/
theorem prfKeyOf_eq_some_iff {a : Adrs} {k : PrfKey core} :
    prfKeyOf core a = some k ↔ a.IsSecretKey ∧ core.adrsToKey a = k.1 := by
  unfold prfKeyOf
  split_ifs with h
  · simp only [Option.some.injEq, h, true_and]
    exact ⟨fun h' => by rw [← h'], fun h' => Subtype.ext h'⟩
  · simp [h]

/-- An address has node key `κ` exactly when it is a ledger address with key `κ`. -/
theorem nodeKeyOf_eq_some_iff {a : Adrs} {κ : NodeKey core} :
    nodeKeyOf core a = some κ ↔ a ∈ constructionAddresses vp ∧ core.adrsToKey a = κ.1 := by
  unfold nodeKeyOf
  split_ifs with h
  · simp only [Option.some.injEq, h, true_and]
    exact ⟨fun h' => by rw [← h'], fun h' => Subtype.ext h'⟩
  · simp [h]

/-- The cell of a structural child: the derivation at the key of a secret-key address, or the
label of the node at the key of a ledger address. -/
def childCell : Adrs ⊕ Adrs → Option (DeriveQuery core ⊕ NodeKey core)
  | .inl a => (prfKeyOf core a).map fun k => .inl (.inl k)
  | .inr a => (nodeKeyOf core a).map .inr

/-- The cell of a secret child is the derivation at its key. -/
theorem childCell_inl {a : Adrs} (h : a.IsSecretKey) :
    childCell core (.inl a) = some (.inl (.inl ⟨core.adrsToKey a, a, h, rfl⟩)) := by
  simp [childCell, prfKeyOf_of_isSecretKey core h]

/-- The cell of a node child in the ledger is the label at its key. -/
theorem childCell_inr {a : Adrs} (h : a ∈ constructionAddresses vp) :
    childCell core (.inr a) = some (.inr ⟨core.adrsToKey a, a, h, rfl⟩) := by
  simp [childCell, nodeKeyOf_of_mem core h]

/-- Every structural child of a ledger address has a cell. -/
theorem isSome_childCell_of_mem_childAdrs {a : Adrs} (ha : a ∈ constructionAddresses vp)
    {c : Adrs ⊕ Adrs} (hc : c ∈ childAdrs vp a) : (childCell core c).isSome := by
  rcases c with b | b
  · simp [childCell_inl core (isSecretKey_of_inl_mem_childAdrs hc)]
  · simp [childCell_inr core (mem_constructionAddresses_of_inr_mem_childAdrs ha hc)]

/-- Keeping the cells of the structural children of a ledger address drops none of them. -/
theorem map_some_filterMap_childCell {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    ((childAdrs vp a).filterMap (childCell core)).map some =
      (childAdrs vp a).map (childCell core) := by
  rw [List.map_filterMap_some_eq_filter_map_isSome, List.filter_eq_self]
  simp only [List.mem_map]
  rintro _ ⟨c, hc, rfl⟩
  exact isSome_childCell_of_mem_childAdrs core ha hc

end Keys

/-! ## The graph -/

section Graph

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- **The canonical graph of SLH-DSA at public seed `pkSeed`.** Its nodes are the oracle keys of
the union ledger; the children of a node are the cells of the structural children of its
address; the point of node `κ` at values `vs` is the tweakable hash `T(PK.seed, κ, vs)`. -/
@[expose] noncomputable def slhGraph (pkSeed : core.PkSeed) :
    CanonicalGraph (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y where
  ch κ := (childAdrs vp (nodeAdrs core κ)).filterMap (childCell core)
  pt κ vs := .inl (.thash pkSeed κ.1 vs)
  range_eq _ _ := rfl
  pt_inj {_ _ _ _} _ _ h := by
    simp only [Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at h
    exact ⟨Subtype.ext h.1, h.2⟩

/-- The children of a node, at every public seed. -/
theorem slhGraph_ch (pkSeed : core.PkSeed) (κ : NodeKey core) :
    (slhGraph core pkSeed).ch κ = (childAdrs vp (nodeAdrs core κ)).filterMap (childCell core) :=
  rfl

/-- The point of a node is the tweakable hash at the public seed and the node's key. -/
@[simp]
theorem slhGraph_pt (pkSeed : core.PkSeed) (κ : NodeKey core) (vs : List core.Y) :
    (slhGraph core pkSeed).pt κ vs = .inl (.thash pkSeed κ.1 vs) := rfl

/-- **Point injectivity at every length.** Two points of the graph are equal only at one node and
one list of values, of whatever lengths. -/
theorem slhGraph_pt_inj (pkSeed : core.PkSeed) {κ κ' : NodeKey core} {vs vs' : List core.Y}
    (h : (slhGraph core pkSeed).pt κ vs = (slhGraph core pkSeed).pt κ' vs') :
    κ = κ' ∧ vs = vs' := by
  simp only [slhGraph_pt, Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at h
  exact ⟨Subtype.ext h.1, h.2⟩

/-- The graphs at distinct public seeds have no point in common. -/
theorem slhGraph_pt_ne_of_ne {pkSeed pkSeed' : core.PkSeed} (h : pkSeed ≠ pkSeed')
    (κ κ' : NodeKey core) (vs vs' : List core.Y) :
    (slhGraph core pkSeed).pt κ vs ≠ (slhGraph core pkSeed').pt κ' vs' := by
  simp only [slhGraph_pt, ne_eq, Sum.inl.injEq, PublicHashQuery.thash.injEq, not_and]
  exact fun h' => absurd h' h

/-- The children of a node are exactly the cells of the structural children of its address: no
structural child is dropped. -/
theorem map_some_slhGraph_ch (pkSeed : core.PkSeed) (κ : NodeKey core) :
    ((slhGraph core pkSeed).ch κ).map some =
      (childAdrs vp (nodeAdrs core κ)).map (childCell core) :=
  map_some_filterMap_childCell core (nodeAdrs_mem_constructionAddresses core κ)

/-- A node has as many children as its address has structural children. -/
theorem length_slhGraph_ch (pkSeed : core.PkSeed) (κ : NodeKey core) :
    ((slhGraph core pkSeed).ch κ).length = (childAdrs vp (nodeAdrs core κ)).length := by
  simpa using congrArg List.length (map_some_slhGraph_ch core pkSeed κ)

/-- **Children at a key.** Under key injectivity on the in-range addresses and the FIPS 205
address widths, the children of the node at the key of a ledger address `a` are the cells of the
structural children of `a`. -/
theorem slhGraph_ch_of_nodeKeyOf_eq_some (hinj : core.KeyInjective vp)
    (hb : CanonicalAddressBounds vp.params) (pkSeed : core.PkSeed) {a : Adrs}
    {κ : NodeKey core} (h : nodeKeyOf core a = some κ) :
    (slhGraph core pkSeed).ch κ = (childAdrs vp a).filterMap (childCell core) := by
  obtain ⟨ha, hκ⟩ := (nodeKeyOf_eq_some_iff core).1 h
  rw [slhGraph_ch, nodeAdrs_eq_of_adrsToKey_eq core hinj hb ha hκ]

/-- The children at a key, under the key discipline. -/
theorem _root_.SLHDSA.CorePrimitives.KeyDiscipline.slhGraph_ch_of_nodeKeyOf_eq_some
    {core : CorePrimitives vp.params} (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    {a : Adrs} {κ : NodeKey core} (h : nodeKeyOf core a = some κ) :
    (slhGraph core pkSeed).ch κ = (childAdrs vp a).filterMap (childCell core) :=
  Security.slhGraph_ch_of_nodeKeyOf_eq_some core hd.keyInjective hd.canonicalAddressBounds
    pkSeed h

end Graph

/-! ## The node of a public point -/

section NodeKeys

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

open Classical in
/-- **The node keys of the graph at public seed `pkSeed`.** A tweakable-hash query at the public
seed `pkSeed` and a node's key is at that node, whatever its inputs; no other public query is at a
node. -/
noncomputable def slhNodeKeys (pkSeed : core.PkSeed) : (slhGraph core pkSeed).NodeKeys where
  node
    | .inl (.thash s κ _) =>
        if h : s = pkSeed ∧ ∃ a ∈ constructionAddresses vp, core.adrsToKey a = κ then
          some ⟨κ, h.2⟩ else none
    | _ => none
  node_pt {k} _ _ := dite_eq_left ⟨rfl, k.2⟩
  range_eq {t} _ h := by
    rcases t with (_ | _) | _
    · rfl
    all_goals exact absurd h (by simp)

/-- A tweakable-hash query is at node `k` exactly when it is at the public seed and `k`'s key. -/
theorem slhNodeKeys_node_thash_eq_some_iff {pkSeed s : core.PkSeed} {κ : core.AdrsKey}
    {xs : List core.Y} {k : NodeKey core} :
    (slhNodeKeys core pkSeed).node (.inl (.thash s κ xs)) = some k ↔ s = pkSeed ∧ κ = k.1 := by
  dsimp only [slhNodeKeys]
  split_ifs with h
  · rw [Option.some.injEq]
    exact ⟨fun h' => ⟨h.1, by rw [← h']⟩, fun h' => Subtype.ext h'.2⟩
  · simp only [false_iff, not_and]
    rintro rfl rfl
    exact h ⟨rfl, k.2⟩

/-- A public query other than a tweakable hash is at no node. -/
theorem slhNodeKeys_node_eq_none_of_forall_ne_thash {pkSeed : core.PkSeed}
    {t : PublicHashQuery core.PkSeed core.AdrsKey core.Y ⊕ PrfMsgQuery core.SkPrf core.Y}
    (ht : ∀ s κ xs, t ≠ .inl (.thash s κ xs)) : (slhNodeKeys core pkSeed).node t = none := by
  rcases t with (⟨s, κ, xs⟩ | _) | _
  · exact absurd rfl (ht s κ xs)
  all_goals rfl

end NodeKeys

/-! ## Node keys and derivation keys -/

section Separation

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- Every address of the union ledger has type at most `4`. -/
theorem type_le_four_of_mem_constructionAddresses {a : Adrs}
    (ha : a ∈ constructionAddresses vp) : a.type ≤ 4 := by
  rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
  · rw [type_of_mem_forsLeafAddresses vp h]; decide
  · rw [type_of_mem_forsTreeAddresses vp h]; decide
  · rw [type_of_mem_forsRootAddresses vp h]; decide
  · rw [type_of_mem_wotsStepAddresses vp h]; decide
  · rw [type_of_mem_wotsPkAddresses vp h]; decide
  · rw [type_of_mem_xmssNodeAddresses vp h]; decide

/-- **Separation.** Under key separation no derivation key is a node key. -/
theorem prfKey_val_ne_nodeKey_val (hsep : core.KeySeparated) (k : PrfKey core)
    (κ : NodeKey core) : k.1 ≠ κ.1 := by
  obtain ⟨b, hb, hbk⟩ := k.2
  obtain ⟨a, ha, hak⟩ := κ.2
  rw [← hbk, ← hak]
  exact hsep b a hb (type_le_four_of_mem_constructionAddresses ha)

/-- Under key separation no encoded derivation is a node point, at any pair of public seeds. -/
theorem secretEncoding_enc_ne_slhGraph_pt (hsep : core.KeySeparated) (e : core.SkSeed ≃ core.Y)
    (pkSeed pkSeed' : core.PkSeed) (s : core.SkSeed × core.SkPrf) (x : DeriveQuery core)
    (κ : NodeKey core) (vs : List core.Y) :
    (secretEncoding core e pkSeed).enc s x ≠ (slhGraph core pkSeed').pt κ vs := by
  rcases x with k | ⟨o, msg⟩
  · simp only [secretEncoding_enc_inl, slhGraph_pt, ne_eq, Sum.inl.injEq,
      PublicHashQuery.thash.injEq, not_and]
    exact fun _ hk => absurd hk (prfKey_val_ne_nodeKey_val core hsep k κ)
  · simp [secretEncoding_enc_inr]

end Separation

end SLHDSA.Security
