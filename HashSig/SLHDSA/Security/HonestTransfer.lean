/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.NodeGraph

/-!
# Honest computations on caches that agree off a set of points

Fix a set `L` of public-hash points and two public-hash caches `A`, `B` that agree at every point
outside `L`. An *honest input in `L`* of `B` (`HonestInputIn`) is a point of `L` that is an honest
entry of `B` (`HonestEntry`), or the point at which the secret of a secret-key child of a ledger
address is queried. When `B` has none (`HonestTransfer`), every honest computation settled on `A`
is settled at the same value on `B`: an honest program reads only honest entries and ledger
secrets, and each of those it settles on `A` is outside `L`.

* *Readers*: the secrets, WOTS+ chains and chain tops, XMSS and FORS nodes, XMSS roots, FORS
  public keys and honest messages (`HonestTransfer.secret`, …, `HonestTransfer.honestMessage`),
  and honest entries themselves (`HonestTransfer.honestEntry`).
* *Programs*: key generation, FORS and XMSS signing and recovery from an honest signature,
  hypertree signing from any layer, and internal signing when `L` has no `H_msg` point
  (`HonestTransfer.keygen`, …, `HonestTransfer.sign`). Authentication paths and climbs are
  carried by the generic Merkle lemmas
  `PerfectMerkleTree.simulateQ_intrinsicAuthPathM_of_merkleRootM` and
  `PerfectMerkleTree.simulateQ_climbM_eq_some_of_merkleRootM`.

With `A` a cache read through a redirect of the points of `L` and `B` the cache itself, a
hidden-value hit on `A` is a hit whose honest values are read on `B` and whose hashed forger
point is outside `L` (`HiddenHitMixed`, `hiddenHitMixed_of_hiddenHit`), and coverage, which reads
only `H_msg` points, is the same on both (`itsrCovered_congr`). At `n = 32` these split the
bridge's events on the view of a run's cache through the linked redirect
(`HashSig.SLHDSA.Security.ByteLinkedView`).

## Scope

* Nothing here is probabilistic, and nothing here is quantum.
* No property of `L` is assumed.

## Labels

*Ledger*: `wotsChainAdrs_setHashAddress_mem_constructionAddresses_of_le`,
`forsNodeAdrs_sibling_mem_constructionAddresses`, `xmssCellAdrs_sibling_mem_constructionAddresses`.

*The transfer*: `HonestInputIn`, `HonestTransfer`.

*The hidden-value hit on two caches*: `HiddenHitMixed`, `hiddenHitMixed_of_hiddenHit`,
`itsrCovered_congr`.
-/

public section

open OracleComp OracleSpec PerfectMerkleTree

namespace SLHDSA.Security

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## Ledger -/

/-- A WOTS+ chain step below a ledger chain step is a ledger address. -/
theorem wotsChainAdrs_setHashAddress_mem_constructionAddresses_of_le {adrs : Adrs} {i s t : ℕ}
    (hst : s ≤ t) (h : (wotsChainAdrs adrs i).setHashAddress t ∈ constructionAddresses vp) :
    (wotsChainAdrs adrs i).setHashAddress s ∈ constructionAddresses vp := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact ih (mem_constructionAddresses_of_inr_mem_childAdrs h (by
      simp only [childAdrs_wotsChainAdrs_setHashAddress_succ, List.mem_singleton]))

/-- The sibling of the height-`z` ancestor of a leaf of FORS tree `tree` of a reachable instance,
below the tree's root, is a ledger address. -/
theorem forsNodeAdrs_sibling_mem_constructionAddresses (pos : BottomPosition vp)
    (tree : Fin vp.params.k) {idx : ℕ} (hidx : idx / 2 ^ vp.params.a = tree.val) {z : ℕ}
    (hz : z < vp.params.a) :
    forsNodeAdrs pos.forsAdrs z (sibling (idx / 2 ^ z)) ∈ constructionAddresses vp := by
  have hs : sibling (idx / 2 ^ z) / 2 ^ (vp.params.a - z) = tree.val := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hz
    rw [show vp.params.a - z = 1 + k by omega, pow_add, pow_one, ← Nat.div_div_eq_div_mul,
      sibling_div_two, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← hidx, hk, pow_succ,
      pow_add]
    ring_nf
  rcases Nat.eq_zero_or_pos z with rfl | hz0
  · exact forsLeafAdrs_mem_constructionAddresses pos tree (by simpa using hs)
  · exact forsTreeAdrs_mem_constructionAddresses pos tree hz0 hz.le hs

/-- The sibling of the height-`z` ancestor of the leaf at a layer position, below the tree's
root, is a ledger address. -/
theorem xmssCellAdrs_sibling_mem_constructionAddresses (pos : LayerPosition vp) {z : ℕ}
    (hz : z < vp.params.hp) :
    xmssCellAdrs pos.toAdrs z (sibling (pos.leaf.val / 2 ^ z)) ∈ constructionAddresses vp := by
  have hq : pos.leaf.val / 2 ^ z / 2 < 2 ^ (vp.params.hp - z - 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ, ← pow_add,
      show vp.params.hp - z - 1 + (z + 1) = vp.params.hp by omega]
    exact pos.leaf.isLt
  have hs : sibling (pos.leaf.val / 2 ^ z) < 2 ^ (vp.params.hp - z) := by
    have := sibling_div_two (pos.leaf.val / 2 ^ z)
    rw [show vp.params.hp - z = vp.params.hp - z - 1 + 1 by omega, pow_succ]
    omega
  rcases z with _ | z
  · simp only [pow_zero, Nat.div_one, Nat.sub_zero] at hs ⊢
    exact wotsPkAdrs_mem_constructionAddresses ⟨pos.layer, pos.tree, ⟨_, hs⟩⟩
  · exact xmssNodeAdrs_mem_constructionAddresses_of_position pos (Nat.succ_pos z) hz.le hs

private theorem inl_wotsSkAdrs_mem_childAdrs (adrs : Adrs) (i : ℕ) :
    .inl (wotsSkAdrs adrs i) ∈ childAdrs vp ((wotsChainAdrs adrs i).setHashAddress 0) := by
  rw [childAdrs_wotsChainAdrs_setHashAddress_zero]
  exact List.mem_singleton_self _

private theorem inl_forsSkAdrs_mem_childAdrs (adrs : Adrs) (t : ℕ) :
    .inl (forsSkAdrs adrs t) ∈ childAdrs vp (forsNodeAdrs adrs 0 t) := by
  rw [childAdrs_forsNodeAdrs_zero]
  exact List.mem_singleton_self _

private theorem add_forsIdx_div_two_pow (p : Params) (md : List Byte) (i : ℕ) :
    (i * 2 ^ p.a + forsIdx p md i) / 2 ^ p.a = i := by
  rw [← forsSigLeafIndex_eq, forsSigLeafIndex_div_pow_a]

/-! ## The transfer -/

variable (e : core.SkSeed ≃ core.Y) (pk : core.PkSeed) (sk : core.SkSeed)
  (L : (publicHashSpec core).Domain → Prop)

/-- An honest input of `B` in `L`, for the oracle-backed provider at seeds `pk`, `sk`: a point of
`L` that is an honest entry of `B`, or a point of `L` at which the secret of a secret-key child of
a ledger address is queried. -/
@[expose] def HonestInputIn (B : PublicHash.Cache core) : Prop :=
  (∃ t, L t ∧ HonestEntry (oracleSecret core e pk sk) pk B t) ∨
    ∃ a b : Adrs, a ∈ constructionAddresses vp ∧ .inl b ∈ childAdrs vp a ∧
      L (.thash pk (core.adrsToKey b) [e sk])

/-- The caches `A` and `B` agree at every point outside `L`, and `B` has no honest input in `L`
for the oracle-backed provider at seeds `pk`, `sk`. -/
structure HonestTransfer (A B : PublicHash.Cache core) : Prop where
  /-- The caches agree at every point outside `L`. -/
  eqOn : ∀ t, ¬L t → A t = B t
  /-- `B` has no honest input in `L`. -/
  not_honestInputIn : ¬HonestInputIn e pk sk L B

namespace HonestTransfer

variable {e pk sk L} {A B : PublicHash.Cache core} (h : HonestTransfer e pk sk L A B)
include h

/-- A point settled on `A` is settled at the same value on `B`, if its being in `L` makes it an
honest input of `B`. -/
theorem apply_eq_some {t : (publicHashSpec core).Domain} {v : (publicHashSpec core).Range t}
    (ht : A t = some v) (hL : L t → HonestInputIn e pk sk L B) : B t = some v := by
  by_cases hLt : L t
  · exact absurd (hL hLt) h.not_honestInputIn
  · rwa [← h.eqOn t hLt]

/-- The secret of a secret-key child of a ledger address settled on `A` is settled at the same value
on `B`. -/
theorem secret {a b : Adrs} (ha : a ∈ constructionAddresses vp)
    (hab : .inl b ∈ childAdrs vp a) {x : core.Y}
    (hx : simulateQ A.toPartialImpl (oracleSecret core e (m := OracleComp (publicHashSpec core))
      pk sk b) = some x) :
    simulateQ B.toPartialImpl (oracleSecret core e (m := OracleComp (publicHashSpec core))
      pk sk b) = some x := by
  rw [simulateQ_toPartialImpl_oracleSecret] at hx ⊢
  exact h.apply_eq_some hx fun hL => .inr ⟨a, b, ha, hab, hL⟩

/-- A WOTS+ chain whose every step is a ledger address, from a secret settled on `B`, settled on
`A` is settled at the same value on `B`. -/
theorem chain {adrs : Adrs} {i : ℕ} {x : core.Y}
    (hx : simulateQ B.toPartialImpl (oracleSecret core e (m := OracleComp (publicHashSpec core))
      pk sk (wotsSkAdrs adrs i)) = some x) :
    ∀ {t : ℕ} {v : core.Y},
      (∀ s < t, (wotsChainAdrs adrs i).setHashAddress s ∈ constructionAddresses vp) →
      chain? core A pk (wotsChainAdrs adrs i) x 0 t = some v →
      chain? core B pk (wotsChainAdrs adrs i) x 0 t = some v
  | 0, _, _, hc => hc
  | t + 1, v, hmem, hc => by
    obtain ⟨y, hy, hv⟩ := (chain?_succ_eq_some_iff core _ pk _ x 0 t).1 hc
    rw [Nat.zero_add] at hv
    have hy' := chain hx (fun s hs => hmem s (by omega)) hy
    refine (chain?_succ_eq_some_iff core _ pk _ x 0 t).2 ⟨y, hy', ?_⟩
    rw [Nat.zero_add]
    exact h.apply_eq_some hv fun hL =>
      .inl ⟨_, hL, .wotsChain adrs i t x y (hmem t (by omega)) hx hy'⟩

/-- A WOTS+ chain and its secret, settled on `A`, are settled at the same values on `B` when the
step after the chain is a ledger address. -/
theorem chain_of_mem {adrs : Adrs} {i t : ℕ} {x v : core.Y}
    (hmem : (wotsChainAdrs adrs i).setHashAddress t ∈ constructionAddresses vp)
    (hx : simulateQ A.toPartialImpl (oracleSecret core e (m := OracleComp (publicHashSpec core))
      pk sk (wotsSkAdrs adrs i)) = some x)
    (hc : chain? core A pk (wotsChainAdrs adrs i) x 0 t = some v) :
    simulateQ B.toPartialImpl (oracleSecret core e (m := OracleComp (publicHashSpec core))
      pk sk (wotsSkAdrs adrs i)) = some x ∧
        chain? core B pk (wotsChainAdrs adrs i) x 0 t = some v := by
  have hx' := h.secret (wotsChainAdrs_setHashAddress_mem_constructionAddresses_of_le
    (Nat.zero_le t) hmem) (inl_wotsSkAdrs_mem_childAdrs _ _) hx
  exact ⟨hx', h.chain hx' (fun s hs =>
    wotsChainAdrs_setHashAddress_mem_constructionAddresses_of_le hs.le hmem) hc⟩

/-- The chain tops of a WOTS+ public key at a ledger address, settled on `A`, are settled at the
same values on `B`. -/
theorem wotsTops {adrs : Adrs} {tops : Vector core.Y vp.params.len}
    (hmem : wotsPkAdrs adrs ∈ constructionAddresses vp)
    (ht : wotsPkGenTopsWithSecret? core A (oracleSecret core e pk sk) pk adrs = some tops) :
    wotsPkGenTopsWithSecret? core B (oracleSecret core e pk sk) pk adrs = some tops := by
  have hw : 2 ≤ vp.params.w := Nat.one_lt_two_pow vp.valid.lgw_pos.ne'
  rw [wotsPkGenTopsWithSecret?_eq_some_iff] at ht ⊢
  intro i
  obtain ⟨x, hx, hc⟩ := ht i
  have hmem' := mem_constructionAddresses_of_inr_mem_childAdrs hmem
    (by rw [childAdrs_wotsPkAdrs]; exact List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)
  change chain? core A pk _ x 0 _ = _ at hc
  rw [show vp.params.w - 1 = vp.params.w - 2 + 1 by omega] at hc ⊢
  obtain ⟨y, hy, hv⟩ := (chain?_succ_eq_some_iff core _ pk _ x 0 _).1 hc
  obtain ⟨hx', hy'⟩ := h.chain_of_mem hmem' hx hy
  refine ⟨x, hx', (chain?_succ_eq_some_iff core _ pk _ x 0 _).2 ⟨y, hy', ?_⟩⟩
  rw [Nat.zero_add] at hv ⊢
  exact h.apply_eq_some hv fun hL => .inl ⟨_, hL, .wotsChain adrs i _ x y hmem' hx' hy'⟩

/-- An XMSS node at a ledger address settled on `A` is settled at the same value on `B`. -/
theorem xmssNode {adrs : Adrs} :
    ∀ {z t : ℕ} {v : core.Y}, xmssCellAdrs adrs z t ∈ constructionAddresses vp →
      xmssNodeWithSecret? core A (oracleSecret core e pk sk) pk adrs z t = some v →
      xmssNodeWithSecret? core B (oracleSecret core e pk sk) pk adrs z t = some v
  | 0, t, v, hmem, hn => by
    simp only [xmssNodeWithSecret?, xmssNodeWithSecret, merkleRootM, xmssLeafWithSecret,
      wotsPkGenWithSecret, simulateQ_bind_eq_some_iff, simulateQ_toPartialImpl_tl] at hn ⊢
    obtain ⟨tops, htops, hv⟩ := hn
    have htops' := h.wotsTops hmem htops
    exact ⟨tops, htops', h.apply_eq_some hv fun hL => .inl ⟨_, hL, .wotsPk _ tops hmem htops'⟩⟩
  | z + 1, t, v, hmem, hn => by
    obtain ⟨l, r, hl, hr, hv⟩ := (simulateQ_merkleRootM_succ_eq_some_iff _ _ _ z t).1 hn
    have hm := fun b (hb : .inr b ∈ childAdrs vp (xmssCellAdrs adrs (z + 1) t)) ↦
      mem_constructionAddresses_of_inr_mem_childAdrs hmem hb
    rw [childAdrs_xmssCellAdrs_succ] at hm
    have hl' := xmssNode (hm _ (by simp)) hl
    have hr' := xmssNode (hm _ (by simp)) hr
    rw [xmssNodeHashWith, simulateQ_toPartialImpl_h] at hv
    refine (simulateQ_merkleRootM_succ_eq_some_iff _ _ _ z t).2 ⟨l, r, hl', hr', ?_⟩
    rw [xmssNodeHashWith, simulateQ_toPartialImpl_h]
    exact h.apply_eq_some hv fun hL =>
      .inl ⟨_, hL, .xmssNode adrs (z + 1) t l r (Nat.succ_pos z) hmem hl' hr'⟩

/-- A FORS node at a ledger address settled on `A` is settled at the same value on `B`. -/
theorem forsNode {adrs : Adrs} :
    ∀ {z t : ℕ} {v : core.Y}, forsNodeAdrs adrs z t ∈ constructionAddresses vp →
      forsNodeWithSecret? core A (oracleSecret core e pk sk) pk adrs z t = some v →
      forsNodeWithSecret? core B (oracleSecret core e pk sk) pk adrs z t = some v
  | 0, t, v, hmem, hn => by
    simp only [forsNodeWithSecret?, merkleRootM, forsLeafWithSecret, simulateQ_bind_eq_some_iff,
      simulateQ_toPartialImpl_f] at hn ⊢
    obtain ⟨x, hx, hv⟩ := hn
    have hx' := h.secret hmem (inl_forsSkAdrs_mem_childAdrs _ _) hx
    exact ⟨x, hx', h.apply_eq_some hv fun hL => .inl ⟨_, hL, .forsLeaf adrs t x hmem hx'⟩⟩
  | z + 1, t, v, hmem, hn => by
    obtain ⟨l, r, hl, hr, hv⟩ := (simulateQ_merkleRootM_succ_eq_some_iff _ _ _ z t).1 hn
    have hm := fun b (hb : .inr b ∈ childAdrs vp (forsNodeAdrs adrs (z + 1) t)) ↦
      mem_constructionAddresses_of_inr_mem_childAdrs hmem hb
    rw [childAdrs_forsNodeAdrs vp (Nat.succ_pos z) adrs t] at hm
    have hl' := forsNode (hm _ (by simp)) hl
    have hr' := forsNode (hm _ (by simp)) hr
    rw [forsNodeHashWith, simulateQ_toPartialImpl_h] at hv
    refine (simulateQ_merkleRootM_succ_eq_some_iff _ _ _ z t).2 ⟨l, r, hl', hr', ?_⟩
    rw [forsNodeHashWith, simulateQ_toPartialImpl_h]
    exact h.apply_eq_some hv fun hL =>
      .inl ⟨_, hL, .forsNode adrs (z + 1) t l r (Nat.succ_pos z) hmem hl' hr'⟩

/-- An honest entry of `A` is an honest entry of `B`. -/
theorem honestEntry {t : (publicHashSpec core).Domain}
    (ht : HonestEntry (oracleSecret core e pk sk) pk A t) :
    HonestEntry (oracleSecret core e pk sk) pk B t := by
  cases ht with
  | xmssNode adrs z i l r hh hmem hl hr =>
    obtain ⟨z, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hh.ne'
    have hm := fun b (hb : .inr b ∈ childAdrs vp (xmssCellAdrs adrs (z + 1) i)) ↦
      mem_constructionAddresses_of_inr_mem_childAdrs hmem hb
    rw [childAdrs_xmssCellAdrs_succ] at hm
    exact .xmssNode adrs (z + 1) i l r hh hmem (h.xmssNode (hm _ (by simp)) hl)
      (h.xmssNode (hm _ (by simp)) hr)
  | wotsPk adrs tops hmem ht => exact .wotsPk adrs tops hmem (h.wotsTops hmem ht)
  | wotsChain adrs i t x v hmem hx hc =>
    obtain ⟨hx', hc'⟩ := h.chain_of_mem hmem hx hc
    exact .wotsChain adrs i t x v hmem hx' hc'
  | forsLeaf adrs t x hmem hx =>
    exact .forsLeaf adrs t x hmem (h.secret hmem (inl_forsSkAdrs_mem_childAdrs _ _) hx)
  | forsNode adrs z i l r hh hmem hl hr =>
    have hm := fun b (hb : .inr b ∈ childAdrs vp (forsNodeAdrs adrs z i)) ↦
      mem_constructionAddresses_of_inr_mem_childAdrs hmem hb
    rw [childAdrs_forsNodeAdrs vp hh adrs i] at hm
    exact .forsNode adrs z i l r hh hmem (h.forsNode (hm _ (by simp)) hl)
      (h.forsNode (hm _ (by simp)) hr)
  | forsRoots adrs roots hmem ht =>
    refine .forsRoots adrs roots hmem fun i => h.forsNode
      (mem_constructionAddresses_of_inr_mem_childAdrs hmem ?_) (ht i)
    rw [childAdrs_forsPkAdrs]
    exact List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩

/-- The root of an XMSS tree at a ledger root address settled on `A` is settled at the same value on
`B`. -/
theorem xmssRoot {adrs : Adrs} {v : core.Y}
    (hmem : xmssNodeAdrs adrs vp.params.hp 0 ∈ constructionAddresses vp)
    (hr : xmssRootWithSecret? core A (oracleSecret core e pk sk) pk adrs = some v) :
    xmssRootWithSecret? core B (oracleSecret core e pk sk) pk adrs = some v := by
  have hp := vp.valid.hp_pos
  unfold xmssRootWithSecret? xmssRootWithSecret at hr ⊢
  generalize vp.params.hp = n at hp hmem hr ⊢
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  exact h.xmssNode (z := z + 1) hmem hr

/-- The FORS public key of an instance at a ledger roots address settled on `A` is settled at the
same value on `B`. -/
theorem forsPk {adrs : Adrs} {v : core.Y} (hmem : forsPkAdrs adrs ∈ constructionAddresses vp)
    (hv : forsPkGenWithSecret? core A (oracleSecret core e pk sk) pk adrs = some v) :
    forsPkGenWithSecret? core B (oracleSecret core e pk sk) pk adrs = some v := by
  obtain ⟨roots, hroots, hv⟩ := (forsPkGenWithSecret?_eq_some_iff core _ _ pk adrs).1 hv
  have hroots' : ∀ i : Fin vp.params.k, forsNodeWithSecret? core B (oracleSecret core e pk sk)
      pk adrs vp.params.a i.val = some roots[i] := fun i => h.forsNode
    (mem_constructionAddresses_of_inr_mem_childAdrs hmem (by
      rw [childAdrs_forsPkAdrs]; exact List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)) (hroots i)
  exact (forsPkGenWithSecret?_eq_some_iff core _ _ pk adrs).2 ⟨roots, hroots',
    h.apply_eq_some hv fun hL => .inl ⟨_, hL, .forsRoots adrs roots hmem hroots'⟩⟩

/-- The honest message signed at a layer position settled on `A` is settled at the same value on
`B`. -/
theorem honestMessage (pos : LayerPosition vp) {m : core.Y}
    (hm : honestMessage? A (oracleSecret core e pk sk) pk pos = some m) :
    honestMessage? B (oracleSecret core e pk sk) pk pos = some m := by
  unfold honestMessage? at hm ⊢
  split_ifs at hm ⊢ with h0
  · exact h.forsPk (forsPkAdrs_forsInstanceAdrs_mem_constructionAddresses pos h0) hm
  · exact h.xmssRoot
      (xmssNodeAdrs_childTreeAdrs_mem_constructionAddresses pos (Nat.pos_of_ne_zero h0)) hm

/-- Key generation settled on `A` is settled at the same value on `B`. -/
theorem keygen {r : core.Y}
    (hr : simulateQ A.toPartialImpl
      (GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pk sk) pk) = some r) :
    simulateQ B.toPartialImpl
      (GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pk sk) pk) = some r := by
  refine h.xmssRoot ?_ hr
  rw [← LayerTreeCoord.top_toAdrs_layerAdrs]
  exact xmssNodeAdrs_mem_constructionAddresses _ vp.valid.hp_pos le_rfl (by simp)

/-- FORS signing of a digest at a reachable instance settled on `A` is settled at the same value on
`B`. -/
theorem forsSign (pos : BottomPosition vp) (md : List Byte) {sig : ForsSigCore vp.params core}
    (hs : simulateQ A.toPartialImpl
      (forsSignWithSecretM core (oracleSecret core e pk sk) md pk pos.forsAdrs) = some sig) :
    simulateQ B.toPartialImpl
      (forsSignWithSecretM core (oracleSecret core e pk sk) md pk pos.forsAdrs) = some sig := by
  rw [simulateQ_toPartialImpl_forsSignWithSecret_eq_some_iff] at hs ⊢
  intro i
  obtain ⟨x, hx, path, hpath, hsig⟩ := hs i
  have hidx := add_forsIdx_div_two_pow vp.params md i
  exact ⟨x, h.secret (forsLeafAdrs_mem_constructionAddresses pos i hidx)
      (inl_forsSkAdrs_mem_childAdrs _ _) hx,
    path, simulateQ_intrinsicAuthPathM_of_merkleRootM _ _ _ _ _ (fun z hz w hw =>
      h.forsNode (forsNodeAdrs_sibling_mem_constructionAddresses pos i hidx hz) hw) hpath, hsig⟩

/-- Recovery of the FORS public key from an honest FORS signature at a reachable instance,
settled on `A`, is settled at the same value on `B`. -/
theorem forsPkFromSig (pos : BottomPosition vp) (md : List Byte)
    {sig : ForsSigCore vp.params core} {fpk : core.Y}
    (hs : simulateQ A.toPartialImpl
      (forsSignWithSecretM core (oracleSecret core e pk sk) md pk pos.forsAdrs) = some sig)
    (hr : simulateQ A.toPartialImpl (forsPkFromSigM core sig md pk pos.forsAdrs) = some fpk) :
    simulateQ B.toPartialImpl (forsPkFromSigM core sig md pk pos.forsAdrs) = some fpk := by
  obtain ⟨roots, hroots, hv⟩ := (forsPkGenWithSecret?_eq_some_iff core _ _ pk _).1
    (h.forsPk (forsRootAdrs_mem_constructionAddresses pos)
      (forsPkGenWithSecret?_eq_some_of_forsSignWithSecret core A _ md pk _ hs hr))
  have hsB := (simulateQ_toPartialImpl_forsSignWithSecret_eq_some_iff core B _ md pk _).1
    (h.forsSign pos md hs)
  refine (simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff core B _ md pk _).2
    ⟨roots, fun i => ?_, hv⟩
  obtain ⟨x, hx, path, hpath, hsig⟩ := hsB i
  have hroot : forsNodeWithSecret? core B (oracleSecret core e pk sk) pk pos.forsAdrs
      vp.params.a ((i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) / 2 ^ vp.params.a) =
        some roots[i] := by
    rw [add_forsIdx_div_two_pow]
    exact hroots i
  obtain ⟨y, hy⟩ := exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq _ _ _ hroot
    (Nat.zero_le _) (by rw [Nat.sub_zero])
  have hy' := hy
  simp only [merkleRootM, forsLeafWithSecret, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_f] at hy'
  obtain ⟨x', hx', hpt⟩ := hy'
  obtain rfl : x' = x := Option.some_inj.1 (hx'.symm.trans hx)
  rw [Fin.getElem_fin] at hsig
  rw [← hsig]
  exact ⟨y, hpt, simulateQ_climbM_eq_some_of_merkleRootM _ _ _ _ hy hpath hroot⟩

/-- XMSS signing at a layer position settled on `A` is settled at the same value on `B`. -/
theorem xmssSign (pos : LayerPosition vp) (msg : core.Y) {sig : XmssSig vp.params core}
    (hs : simulateQ A.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
      (PublicHash.tl core pk) (PublicHash.h core pk) (oracleSecret core e pk sk) msg pos.toAdrs
        pos.leaf.val) = some sig) :
    simulateQ B.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
      (PublicHash.tl core pk) (PublicHash.h core pk) (oracleSecret core e pk sk) msg pos.toAdrs
        pos.leaf.val) = some sig := by
  rw [simulateQ_toPartialImpl_xmssSignWithSecret_eq_some_iff] at hs ⊢
  obtain ⟨hpath, hwots⟩ := hs
  refine ⟨simulateQ_intrinsicAuthPathM_of_merkleRootM _ _ _ _ _ (fun z hz w hw =>
    h.xmssNode (xmssCellAdrs_sibling_mem_constructionAddresses pos hz) hw) hpath, ?_⟩
  rw [simulateQ_toPartialImpl_wotsSignWithSecret_eq_some_iff] at hwots ⊢
  intro i
  obtain ⟨x, hx, hc⟩ := hwots i
  have hw : 2 ≤ vp.params.w := Nat.one_lt_two_pow vp.valid.lgw_pos.ne'
  have hmem : ∀ s < chainStepsCore core msg i.val, (wotsChainAdrs (wotsLeafAdrs pos.toAdrs
      pos.leaf.val) i.val).setHashAddress s ∈ constructionAddresses vp := fun s hs =>
    wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i
      (by have := chainStepsCore_le core msg i.val; omega)
  have hx' := h.secret (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i
    (t := 0) (by omega)) (inl_wotsSkAdrs_mem_childAdrs _ _) hx
  exact ⟨x, hx', h.chain hx' hmem hc⟩

/-- Recovery of the XMSS root from an honest XMSS signature at a layer position, settled on `A`,
is settled at the same value on `B`. -/
theorem xmssPkFromSig (pos : LayerPosition vp) (msg : core.Y) {sig : XmssSig vp.params core}
    {root : core.Y}
    (hs : simulateQ A.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
      (PublicHash.tl core pk) (PublicHash.h core pk) (oracleSecret core e pk sk) msg pos.toAdrs
        pos.leaf.val) = some sig)
    (hr : simulateQ A.toPartialImpl (xmssPkFromSigM core pos.leaf.val sig msg pk pos.toAdrs) =
      some root) :
    simulateQ B.toPartialImpl (xmssPkFromSigM core pos.leaf.val sig msg pk pos.toAdrs) =
      some root := by
  have hidx := pos.leaf.isLt
  have hrootB := h.xmssRoot
    (xmssNodeAdrs_mem_constructionAddresses_of_position pos vp.valid.hp_pos le_rfl (by simp))
    (xmssRootWithSecret?_eq_some_of_xmssSignWithSecret core A _ msg pk _ _ hs hidx hr)
  obtain ⟨hpath, hwots⟩ :=
    (simulateQ_toPartialImpl_xmssSignWithSecret_eq_some_iff core B _ msg pk _ _).1
      (h.xmssSign pos msg hs)
  have hroot : simulateQ B.toPartialImpl (merkleRootM
      (xmssLeafWithSecret core (PublicHash.f core pk) (PublicHash.tl core pk)
        (oracleSecret core e pk sk) pos.toAdrs) (xmssNodeHashM core pk pos.toAdrs) vp.params.hp
      (pos.leaf.val / 2 ^ vp.params.hp)) = some root := by
    rw [Nat.div_eq_of_lt hidx]
    exact hrootB
  obtain ⟨y, hy⟩ := exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq _ _ _ hroot
    (Nat.zero_le _) (by rw [Nat.sub_zero])
  have hy' := hy
  simp only [merkleRootM, xmssLeafWithSecret, wotsPkGenWithSecret, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_tl] at hy'
  obtain ⟨tops, htops, hpt⟩ := hy'
  refine (simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff core B _ _ msg pk _).2
    ⟨y, ⟨tops, ?_, hpt⟩, simulateQ_climbM_eq_some_of_merkleRootM _ _ _ _ hy hpath hroot⟩
  rw [simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff]
  replace htops : wotsPkGenTopsWithSecret? core B _ pk _ = some tops := htops
  rw [wotsPkGenTopsWithSecret?_eq_some_iff] at htops
  rw [simulateQ_toPartialImpl_wotsSignWithSecret_eq_some_iff] at hwots
  intro i
  obtain ⟨x, hx, hc⟩ := htops i
  obtain ⟨x', hx', hc'⟩ := hwots i
  obtain rfl : x' = x := Option.some_inj.1 (hx'.symm.trans hx)
  rw [← Nat.add_sub_cancel' (chainStepsCore_le core msg i.val),
    simulateQ_toPartialImpl_chainM_add_eq_some_iff] at hc
  obtain ⟨w, hw, hc⟩ := hc
  obtain rfl : w = sig.wots[i] := Option.some_inj.1 (hw.symm.trans hc')
  rwa [Nat.zero_add] at hc

/-- Hypertree signing from a layer position through `layers` layers settled on `A` is settled at the
same value on `B`. -/
theorem signFromPosition (rf : Bool) :
    ∀ (pos : LayerPosition vp) (layers : ℕ) (hl : pos.layer.val + layers = vp.params.d)
      (msg : core.Y) {sigs : Vector (XmssSig vp.params core) layers},
      simulateQ A.toPartialImpl (GeneralHypertree.signFromPositionWithSecret core
        (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk)
        (oracleSecret core e pk sk) rf pos layers hl msg) = some sigs →
      simulateQ B.toPartialImpl (GeneralHypertree.signFromPositionWithSecret core
        (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk)
        (oracleSecret core e pk sk) rf pos layers hl msg) = some sigs
  | _, 0, _, _, _, hss => hss
  | pos, 1, hl, msg, sigs, hss => by
    cases rf
    · obtain ⟨sig, hs, rfl⟩ :=
        (simulateQ_toPartialImpl_signFromPositionWithSecret_one_false_eq_some_iff core A _ pk pos
          hl msg).1 hss
      exact (simulateQ_toPartialImpl_signFromPositionWithSecret_one_false_eq_some_iff core B _ pk
        pos hl msg).2 ⟨sig, h.xmssSign pos msg hs, rfl⟩
    · simp only [GeneralHypertree.signFromPositionWithSecret,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind_eq_some_iff,
        simulateQ_pure_eq_some_iff, ↓reduceIte] at hss ⊢
      obtain ⟨sig, hs, r, hr, rfl⟩ := hss
      exact ⟨sig, h.xmssSign pos msg hs, r, h.xmssPkFromSig pos msg hs hr, rfl⟩
  | pos, layers + 2, hl, msg, sigs, hss => by
    obtain ⟨sig, root, rest, hs, hr, hrest, rfl⟩ :=
      (simulateQ_toPartialImpl_signFromPositionWithSecret_add_two_eq_some_iff core A _ pk rf pos
        layers hl msg).1 hss
    exact (simulateQ_toPartialImpl_signFromPositionWithSecret_add_two_eq_some_iff core B _ pk rf
      pos layers hl msg).2 ⟨sig, root, rest, h.xmssSign pos msg hs,
        h.xmssPkFromSig pos msg hs hr, signFromPosition false _ _ _ root hrest, rfl⟩

/-- Internal signing at a randomizer settled on `A` is settled at the same value on `B`, when `L`
has no `H_msg` point. -/
theorem sign (hm : ∀ r s root msg, ¬L (.hmsg r s root msg)) (msg : List Byte) (pkRoot R : core.Y)
    {σ : GeneralScheme.SignatureCore vp core}
    (hs : simulateQ A.toPartialImpl (GeneralScheme.signInternalWithSecretRandomizerM core
      (oracleSecret core e pk sk) msg pk pkRoot R) = some σ) :
    simulateQ B.toPartialImpl (GeneralScheme.signInternalWithSecretRandomizerM core
      (oracleSecret core e pk sk) msg pk pkRoot R) = some σ := by
  obtain ⟨digest, forsSig, forsPk, htSig, hd, hfs, hfp, hht, rfl⟩ :=
    (simulateQ_toPartialImpl_signInternalWithSecretRandomizerM_eq_some_iff core A _ msg pk pkRoot
      R).1 hs
  have hpos := BottomPosition.forsAdrs_ofDigestParts vp (splitDigest vp.params digest)
  rw [← hpos] at hfs hfp
  refine (simulateQ_toPartialImpl_signInternalWithSecretRandomizerM_eq_some_iff core B _ msg pk
    pkRoot R).2 ⟨digest, forsSig, forsPk, htSig, h.eqOn _ (hm _ _ _ _) ▸ hd, ?_, ?_,
      h.signFromPosition _ _ _ _ _ hht, rfl⟩
  · rw [← hpos]
    exact h.forsSign _ _ hfs
  · rw [← hpos]
    exact h.forsPkFromSig _ _ hfs hfp

end HonestTransfer

/-! ## The hidden-value hit on two caches -/

/-- A hidden-value hit whose forger replay is read on `V` and whose honest values are read on
`C`, and whose point hashed by the verification at the hit is not in `S`: either the forgery's
WOTS+ signature entry on chain `i` of the leaf its replay on `V` enters at layer `j` with message
`m` is the honest chain value on `C` at the hidden step `t = chainStepsCore core m i < w - 1`, and
the step `t` point at that value is not in `S`; or, at a FORS coordinate of the forger's digest no
logged signature opened, the forgery carries the secret settled on `C`, and the FORS leaf point at
that value is not in `S`. -/
@[expose] def HiddenHitMixed (S : (publicHashSpec core).Domain → Prop)
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (o : RomOutcome vp core) (V C : PublicHash.Cache core) : Prop :=
  (∃ (j : Fin vp.params.d) (pos : LayerPosition vp) (m : core.Y) (i : Fin vp.params.len)
      (x : core.Y),
    ForgerLayer o V j pos m ∧
    HiddenChainValue secret o C j pos i.val (chainStepsCore core m i.val) ∧
    chainStepsCore core m i.val < vp.params.w - 1 ∧
    simulateQ C.toPartialImpl
      (secret (wotsSkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)) = some x ∧
    chain? core C o.pk.pkSeed (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val) x 0
      (chainStepsCore core m i.val) = some (o.sig.hypertree[j]).wots[i] ∧
    ¬S (.thash o.pk.pkSeed (core.adrsToKey ((wotsChainAdrs (wotsLeafAdrs pos.toAdrs
      pos.leaf.val) i.val).setHashAddress (chainStepsCore core m i.val)))
        [(o.sig.hypertree[j]).wots[i]])) ∨
  (∃ (digest : Bytes vp.params.m) (i : Fin vp.params.k),
    ForgerDigest o C digest ∧
    UnopenedCoord o C (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val) ∧
    simulateQ C.toPartialImpl (secret (forsSkAdrs (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val))) =
        some (o.sig.fors[i]).sk ∧
    ¬S (.thash o.pk.pkSeed (core.adrsToKey (forsNodeAdrs (splitDigest vp.params digest).forsAdrs
      0 (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val)))
        [(o.sig.fors[i]).sk]))

/-- Coverage reads only `H_msg` points, so caches that agree on them agree on coverage. -/
theorem itsrCovered_congr {o : RomOutcome vp core} {V C : PublicHash.Cache core}
    (hV : ∀ r s root msg, V (.hmsg r s root msg) = C (.hmsg r s root msg)) :
    ItsrCovered o V ↔ ItsrCovered o C := by
  simp only [ItsrCovered, ForgerDigest, LoggedDigest, hV]

/-- If `V` transfers honestly to `C` off a set `L` with no `H_msg` point, a hidden-value hit on
`V` for the oracle-backed provider is a hit on `V` and `C` whose hashed point is not in `L`. -/
theorem hiddenHitMixed_of_hiddenHit {e : core.SkSeed ≃ core.Y}
    {L : (publicHashSpec core).Domain → Prop} {o : RomOutcome vp core}
    {V C : PublicHash.Cache core} (h : HonestTransfer e o.pk.pkSeed o.sk.skSeed L V C)
    (hm : ∀ r s root msg, ¬L (.hmsg r s root msg))
    (hh : HiddenHit (oracleSecret core e o.pk.pkSeed o.sk.skSeed) o V) :
    HiddenHitMixed L (oracleSecret core e o.pk.pkSeed o.sk.skSeed) o V C := by
  have hV : ∀ r s root msg, V (.hmsg r s root msg) = C (.hmsg r s root msg) :=
    fun r s root msg => h.eqOn _ (hm r s root msg)
  rcases hh with ⟨j, pos, m, i, x, hFL, hHCV, ht, hx, hg⟩ | ⟨digest, i, hD, hUC, hx⟩
  · obtain ⟨hx', hg'⟩ :=
      h.chain_of_mem (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i ht) hx hg
    refine .inl ⟨j, pos, m, i, x, hFL, fun hUL => ?_, ht, hx', hg', fun hL =>
      h.not_honestInputIn (.inl ⟨_, hL, .wotsChain _ i.val _ x _
        (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i ht) hx' hg'⟩)⟩
    obtain ⟨m', hm', hlt⟩ := hHCV (by simpa only [UsedLeaf, LoggedDigest, hV] using hUL)
    exact ⟨m', h.honestMessage pos hm', hlt⟩
  · have hmem : forsNodeAdrs (splitDigest vp.params digest).forsAdrs 0
        (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val) ∈
          constructionAddresses vp := by
      rw [← BottomPosition.forsAdrs_ofDigestParts]
      exact forsLeafAdrs_mem_constructionAddresses _ i (forsSigLeafIndex_div_pow_a _ _ _)
    have hx' := h.secret hmem (inl_forsSkAdrs_mem_childAdrs _ _) hx
    refine .inr ⟨digest, i, by simpa only [ForgerDigest, hV] using hD,
      by simpa only [UnopenedCoord, LoggedDigest, hV] using hUC, hx', fun hL =>
        h.not_honestInputIn (.inl ⟨_, hL, .forsLeaf _ _ _ hmem hx'⟩)⟩

end SLHDSA.Security
