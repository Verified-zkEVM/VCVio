/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.NodeGraph

/-!
# Honest readers on a merged relabelled state read node labels

A state `st` of the relabelled game over the SLH-DSA graph `slhGraph core pkSeed` stands, at
secret seeds `s`, for the public-hash cache

`((secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st)).fst`:

an encoded secret point `F(PK.seed, k, [e SK.seed])` reads the derivation cell at key `k`, the
point of a node at its drawn children values reads the node's label, and every other point reads
the public cache. This module shows that the honest readers of
`HashSig.SLHDSA.Security.CacheReaders` and `HashSig.SLHDSA.Security.CacheSecret`, run on that cache
at the oracle-backed provider `oracleSecret core e pkSeed s.1`, return drawn cells. The scoped
notations `𝒞[e, pkSeed, s, st]` for that cache and `𝒮[e, pkSeed, s]` for that provider are opened
by `open scoped SLHDSA.Security.MergedCache`.

* The secret at a secret-key address reads its derivation cell
  (`simulateQ_toPartialImpl_oracleSecret_merge`).
* The point of a node at its drawn children values reads its label
  (`merge_fst_thash_of_childVals_eq_some`); at any other input list it reads the public cache
  (`merge_fst_thash_of_childVals_ne`), and so does every `H_msg` point (`merge_fst_hmsg`,
  `merge_fst_hmsg_of_fst_eq`).
* Bottom-up, every value a reader returns is the drawn cell of the corresponding node: the
  children of the node are drawn at the values the reader hashed, so its point is the point at its
  children values, and the merge reads its label there. This gives the children of a WOTS+ chain
  step (`childVals_eq_some_of_chain?`) and of a FORS leaf (`childVals_eq_some_of_forsSkAdrs`), and
  the labels of XMSS roots (`label_of_xmssRootWithSecret?`), of FORS public keys
  (`label_of_forsPkGenWithSecret?`) and of the honest message signed at a hypertree position, the
  label of the node at `msgAdrs pos` (`label_of_honestMessage?`).
* Every honest entry is the point of a node at its drawn children values
  (`exists_childVals_eq_some_of_honestEntry`), so a target collision of the merged cache is a
  public entry at a node's key equal to the node's drawn label (`tcHazard_of_targetCollision`).

The point lemmas assume key separation (`CorePrimitives.KeySeparated`), which keeps encoded
secrets off node points. The reader lemmas assume the key discipline
(`CorePrimitives.KeyDiscipline`), whose key injectivity also identifies the graph children of a
node with the structural children of its ledger address. Nothing is assumed about the state: a
drawn label is read wherever its children are drawn, whatever the public cache holds at its
point, so neither the absence of a conflict (`CanonicalGraph.Conflict`) nor completeness of the
drawn labels (`CanonicalGraph.LabelsComplete`) is needed.

## Scope

* Ledger membership of a reader's node is a hypothesis; every node below it is in the ledger by
  closure (`mem_constructionAddresses_of_inr_mem_childAdrs`). The honest message's node is in the
  ledger at every position (`msgAdrs_mem_constructionAddresses`).
* Nothing here is probabilistic: the statements hold for every state and every pair of secret
  seeds.

## Labels

*Points of the merged cache*: `simulateQ_toPartialImpl_oracleSecret_merge`,
`merge_fst_thash_of_childVals_eq_some`, `merge_fst_thash_of_childVals_ne`, `merge_fst_hmsg`,
`merge_fst_hmsg_of_fst_eq`.

*Readers*: `childVals_eq_some_of_chain?`, `label_of_xmssRootWithSecret?`,
`childVals_eq_some_of_forsSkAdrs`, `label_of_forsPkGenWithSecret?`, `label_of_honestMessage?`.

*Honest entries*: `exists_childVals_eq_some_of_honestEntry`, `tcHazard_of_targetCollision`.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

variable {vp : ValidatedParams} {core : CorePrimitives vp.params} {e : core.SkSeed ≃ core.Y}
  {pkSeed : core.PkSeed} {s : core.SkSeed × core.SkPrf}
  {st : LabState core}

namespace MergedCache

/-- The public-hash cache that the relabelled state `st` stands for at the secret seeds `s`, under
the secret encoding of `e` at the public seed `pkSeed`. -/
scoped notation "𝒞[" e ", " pkSeed ", " s ", " st "]" =>
  QueryCache.fst (SecretEncoding.merge (secretEncoding _ e pkSeed) s
    (CanonicalGraph.toSplitCache (slhGraph _ pkSeed) st))

/-- The oracle-backed secret provider at the first secret seed of `s`. -/
scoped notation "𝒮[" e ", " pkSeed ", " s "]" => oracleSecret _ e pkSeed (Prod.fst s)

end MergedCache

open scoped MergedCache

/-! ## Points of the merged cache -/

private theorem map_cast_eq {α : Type} {h : α = α} (o : Option α) : o.map (cast h) = o := by
  cases o <;> rfl

/-- At a secret-key address, the oracle-backed secret reads the derivation cell at its key. -/
theorem simulateQ_toPartialImpl_oracleSecret_merge {b : Adrs} (hb : b.IsSecretKey) :
    simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl (𝒮[e, pkSeed, s] b) =
      st.2 (.inl (.inl ⟨core.adrsToKey b, b, hb, rfl⟩)) := by
  rw [oracleSecret, simulateQ_toPartialImpl_f, QueryCache.fst_apply]
  exact ((secretEncoding core e pkSeed).merge_toSplitCache_apply_enc (slhGraph core pkSeed) s st
    (.inl ⟨core.adrsToKey b, b, hb, rfl⟩)).trans (map_cast_eq _)

/-- At the point of a node at its drawn children values, the merged cache reads the node's
label. -/
theorem merge_fst_thash_of_childVals_eq_some (hsep : core.KeySeparated) {κ : NodeKey core}
    {vs : List core.Y} (h : (slhGraph core pkSeed).childVals st κ = some vs) :
    𝒞[e, pkSeed, s, st] (.thash pkSeed κ.1 vs) = st.2 (.inr κ) :=
  ((secretEncoding core e pkSeed).merge_toSplitCache_apply_pt (slhGraph core pkSeed) s
    (fun x ↦ secretEncoding_enc_ne_slhGraph_pt core hsep e pkSeed pkSeed s x κ vs)
    h).trans (map_cast_eq _)

/-- At a node's key and an input list at which the node's children are not drawn, because a child
is undrawn or the children are drawn at other values, the merged cache reads the public cache, at
every length of the input list. -/
theorem merge_fst_thash_of_childVals_ne (hsep : core.KeySeparated) {κ : NodeKey core}
    {vs : List core.Y} (h : (slhGraph core pkSeed).childVals st κ ≠ some vs) :
    𝒞[e, pkSeed, s, st] (.thash pkSeed κ.1 vs) = st.1 (.inl (.thash pkSeed κ.1 vs)) := by
  refine (secretEncoding core e pkSeed).merge_toSplitCache_apply_of_not_exists
    (slhGraph core pkSeed) s
    (fun x ↦ secretEncoding_enc_ne_slhGraph_pt core hsep e pkSeed pkSeed s x κ vs) ?_
  rintro ⟨κ', vs', hκ', hpt⟩
  obtain ⟨rfl, rfl⟩ := slhGraph_pt_inj core pkSeed hpt
  exact h hκ'

/-- Every `H_msg` point of the merged cache reads the public cache. -/
theorem merge_fst_hmsg (r : core.Y) (pk : core.PkSeed) (root : core.Y) (msg : List Byte) :
    𝒞[e, pkSeed, s, st] (.hmsg r pk root msg) = st.1 (.inl (.hmsg r pk root msg)) :=
  (secretEncoding core e pkSeed).merge_toSplitCache_apply_of_not_exists (slhGraph core pkSeed) s
    (fun x ↦ by rcases x with _ | _ <;> simp [secretEncoding])
    (by rintro ⟨_, _, -, h⟩; simp [slhGraph_pt] at h)

/-- Every `H_msg` point of the merged cache of `st` reads the public cache of any state `st₀` with
the same public cache. -/
theorem merge_fst_hmsg_of_fst_eq {st₀ : LabState core} (h : st.1 = st₀.1) (r : core.Y)
    (pk : core.PkSeed) (root : core.Y) (msg : List Byte) :
    𝒞[e, pkSeed, s, st] (.hmsg r pk root msg) = st₀.1 (.inl (.hmsg r pk root msg)) := by
  rw [merge_fst_hmsg, h]

/-! ## Structural children -/

/-- The value drawn at the cell of a structural child. -/
private def cellValue (st : LabState core) (b : Adrs ⊕ Adrs) : Option core.Y :=
  (childCell core b).bind fun c ↦ st.2 c

private theorem cellValue_inr {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    cellValue st (.inr a) = st.2 (.inr ⟨core.adrsToKey a, a, ha, rfl⟩) := by
  simp [cellValue, childCell_inr core ha]

private theorem forall₂_filterMap {α β γ : Type} {f : α → Option β} {g : β → Option γ} :
    ∀ {l : List α} {vs : List γ}, List.Forall₂ (fun a v ↦ (f a).bind g = some v) l vs →
      List.Forall₂ (fun b v ↦ g b = some v) (l.filterMap f) vs
  | _, _, .nil => .nil
  | _, _, .cons h hs => by
    obtain ⟨b, hb, hg⟩ := Option.bind_eq_some_iff.1 h
    rw [List.filterMap_cons_some hb]
    exact .cons hg (forall₂_filterMap hs)

/-- A ledger node whose structural children are drawn at `vs` has children values `vs`. -/
private theorem childVals_of_forall₂ (hd : core.KeyDiscipline vp) {a : Adrs}
    (ha : a ∈ constructionAddresses vp) {vs : List core.Y}
    (h : List.Forall₂ (fun b v ↦ cellValue st b = some v) (childAdrs vp a) vs) :
    (slhGraph core pkSeed).childVals st ⟨core.adrsToKey a, a, ha, rfl⟩ = some vs := by
  rw [CanonicalGraph.childVals_eq_some_iff,
    hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed (nodeKeyOf_of_mem core ha)]
  exact forall₂_filterMap h

/-- A ledger node whose structural children are drawn at `vs` reads its label at `vs`. -/
private theorem merge_fst_thash_of_forall₂ (hd : core.KeyDiscipline vp) {a : Adrs}
    (ha : a ∈ constructionAddresses vp) {vs : List core.Y}
    (h : List.Forall₂ (fun b v ↦ cellValue st b = some v) (childAdrs vp a) vs) :
    𝒞[e, pkSeed, s, st] (.thash pkSeed (core.adrsToKey a) vs) = cellValue st (.inr a) :=
  (merge_fst_thash_of_childVals_eq_some hd.keySeparated (childVals_of_forall₂ hd ha h)).trans
    (cellValue_inr ha).symm

private theorem forall₂_map_range {n : ℕ} {P : Adrs ⊕ Adrs → core.Y → Prop}
    {f : ℕ → Adrs ⊕ Adrs} {v : Vector core.Y n} (h : ∀ i : Fin n, P (f i) v[i]) :
    List.Forall₂ P ((List.range n).map f) v.toList :=
  List.forall₂_iff_get.2 ⟨by simp, fun i h₁ _ ↦ by
    simpa using h ⟨i, by simpa using h₁⟩⟩

private theorem cellValue_inl_of_oracleSecret {b : Adrs} (hb : b.IsSecretKey) {x : core.Y}
    (hx : simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl (𝒮[e, pkSeed, s] b) = some x) :
    cellValue st (.inl b) = some x := by
  simpa [cellValue, childCell_inl core hb] using
    (simulateQ_toPartialImpl_oracleSecret_merge hb).symm.trans hx

/-- The children of a Merkle node at height `z + 1` whose cells are the height-`z` cells of a
reader `R`: when `R` reads `l` and `r` at the two children, they are drawn at `[l, r]`. -/
private theorem forall₂_childAdrs_succ {cell : ℕ → ℕ → Adrs} {R : ℕ → ℕ → Option core.Y}
    {z t : ℕ} {l r : core.Y}
    (hch : childAdrs vp (cell (z + 1) t) = [.inr (cell z (2 * t)), .inr (cell z (2 * t + 1))])
    (ih : ∀ {i v}, cell z i ∈ constructionAddresses vp → R z i = some v →
      cellValue st (.inr (cell z i)) = some v)
    (ha : cell (z + 1) t ∈ constructionAddresses vp) (hl : R z (2 * t) = some l)
    (hr : R z (2 * t + 1) = some r) :
    List.Forall₂ (fun b v ↦ cellValue st b = some v) (childAdrs vp (cell (z + 1) t)) [l, r] := by
  have hm := fun b (hb : .inr b ∈ childAdrs vp (cell (z + 1) t)) ↦
    mem_constructionAddresses_of_inr_mem_childAdrs ha hb
  rw [hch] at hm ⊢
  exact .cons (ih (hm _ (by simp)) hl) (.cons (ih (hm _ (by simp)) hr) .nil)

/-! ## WOTS+ -/

/-- The children of a chain step are drawn at the value of the chain prefix below it. -/
private theorem forall₂_childAdrs_of_chain? (hd : core.KeyDiscipline vp) {adrs : Adrs} {i : ℕ}
    {x : core.Y} (hx : cellValue st (.inl (wotsSkAdrs adrs i)) = some x) :
    ∀ {t : ℕ} {v : core.Y}, (wotsChainAdrs adrs i).setHashAddress t ∈ constructionAddresses vp →
      chain? core 𝒞[e, pkSeed, s, st] pkSeed (wotsChainAdrs adrs i) x 0 t = some v →
      List.Forall₂ (fun b v ↦ cellValue st b = some v)
        (childAdrs vp ((wotsChainAdrs adrs i).setHashAddress t)) [v]
  | 0, v, _, h => by
    obtain rfl : x = v := Option.some_inj.1 ((chain?_zero core _ pkSeed _ x 0).symm.trans h)
    rw [childAdrs_wotsChainAdrs_setHashAddress_zero]
    exact .cons hx .nil
  | t + 1, v, hmem, h => by
    obtain ⟨z, hz, hv⟩ := (chain?_succ_eq_some_iff core _ pkSeed _ x 0 t).1 h
    rw [Nat.zero_add] at hv
    have hmem' := mem_constructionAddresses_of_inr_mem_childAdrs hmem
      (by rw [childAdrs_wotsChainAdrs_setHashAddress_succ]; exact List.mem_singleton_self _)
    rw [childAdrs_wotsChainAdrs_setHashAddress_succ]
    exact .cons ((merge_fst_thash_of_forall₂ hd hmem'
      (forall₂_childAdrs_of_chain? hd hx hmem' hz)).symm.trans hv) .nil

/-- The tops of the chains at `adrs` are the drawn labels of the steps at hash address `w - 2`. -/
private theorem forall₂_childAdrs_wotsPkAdrs (hd : core.KeyDiscipline vp) {adrs : Adrs}
    {tops : Vector core.Y vp.params.len} (hmem : wotsPkAdrs adrs ∈ constructionAddresses vp)
    (h : wotsPkGenTopsWithSecret? core 𝒞[e, pkSeed, s, st] 𝒮[e, pkSeed, s] pkSeed adrs =
      some tops) :
    List.Forall₂ (fun b v ↦ cellValue st b = some v) (childAdrs vp (wotsPkAdrs adrs))
      tops.toList := by
  have hw : 2 ≤ vp.params.w := Nat.one_lt_two_pow vp.valid.lgw_pos.ne'
  rw [childAdrs_wotsPkAdrs]
  refine forall₂_map_range fun i ↦ ?_
  obtain ⟨x, hx, hc⟩ := (wotsPkGenTopsWithSecret?_eq_some_iff core _ _ pkSeed adrs).1 h i
  have hmem' := mem_constructionAddresses_of_inr_mem_childAdrs hmem
    (by rw [childAdrs_wotsPkAdrs]; exact List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)
  rw [show vp.params.w - 1 = vp.params.w - 2 + 1 by omega] at hc
  obtain ⟨z, hz, hv⟩ := (chain?_succ_eq_some_iff core _ pkSeed _ x 0 _).1 hc
  rw [Nat.zero_add] at hv
  exact (merge_fst_thash_of_forall₂ hd hmem' (forall₂_childAdrs_of_chain? hd
    (cellValue_inl_of_oracleSecret (Adrs.isSecretKey_wotsSkAdrs _ _) hx) hmem' hz)).symm.trans hv

/-- **WOTS+ chain step.** If the chain of `adrs` and `i` from the secret read `x` reads `v` after
`t` steps, the children of the step at hash address `t` are drawn at `[v]`. -/
theorem childVals_eq_some_of_chain? (hd : core.KeyDiscipline vp) {adrs : Adrs} {i t : ℕ}
    {x v : core.Y} (hmem : (wotsChainAdrs adrs i).setHashAddress t ∈ constructionAddresses vp)
    (hx : simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl
      (𝒮[e, pkSeed, s] (wotsSkAdrs adrs i)) = some x)
    (h : chain? core 𝒞[e, pkSeed, s, st] pkSeed (wotsChainAdrs adrs i) x 0 t = some v) :
    (slhGraph core pkSeed).childVals st
      ⟨core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress t), _, hmem, rfl⟩ = some [v] :=
  childVals_of_forall₂ hd hmem (forall₂_childAdrs_of_chain? hd
    (cellValue_inl_of_oracleSecret (Adrs.isSecretKey_wotsSkAdrs adrs i) hx) hmem h)

/-! ## XMSS -/

/-- The address of the XMSS node at height `z` and index `t` of the tree at `adrs`; at height `0`
it is the WOTS+ public-key compression of leaf `t`. -/
private def xmssCellAdrs (adrs : Adrs) : ℕ → ℕ → Adrs
  | 0, t => wotsPkAdrs (wotsLeafAdrs adrs t)
  | z + 1, t => xmssNodeAdrs adrs (z + 1) t

private theorem childAdrs_xmssNodeAdrs_succ (adrs : Adrs) (z t : ℕ) :
    childAdrs vp (xmssCellAdrs adrs (z + 1) t) =
      [.inr (xmssCellAdrs adrs z (2 * t)), .inr (xmssCellAdrs adrs z (2 * t + 1))] := by
  cases z with
  | zero => exact childAdrs_xmssNodeAdrs_one vp adrs t
  | succ z => exact childAdrs_xmssNodeAdrs vp (by omega) adrs t

private theorem cellValue_of_xmssNodeWithSecret? (hd : core.KeyDiscipline vp) {adrs : Adrs} :
    ∀ {z t : ℕ} {v : core.Y}, xmssCellAdrs adrs z t ∈ constructionAddresses vp →
      xmssNodeWithSecret? core 𝒞[e, pkSeed, s, st] 𝒮[e, pkSeed, s] pkSeed adrs z t = some v →
      cellValue st (.inr (xmssCellAdrs adrs z t)) = some v
  | 0, t, v, hmem, h => by
    simp only [xmssNodeWithSecret?, xmssNodeWithSecret, PerfectMerkleTree.merkleRootM,
      xmssLeafWithSecret, wotsPkGenWithSecret, simulateQ_bind_eq_some_iff,
      simulateQ_toPartialImpl_tl] at h
    obtain ⟨tops, htops, hv⟩ := h
    exact (merge_fst_thash_of_forall₂ hd hmem
      (forall₂_childAdrs_wotsPkAdrs hd hmem htops)).symm.trans hv
  | z + 1, t, v, hmem, h => by
    obtain ⟨l, r, hl, hr, hv⟩ :=
      (PerfectMerkleTree.simulateQ_merkleRootM_succ_eq_some_iff _ _ _ z t).1 h
    rw [xmssNodeHashWith, simulateQ_toPartialImpl_h] at hv
    exact (merge_fst_thash_of_forall₂ hd hmem (forall₂_childAdrs_succ
      (childAdrs_xmssNodeAdrs_succ adrs z t) (cellValue_of_xmssNodeWithSecret? hd) hmem hl
      hr)).symm.trans hv

/-- **XMSS root.** If the honest XMSS root at `adrs` reads `v`, `v` is the drawn label of the
node at `xmssNodeAdrs adrs hp 0`. -/
theorem label_of_xmssRootWithSecret? (hd : core.KeyDiscipline vp) {adrs : Adrs} {v : core.Y}
    (hmem : xmssNodeAdrs adrs vp.params.hp 0 ∈ constructionAddresses vp)
    (h : xmssRootWithSecret? core 𝒞[e, pkSeed, s, st] 𝒮[e, pkSeed, s] pkSeed adrs = some v) :
    st.2 (.inr ⟨core.adrsToKey (xmssNodeAdrs adrs vp.params.hp 0), _, hmem, rfl⟩) = some v := by
  have hp := vp.valid.hp_pos
  unfold xmssRootWithSecret? xmssRootWithSecret at h
  generalize vp.params.hp = n at hp hmem h ⊢
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  exact (cellValue_inr hmem).symm.trans
    (cellValue_of_xmssNodeWithSecret? hd (adrs := adrs) (z := z + 1) hmem h)

/-! ## FORS -/

/-- **FORS leaf.** If the secret of global leaf `t` at `adrs` reads `x`, the children of the leaf
at `forsNodeAdrs adrs 0 t` are drawn at `[x]`. -/
theorem childVals_eq_some_of_forsSkAdrs (hd : core.KeyDiscipline vp) {adrs : Adrs} {t : ℕ}
    {x : core.Y} (hmem : forsNodeAdrs adrs 0 t ∈ constructionAddresses vp)
    (hx : simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl
      (𝒮[e, pkSeed, s] (forsSkAdrs adrs t)) = some x) :
    (slhGraph core pkSeed).childVals st ⟨core.adrsToKey (forsNodeAdrs adrs 0 t), _, hmem, rfl⟩ =
      some [x] := by
  refine childVals_of_forall₂ hd hmem ?_
  rw [childAdrs_forsNodeAdrs_zero]
  exact .cons (cellValue_inl_of_oracleSecret (Adrs.isSecretKey_forsSkAdrs adrs t) hx) .nil

private theorem cellValue_of_forsNodeWithSecret? (hd : core.KeyDiscipline vp) {adrs : Adrs} :
    ∀ {z t : ℕ} {v : core.Y}, forsNodeAdrs adrs z t ∈ constructionAddresses vp →
      forsNodeWithSecret? core 𝒞[e, pkSeed, s, st] 𝒮[e, pkSeed, s] pkSeed adrs z t = some v →
      cellValue st (.inr (forsNodeAdrs adrs z t)) = some v
  | 0, t, v, hmem, h => by
    simp only [forsNodeWithSecret?, PerfectMerkleTree.merkleRootM, forsLeafWithSecret,
      simulateQ_bind_eq_some_iff, simulateQ_toPartialImpl_f] at h
    obtain ⟨x, hx, hv⟩ := h
    exact (cellValue_inr hmem).trans ((merge_fst_thash_of_childVals_eq_some hd.keySeparated
      (childVals_eq_some_of_forsSkAdrs hd hmem hx)).symm.trans hv)
  | z + 1, t, v, hmem, h => by
    obtain ⟨l, r, hl, hr, hv⟩ :=
      (PerfectMerkleTree.simulateQ_merkleRootM_succ_eq_some_iff _ _ _ z t).1 h
    rw [forsNodeHashWith, simulateQ_toPartialImpl_h] at hv
    exact (merge_fst_thash_of_forall₂ hd hmem (forall₂_childAdrs_succ
      (childAdrs_forsNodeAdrs vp (Nat.succ_pos z) adrs t) (cellValue_of_forsNodeWithSecret? hd)
      hmem hl hr)).symm.trans hv

private theorem forall₂_childAdrs_forsPkAdrs (hd : core.KeyDiscipline vp) {adrs : Adrs}
    {roots : Vector core.Y vp.params.k} (hmem : forsPkAdrs adrs ∈ constructionAddresses vp)
    (h : ∀ i : Fin vp.params.k, forsNodeWithSecret? core 𝒞[e, pkSeed, s, st]
      𝒮[e, pkSeed, s] pkSeed adrs vp.params.a i.val = some roots[i]) :
    List.Forall₂ (fun b v ↦ cellValue st b = some v) (childAdrs vp (forsPkAdrs adrs))
      roots.toList := by
  rw [childAdrs_forsPkAdrs]
  exact forall₂_map_range fun i ↦ cellValue_of_forsNodeWithSecret? hd
    (mem_constructionAddresses_of_inr_mem_childAdrs hmem (by
      rw [childAdrs_forsPkAdrs]; exact List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)) (h i)

/-- **FORS public key.** If the honest FORS public key at `adrs` reads `v`, `v` is the drawn
label of the roots compression at `forsPkAdrs adrs`. -/
theorem label_of_forsPkGenWithSecret? (hd : core.KeyDiscipline vp) {adrs : Adrs} {v : core.Y}
    (hmem : forsPkAdrs adrs ∈ constructionAddresses vp)
    (h : forsPkGenWithSecret? core 𝒞[e, pkSeed, s, st] 𝒮[e, pkSeed, s] pkSeed adrs = some v) :
    st.2 (.inr ⟨core.adrsToKey (forsPkAdrs adrs), _, hmem, rfl⟩) = some v := by
  obtain ⟨roots, hroots, hv⟩ := (forsPkGenWithSecret?_eq_some_iff core _ _ pkSeed adrs).1 h
  exact (cellValue_inr hmem).symm.trans ((merge_fst_thash_of_forall₂ hd hmem
    (forall₂_childAdrs_forsPkAdrs hd hmem hroots)).symm.trans hv)

/-! ## Honest messages, honest entries and target collisions -/

/-- **Honest message.** If the honest message signed at `pos` reads `m`, `m` is the drawn label
of the node at `msgAdrs pos`. -/
theorem label_of_honestMessage? (hd : core.KeyDiscipline vp) (pos : LayerPosition vp) {m : core.Y}
    (h : honestMessage? 𝒞[e, pkSeed, s, st] 𝒮[e, pkSeed, s] pkSeed pos = some m) :
    st.2 (.inr ⟨core.adrsToKey (msgAdrs pos), _, msgAdrs_mem_constructionAddresses pos, rfl⟩) =
      some m := by
  unfold honestMessage? at h
  split_ifs at h with h0
  · exact Eq.trans (by congr 3; simp [msgAdrs, h0]) (label_of_forsPkGenWithSecret? hd
      (forsPkAdrs_forsInstanceAdrs_mem_constructionAddresses pos h0) h)
  · exact Eq.trans (by congr 3; simp [msgAdrs, h0]) (label_of_xmssRootWithSecret? hd
      (xmssNodeAdrs_childTreeAdrs_mem_constructionAddresses pos (Nat.pos_of_ne_zero h0)) h)

/-- **Honest entries are node points.** Every honest entry of the merged cache at the
oracle-backed provider is the point of a node at its drawn children values. -/
theorem exists_childVals_eq_some_of_honestEntry (hd : core.KeyDiscipline vp)
    {t : (publicHashSpec core).Domain}
    (h : HonestEntry 𝒮[e, pkSeed, s] pkSeed 𝒞[e, pkSeed, s, st] t) :
    ∃ κ vs, (slhGraph core pkSeed).childVals st κ = some vs ∧
      (slhGraph core pkSeed).pt κ vs = .inl t := by
  refine match h with
  | .xmssNode adrs (z + 1) i l r _ hmem hl hr => ⟨_, _, childVals_of_forall₂ hd hmem
      (forall₂_childAdrs_succ (cell := xmssCellAdrs adrs) (childAdrs_xmssNodeAdrs_succ adrs z i)
        (cellValue_of_xmssNodeWithSecret? hd) hmem hl hr), rfl⟩
  | .wotsPk adrs tops hmem htops =>
      ⟨_, _, childVals_of_forall₂ hd hmem (forall₂_childAdrs_wotsPkAdrs hd hmem htops), rfl⟩
  | .wotsChain adrs i t x v hmem hx hv => ⟨_, _, childVals_eq_some_of_chain? hd hmem hx hv, rfl⟩
  | .forsLeaf adrs t x hmem hx => ⟨_, _, childVals_eq_some_of_forsSkAdrs hd hmem hx, rfl⟩
  | .forsNode adrs (z + 1) i l r _ hmem hl hr => ⟨_, _, childVals_of_forall₂ hd hmem
      (forall₂_childAdrs_succ (childAdrs_forsNodeAdrs vp (Nat.succ_pos z) adrs i)
        (cellValue_of_forsNodeWithSecret? hd) hmem hl hr), rfl⟩
  | .forsRoots adrs roots hmem hroots => ⟨_, _, childVals_of_forall₂ hd hmem
      (forall₂_childAdrs_forsPkAdrs hd hmem hroots), rfl⟩

/-- **Target collisions are target collisions at node keys.** A target collision of the merged
cache at the oracle-backed provider is a public entry, at the key of a node, equal to the node's
drawn label. -/
theorem tcHazard_of_targetCollision (hd : core.KeyDiscipline vp)
    (h : TargetCollision 𝒮[e, pkSeed, s] pkSeed 𝒞[e, pkSeed, s, st]) :
    (slhNodeKeys core pkSeed).TCHazard st := by
  obtain ⟨key, xs, ys, v, hhon, hne, hx, hy⟩ := h
  obtain ⟨κ, vs, hκ, hpt⟩ := exists_childVals_eq_some_of_honestEntry hd hhon
  simp only [slhGraph_pt, Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at hpt
  obtain ⟨rfl, rfl⟩ := hpt
  refine ⟨.inl (.thash pkSeed κ.1 ys), κ, v,
    (slhNodeKeys_node_thash_eq_some_iff core).2 ⟨rfl, rfl⟩, ?_, ?_⟩
  · exact (merge_fst_thash_of_childVals_eq_some hd.keySeparated hκ).symm.trans hx
  · exact (merge_fst_thash_of_childVals_ne hd.keySeparated
      fun h ↦ hne (Option.some_inj.1 (hκ.symm.trans h))).symm.trans hy

end SLHDSA.Security
