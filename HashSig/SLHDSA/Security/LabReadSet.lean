/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.HiddenCells
import HashSig.SLHDSA.Security.AddressKeys
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# The read sets of the lab components

In the deferred game over the SLH-DSA graph, a lab component draws only the cells it reads: the
labels of the nodes its callbacks read, the secrets it derives, and the cell its touch-then-read
chains read; touches only pend their cells (`CanonicalGraph.ReadsWithin`). This module shows that
none of these is a hidden cell (`HashSig.SLHDSA.Security.HiddenCells`), given what the component
signs.

* **Always visible.** Key generation, the XMSS leaves and nodes, the XMSS authentication paths,
  the FORS leaves and nodes, and FORS public-key recovery read the tops of the WOTS+ chains and
  nodes of other types, never a hidden cell, for every set of digests and every state
  (`readsUnhidden_labKeygen`, `readsUnhidden_intrinsicAuthPathM_labXmssLeaf`,
  `readsUnhidden_forsPkFromSigWith`).
* **WOTS+ at a used position.** At a position some digest uses, whose honest message `m` is drawn,
  WOTS+ signing on `m` reads step `chainStepsCore core m i` of chain `i`, and recovery from a
  signature on `m` reads the steps above it (`readsUnhidden_labXmssSign`,
  `readsUnhidden_xmssPkFromSigWith`).
* **FORS signing** on a digest of the set reads the secrets that digest opens
  (`readsUnhidden_labForsSign`).
* **Signing's other queries.** The `H_msg` query is at no node's point, and the randomizer is a
  derivation that is not a secret (`readsUnhidden_hmsg`, `readsUnhidden_randomizer`).

`ReadsUnhidden pkSeed U st oa` states that every query of `oa` reads within the complement of the
hidden cells of `U` at `st`; by `CanonicalGraph.cell_eq_of_mem_support_simulateQ_deferredImpl` a
run of `oa` in the deferred game then leaves every hidden cell as it found it.

## References

- NIST FIPS 205, Algorithms 6–7 (WOTS+), 9–11 (XMSS), 15–17 (FORS)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

variable (core) in
/-- Every query of the lab program `oa` reads, in the deferred game over the graph at `pkSeed`, no
hidden cell of the digests `U` at the state `st`. -/
abbrev ReadsUnhidden (pkSeed : core.PkSeed) (U : Bytes vp.params.m → Prop)
    (st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y) {α : Type}
    (oa : OracleComp (labSpec core) α) : Prop :=
  AllQueriesSatisfy oa ((slhGraph core pkSeed).ReadsWithin (hiddenCells core U st)ᶜ)

/-- A WOTS+ chain applies its hash at the addresses `start + j` for `j < steps`, so it satisfies a
predicate closed under `bind` as soon as each of those hash calls does. -/
theorem chainWith_pred_of_lt {Y : Type} {m : Type → Type*} [Monad m]
    (Q : ∀ {α : Type}, m α → Prop) (hpure : ∀ {α : Type} (x : α), Q (pure x))
    (hbind : ∀ {α β : Type} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
    {hash : Adrs → Y → m Y} {adrs : Adrs} (x : Y) (start : ℕ) :
    ∀ steps, (∀ j < steps, ∀ y, Q (hash (adrs.setHashAddress (start + j)) y)) →
      Q (chainWith hash adrs x start steps)
  | 0, _ => hpure _
  | s + 1, h => hbind _ _ (chainWith_pred_of_lt Q hpure hbind x start s fun j hj ↦ h j (by omega))
      fun y ↦ h s (by omega) y

/-! ## The public and randomizer queries of signing -/

/-- The `H_msg` query reads no hidden cell. -/
theorem readsUnhidden_hmsg (pkSeed : core.PkSeed) {U : Bytes vp.params.m → Prop}
    {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y} (r : core.Y)
    (pk : core.PkSeed) (root : core.Y) (msg : List Byte) :
    ReadsUnhidden core pkSeed U st
      (PublicHash.hmsg core r pk root msg : OracleComp (labSpec core) _) :=
  (allQueriesSatisfy_query_iff _ _).2 fun _ _ h ↦ by simp at h

/-- Drawing the randomizer reads no hidden cell: its derivation is not a secret. -/
theorem readsUnhidden_randomizer (pkSeed : core.PkSeed) {U : Bytes vp.params.m → Prop}
    {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}
    (o : ProbComp core.Y) (msg : List Byte) :
    ReadsUnhidden core pkSeed U st (liftComp ((do
      let addrnd ← (o : ProbComp core.Y)
      query (spec := deriveSpec core) (.inr (.inr (addrnd, msg)))) :
        OracleComp (deriveSpec core) core.Y) (labSpec core)) := by
  unfold ReadsUnhidden
  rw [liftComp_def]
  refine AllQueriesSatisfy.simulateQ
    (P := fun t ↦ (slhGraph core pkSeed).ReadsWithin (hiddenCells core U st)ᶜ (.inl t)) ?_ ?_
  · refine allQueriesSatisfy_bind ?_ fun _ ↦
      (allQueriesSatisfy_query_iff _ _).2 (inl_inr_not_mem_hiddenCells _)
    classical
    rw [← isQueryBoundP_zero_iff]
    exact isQueryBoundP_liftM_withDerivations (fun _ h ↦ h trivial) _
  · rintro ((n | t) | x) h <;> exact (allQueriesSatisfy_query_iff _ _).2 h

variable [SampleableType core.Y] (pkSeed : core.PkSeed) {U : Bytes vp.params.m → Prop}
  {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}

/-! ## Reads of cells -/

/-- A read of the cell of an in-range structural child that is not hidden reads no hidden
cell. -/
theorem readsUnhidden_readCell_childCell (hd : core.KeyDiscipline vp) {b : Adrs ⊕ Adrs}
    (h : ∀ c, childCell core b = some c → AddressFacts vp (b.elim id id) ∧
      ¬HiddenChild core U st b) :
    ReadsUnhidden core pkSeed U st (readCell (childCell core b)) :=
  (slhGraph core pkSeed).allQueriesSatisfy_readsWithin_readCell fun c hc ↦
    not_mem_hiddenCells_of_childCell_eq_some hd hc (h c hc).1 (h c hc).2

/-- The node value at an address that is not hidden reads no hidden cell. -/
theorem readsUnhidden_labNode (hd : core.KeyDiscipline vp) {a : Adrs}
    (h : ¬HiddenChild core U st (.inr a)) : ReadsUnhidden core pkSeed U st (labNode core a) :=
  readsUnhidden_readCell_childCell pkSeed hd fun _ hc ↦
    ⟨addressFacts_of_childCell_inr_eq_some hd.canonicalAddressBounds hc, h⟩

/-- The node value at an address of a type other than `WOTS_HASH` reads no hidden cell. -/
theorem readsUnhidden_labNode_of_type_ne_zero (hd : core.KeyDiscipline vp) {a : Adrs}
    (h : a.type ≠ 0) : ReadsUnhidden core pkSeed U st (labNode core a) :=
  readsUnhidden_labNode pkSeed hd (not_hiddenChild_inr (.inl h))

/-- A touch-then-read whose read cell is the cell of an in-range structural child that is not
hidden reads no hidden cell. -/
theorem readsUnhidden_touchRead (hd : core.KeyDiscipline vp)
    {cell : ℕ → Option (DeriveQuery core ⊕ NodeKey core)} {s : ℕ} {b : Adrs ⊕ Adrs}
    (hcell : cell s = childCell core b)
    (h : ∀ c, childCell core b = some c → AddressFacts vp (b.elim id id) ∧
      ¬HiddenChild core U st b) :
    ReadsUnhidden core pkSeed U st (touchRead cell s) :=
  (slhGraph core pkSeed).allQueriesSatisfy_readsWithin_touchRead fun c hc ↦
    not_mem_hiddenCells_of_childCell_eq_some hd (hcell ▸ hc) (h c (hcell ▸ hc)).1
      (h c (hcell ▸ hc)).2

/-! ## Components that read no hidden cell at any state -/

/-- The top of a lab WOTS+ chain reads no hidden cell. -/
theorem readsUnhidden_labChain_top (hd : core.KeyDiscipline vp) (adrs : Adrs) (i : ℕ) :
    ReadsUnhidden core pkSeed U st (labChain core adrs i (vp.params.w - 1)) := by
  have hw : vp.params.w - 1 = vp.params.w - 2 + 1 := by
    have : 2 ≤ vp.params.w := Nat.one_lt_two_pow vp.valid.lgw_pos.ne'
    omega
  rw [labChain, hw]
  exact readsUnhidden_touchRead pkSeed hd
    (b := .inr ((wotsChainAdrs adrs i).setHashAddress (vp.params.w - 2))) rfl fun _ hc ↦
      ⟨addressFacts_of_childCell_inr_eq_some hd.canonicalAddressBounds hc,
        not_hiddenChild_inr (.inr (by rw [wotsChainAdrs_setHashAddress_eq]))⟩

/-- The lab WOTS+ chain tops read no hidden cell. -/
theorem readsUnhidden_labWotsPkGenTops (hd : core.KeyDiscipline vp) (adrs : Adrs) :
    ReadsUnhidden core pkSeed U st (labWotsPkGenTops core adrs) :=
  allQueriesSatisfy_ofFnM _ fun _ ↦ readsUnhidden_labChain_top pkSeed hd _ _

/-- A lab XMSS leaf reads no hidden cell. -/
theorem readsUnhidden_labXmssLeaf (hd : core.KeyDiscipline vp) (adrs : Adrs) (t : ℕ) :
    ReadsUnhidden core pkSeed U st (labXmssLeaf core adrs t) :=
  allQueriesSatisfy_bind (readsUnhidden_labWotsPkGenTops pkSeed hd _) fun _ ↦
    readsUnhidden_labNode_of_type_ne_zero pkSeed hd (by simp [wotsPkAdrs_eq])

/-- An XMSS node hash at the lab callbacks reads no hidden cell. -/
theorem readsUnhidden_xmssNodeHashWith (hd : core.KeyDiscipline vp) (adrs : Adrs) (z t : ℕ)
    (l r : core.Y) :
    ReadsUnhidden core pkSeed U st (xmssNodeHashWith (labH core) adrs z t l r) :=
  readsUnhidden_labNode_of_type_ne_zero pkSeed hd (by simp [xmssNodeAdrs_eq])

/-- A FORS node hash at the lab callbacks reads no hidden cell. -/
theorem readsUnhidden_forsNodeHashWith (hd : core.KeyDiscipline vp) (adrs : Adrs) (z t : ℕ)
    (l r : core.Y) :
    ReadsUnhidden core pkSeed U st (forsNodeHashWith (labH core) adrs z t l r) :=
  readsUnhidden_labNode_of_type_ne_zero pkSeed hd (by simp [forsNodeAdrs_eq])

/-- A lab XMSS node reads no hidden cell. -/
theorem readsUnhidden_labXmssNode (hd : core.KeyDiscipline vp) (adrs : Adrs) (z t : ℕ) :
    ReadsUnhidden core pkSeed U st (labXmssNode core adrs z t) :=
  PerfectMerkleTree.merkleRootM_pred_of_subtree (ReadsUnhidden core pkSeed U st)
    (fun _ _ ↦ allQueriesSatisfy_bind) _ _ z t
    (fun _ _ ↦ readsUnhidden_labXmssLeaf pkSeed hd _ _)
    fun _ _ _ _ _ _ _ ↦ readsUnhidden_xmssNodeHashWith pkSeed hd _ _ _ _ _

/-- Lab key generation reads no hidden cell. -/
theorem readsUnhidden_labKeygen (hd : core.KeyDiscipline vp) :
    ReadsUnhidden core pkSeed U st (labKeygen core) :=
  readsUnhidden_labXmssNode pkSeed hd _ _ _

/-- An XMSS authentication path through the lab tree reads no hidden cell. -/
theorem readsUnhidden_intrinsicAuthPathM_labXmssLeaf (hd : core.KeyDiscipline vp) (adrs : Adrs)
    (idx z : ℕ) :
    ReadsUnhidden core pkSeed U st (PerfectMerkleTree.intrinsicAuthPathM (labXmssLeaf core adrs)
      (xmssNodeHashWith (labH core) adrs) idx z) :=
  PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree (ReadsUnhidden core pkSeed U st)
    (fun _ ↦ allQueriesSatisfy_pure _ _) (fun _ _ ↦ allQueriesSatisfy_bind) _ _ idx z
    (fun _ _ ↦ readsUnhidden_labXmssLeaf pkSeed hd _ _)
    fun _ _ _ _ _ _ _ ↦ readsUnhidden_xmssNodeHashWith pkSeed hd _ _ _ _ _

/-- A lab FORS leaf reads no hidden cell. -/
theorem readsUnhidden_labForsLeaf (hd : core.KeyDiscipline vp) (adrs : Adrs) (t : ℕ) :
    ReadsUnhidden core pkSeed U st (labForsLeaf core adrs t) :=
  readsUnhidden_touchRead pkSeed hd (b := .inr (forsNodeAdrs adrs 0 t)) rfl fun _ hc ↦
    ⟨addressFacts_of_childCell_inr_eq_some hd.canonicalAddressBounds hc,
      not_hiddenChild_inr (.inl (by simp [forsNodeAdrs_eq]))⟩

/-- A FORS authentication path through the lab tree reads no hidden cell. -/
theorem readsUnhidden_intrinsicAuthPathM_labForsLeaf (hd : core.KeyDiscipline vp) (adrs : Adrs)
    (idx z : ℕ) :
    ReadsUnhidden core pkSeed U st (PerfectMerkleTree.intrinsicAuthPathM (labForsLeaf core adrs)
      (forsNodeHashWith (labH core) adrs) idx z) :=
  PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree (ReadsUnhidden core pkSeed U st)
    (fun _ ↦ allQueriesSatisfy_pure _ _) (fun _ _ ↦ allQueriesSatisfy_bind) _ _ idx z
    (fun _ _ ↦ readsUnhidden_labForsLeaf pkSeed hd _ _)
    fun _ _ _ _ _ _ _ ↦ readsUnhidden_forsNodeHashWith pkSeed hd _ _ _ _ _

/-- FORS public-key recovery at the lab callbacks reads no hidden cell. -/
theorem readsUnhidden_forsPkFromSigWith (hd : core.KeyDiscipline vp)
    (sig : ForsSigCore vp.params core) (md : List Byte) (adrs : Adrs) :
    ReadsUnhidden core pkSeed U st
      (forsPkFromSigWith core (labF core) (labH core) (labTl core) sig md adrs) :=
  allQueriesSatisfy_bind (allQueriesSatisfy_ofFnM _ fun _ ↦
    allQueriesSatisfy_bind
      (readsUnhidden_labNode_of_type_ne_zero pkSeed hd (by simp [forsNodeAdrs_eq]))
      fun _ ↦ PerfectMerkleTree.climbM_pred_of_ancestors (ReadsUnhidden core pkSeed U st)
        (fun _ ↦ allQueriesSatisfy_pure _ _) (fun _ _ ↦ allQueriesSatisfy_bind) _ _ _ _
        fun _ _ _ _ _ ↦ readsUnhidden_forsNodeHashWith pkSeed hd _ _ _ _ _)
    fun _ ↦ readsUnhidden_labNode_of_type_ne_zero pkSeed hd (by simp [forsPkAdrs_eq])

/-! ## WOTS+ at a used position -/

section Used

variable {pos : LayerPosition vp} (hpos : UsedPosition U pos) {msg : core.Y}
  (hmsg : st.2 (msgCell core pos) = some msg)

include hpos hmsg in
/-- At a position used by `U` whose honest message `msg` is drawn, the lab WOTS+ signature on
`msg` reads no hidden cell. -/
theorem readsUnhidden_labWotsSign (hd : core.KeyDiscipline vp) :
    ReadsUnhidden core pkSeed U st (labWotsSign core msg (wotsInstanceAdrs pos)) :=
  allQueriesSatisfy_ofFnM _ fun i ↦
    readsUnhidden_touchRead pkSeed hd (pathCell_wotsInstanceAdrs core pos i.val _) fun _ _ ↦
      ⟨addressFacts_chainChild hd.canonicalAddressBounds pos i (chainStepsCore_le core msg i.val),
        not_hiddenChild_chainChild hpos hmsg le_rfl⟩

include hpos hmsg in
/-- At a position used by `U` whose honest message `msg` is drawn, the lab XMSS signature on `msg`
at that position reads no hidden cell. -/
theorem readsUnhidden_labXmssSign (hd : core.KeyDiscipline vp) :
    ReadsUnhidden core pkSeed U st (labXmssSign core msg pos.toAdrs pos.leaf.val) :=
  allQueriesSatisfy_bind (readsUnhidden_intrinsicAuthPathM_labXmssLeaf pkSeed hd _ _ _) fun _ ↦
    allQueriesSatisfy_bind (readsUnhidden_labWotsSign pkSeed hpos hmsg hd) fun _ ↦
      allQueriesSatisfy_pure _ _

include hpos hmsg in
/-- At a position used by `U` whose honest message `msg` is drawn, WOTS+ public-key recovery from
a signature on `msg` at the lab callbacks reads no hidden cell: on each chain it reads the steps
above the one `msg` selects. -/
theorem readsUnhidden_wotsPkFromSigWith (hd : core.KeyDiscipline vp)
    (sig : WotsSig vp.params core) :
    ReadsUnhidden core pkSeed U st
      (wotsPkFromSigWith core (labF core) (labTl core) sig msg (wotsInstanceAdrs pos)) :=
  allQueriesSatisfy_bind (allQueriesSatisfy_ofFnM _ fun i ↦
    chainWith_pred_of_lt (ReadsUnhidden core pkSeed U st) (fun _ ↦ allQueriesSatisfy_pure _ _)
      (fun _ _ ↦ allQueriesSatisfy_bind) _ _ _ fun j _ _ ↦
        readsUnhidden_labNode pkSeed hd
          (not_hiddenChild_chainChild (i := i.val) (t := chainStepsCore core msg i.val + j + 1)
            hpos hmsg (by omega)))
    fun _ ↦ readsUnhidden_labNode_of_type_ne_zero pkSeed hd (by simp [wotsPkAdrs_eq])

include hpos hmsg in
/-- At a position used by `U` whose honest message `msg` is drawn, XMSS root recovery from a
signature on `msg` at that position, at the lab callbacks, reads no hidden cell. -/
theorem readsUnhidden_xmssPkFromSigWith (hd : core.KeyDiscipline vp)
    (sig : XmssSig vp.params core) :
    ReadsUnhidden core pkSeed U st (xmssPkFromSigWith core (labF core) (labTl core) (labH core)
      pos.leaf.val sig msg pos.toAdrs) :=
  allQueriesSatisfy_bind (readsUnhidden_wotsPkFromSigWith pkSeed hpos hmsg hd sig.wots) fun _ ↦
    PerfectMerkleTree.climbM_pred_of_ancestors (ReadsUnhidden core pkSeed U st)
      (fun _ ↦ allQueriesSatisfy_pure _ _) (fun _ _ ↦ allQueriesSatisfy_bind) _ _ _ _
      fun _ _ _ _ _ ↦ readsUnhidden_xmssNodeHashWith pkSeed hd _ _ _ _ _

end Used

/-! ## FORS signing on a digest of the set -/

/-- The lab secret at a secret-key address reads the cell of that address. -/
theorem labSecret_eq_readCell_childCell {a : Adrs} (h : a.IsSecretKey) :
    labSecret core a = readCell (childCell core (.inl a)) := by
  rw [labSecret_of_isSecretKey core h, childCell_inl core h]

/-- FORS signing in the lab on a digest of `U` reads no hidden cell: it reads the secrets that
digest opens. -/
theorem readsUnhidden_labForsSign (hd : core.KeyDiscipline vp) {d : Bytes vp.params.m}
    (hU : U d) :
    ReadsUnhidden core pkSeed U st (labForsSign core (splitDigest vp.params d).md.toList
      (splitDigest vp.params d).forsAdrs) := by
  refine allQueriesSatisfy_ofFnM _ fun i ↦ allQueriesSatisfy_bind
    (readsUnhidden_intrinsicAuthPathM_labForsLeaf pkSeed hd _ _ _) fun _ ↦
      allQueriesSatisfy_bind ?_ fun _ ↦ allQueriesSatisfy_pure _ _
  rw [labSecret_eq_readCell_childCell (Adrs.isSecretKey_forsSkAdrs _ _), ← forsSigLeafIndex_eq]
  exact readsUnhidden_readCell_childCell pkSeed hd fun _ _ ↦
    ⟨by simpa using (addressFacts_forsSkAdrs hd.canonicalAddressBounds
        (BottomPosition.ofDigestParts vp (splitDigest vp.params d)) (forsSigLeafIndex_lt _ i)),
      not_hiddenChild_inl_forsSkAdrs hU i⟩

end SLHDSA.Security
