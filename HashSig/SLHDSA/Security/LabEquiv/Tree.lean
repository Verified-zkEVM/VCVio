/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabEquiv.Path
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.EqDistTriple
import ToMathlib.Data.List.Forall2

/-!
# Honest and lab WOTS+, XMSS and FORS in the eager game

The honest WOTS+, XMSS and FORS programs over `labSpec core`, with the public tweakable hash and
every secret read by `labSecret`, are related to the lab components of
`HashSig.SLHDSA.Security.LabScheme` by `LabTriple` at every reachable position. Each component is
assembled from the steps of `HashSig.SLHDSA.Security.LabEquiv.Path` by the combinator rules of
`QueryImpl.EqDistTriple` (`Vector.ofFnM`, `merkleRootM`, `intrinsicAuthPathM`, `climbM`), which
carry the relation between each value and the cell holding it.

* **Signing leaves its values in cells.** A WOTS+ signature leaves each chain value in the chain
  cell at its step count, and an authentication path leaves each entry in the cell of its
  sibling node (`XmssSigHolds`, `ForsSigHolds`).
* **Recovery from held values.** Root recovery hashes signature values, which are not produced by
  the recovery itself; from a state in which they are held (`XmssSigHolds`, `ForsSigHolds`),
  every honest hash in the recovery is the draw of a node label, so the honest recovery is
  related to the recovery at the lab callbacks, and the recovered root is held by its cell.
* **Cells of the trees.** Node `(h, i)` of the XMSS tree at `adrs` is held by the cell of
  `xmssCellAdrs adrs h i`: the WOTS+ public key of leaf `i` at height `0`, the tree node above.
  Node `(h, i)` of the FORS trees at `adrs` is held by the cell of `forsNodeAdrs adrs h i`.
-/

public section

open OracleComp OracleSpec PerfectMerkleTree

namespace SLHDSA.Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Cells of the trees -/

/-- The address whose cell holds node `(h, i)` of the XMSS tree at `adrs`: the WOTS+ public key
of leaf `i` at height `0`, and the tree node above. -/
@[expose] def xmssCellAdrs (adrs : Adrs) : ℕ → ℕ → Adrs
  | 0, i => wotsPkAdrs (wotsLeafAdrs adrs i)
  | h + 1, i => xmssNodeAdrs adrs (h + 1) i

/-- The structural children of XMSS node `(h + 1, i)` are the cells of nodes `(h, 2 i)` and
`(h, 2 i + 1)`. -/
theorem map_childCell_childAdrs_xmssNodeAdrs (adrs : Adrs) (h i : ℕ) :
    (childAdrs vp (xmssNodeAdrs adrs (h + 1) i)).map (childCell core) =
      [childCell core (.inr (xmssCellAdrs adrs h (2 * i))),
        childCell core (.inr (xmssCellAdrs adrs h (2 * i + 1)))] := by
  rcases h with _ | h
  · rw [childAdrs_xmssNodeAdrs_one]
    rfl
  · rw [childAdrs_xmssNodeAdrs vp (by omega)]
    rfl

/-- The structural children of FORS node `(h + 1, i)` are the cells of nodes `(h, 2 i)` and
`(h, 2 i + 1)`. -/
theorem map_childCell_childAdrs_forsNodeAdrs (adrs : Adrs) (h i : ℕ) :
    (childAdrs vp (forsNodeAdrs adrs (h + 1) i)).map (childCell core) =
      [childCell core (.inr (forsNodeAdrs adrs h (2 * i))),
        childCell core (.inr (forsNodeAdrs adrs h (2 * i + 1)))] := by
  rw [childAdrs_forsNodeAdrs vp (by omega)]
  rfl

/-- The structural children of a WOTS+ public-key compression are the chain cells at `w - 1`. -/
theorem map_childCell_childAdrs_wotsPkAdrs (adrs : Adrs) :
    (childAdrs vp (wotsPkAdrs adrs)).map (childCell core) =
      (List.range vp.params.len).map fun i ↦ wotsChainCell core adrs i (vp.params.w - 1) := by
  have hw : vp.params.w - 1 = vp.params.w - 2 + 1 := by
    have := Nat.one_lt_two_pow vp.valid.lgw_pos.ne'
    simp only [Params.w]
    omega
  rw [childAdrs_wotsPkAdrs, List.map_map, hw]
  rfl

/-- The structural children of a FORS roots compression are the cells of the `k` tree roots. -/
theorem map_childCell_childAdrs_forsPkAdrs (adrs : Adrs) :
    (childAdrs vp (forsPkAdrs adrs)).map (childCell core) =
      (List.range vp.params.k).map fun i ↦
        childCell core (.inr (forsNodeAdrs adrs vp.params.a i)) := by
  rw [childAdrs_forsPkAdrs, List.map_map]
  rfl

/-- The state holds node `(h, i)` of the XMSS tree at `adrs` at `y`. -/
abbrev XmssHolds (adrs : Adrs) (h i : ℕ) (y : core.Y) (st : LabState core) : Prop :=
  CellHolds core st (childCell core (.inr (xmssCellAdrs adrs h i))) y

/-- The state holds node `(h, i)` of the FORS trees at `adrs` at `y`. -/
abbrev ForsHolds (adrs : Adrs) (h i : ℕ) (y : core.Y) (st : LabState core) : Prop :=
  CellHolds core st (childCell core (.inr (forsNodeAdrs adrs h i))) y

/-- The state holds an XMSS signature at a reachable position on `msg`: each WOTS+ chain value at
the chain cell of its step count, and each authentication-path entry at the cell of its sibling
node. -/
@[expose] def XmssSigHolds (pos : LayerPosition vp) (msg : core.Y) (sig : XmssSig vp.params core)
    (st : LabState core) : Prop :=
  (∀ i : Fin vp.params.len, CellHolds core st
    (wotsChainCell core (wotsInstanceAdrs pos) i (chainStepsCore core msg i)) sig.wots[i]) ∧
  ∀ j (hj : j < vp.params.hp),
    XmssHolds core pos.toAdrs j (sibling (pos.leaf.val / 2 ^ j)) sig.auth[j] st

/-- The state holds a FORS signature on `md` at a reachable bottom position: for each tree, the
opened secret at its cell, and each authentication-path entry at the cell of its sibling node. -/
@[expose] def ForsSigHolds (pos : BottomPosition vp) (md : List Byte)
    (sig : ForsSigCore vp.params core) (st : LabState core) : Prop :=
  ∀ i : Fin vp.params.k,
    CellHolds core st (childCell core (.inl (forsSkAdrs pos.forsAdrs
      (forsLeafIndex vp.params md i)))) sig[i].sk ∧
    ∀ j (hj : j < vp.params.a), ForsHolds core pos.forsAdrs j
      (sibling (forsLeafIndex vp.params md i / 2 ^ j)) sig[i].auth[j] st

variable {core} in
/-- A held XMSS signature stays held as the state grows. -/
theorem XmssSigHolds.mono {pos : LayerPosition vp} {msg : core.Y} {sig : XmssSig vp.params core}
    {st st' : LabState core} (hle : st ≤ st') (h : XmssSigHolds core pos msg sig st) :
    XmssSigHolds core pos msg sig st' :=
  ⟨fun i ↦ (h.1 i).mono hle, fun j hj ↦ (h.2 j hj).mono hle⟩

variable {core} in
/-- A held FORS signature stays held as the state grows. -/
theorem ForsSigHolds.mono {pos : BottomPosition vp} {md : List Byte}
    {sig : ForsSigCore vp.params core} {st st' : LabState core} (hle : st ≤ st')
    (h : ForsSigHolds core pos md sig st) : ForsSigHolds core pos md sig st' :=
  fun i ↦ ⟨(h i).1.mono hle, fun j hj ↦ ((h i).2 j hj).mono hle⟩

variable [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf] [SampleableType (Bytes vp.params.m)]
  (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)

/-! ## WOTS+ -/

section Wots

variable (pos : LayerPosition vp)

include hd in
/-- **WOTS+ chain vectors.** For step counts `steps i ≤ w - 1`, the honest chains of `steps i`
steps from the secrets are related to the lab chains, and each chain cell at its step count then
holds its value. -/
theorem ofFnM_labChain_labTriple (steps : Fin vp.params.len → ℕ)
    (hs : ∀ i, steps i ≤ vp.params.w - 1) :
    LabTriple core pkSeed (fun _ ↦ True)
      (Vector.ofFnM fun i : Fin vp.params.len ↦ do
        let x ← labSecret core (wotsSkAdrs (wotsInstanceAdrs pos) i)
        chainWith (PublicHash.f core pkSeed) (wotsChainAdrs (wotsInstanceAdrs pos) i) x 0
          (steps i))
      (Vector.ofFnM fun i : Fin vp.params.len ↦ labChain core (wotsInstanceAdrs pos) i (steps i))
      fun v st ↦ ∀ i : Fin vp.params.len, CellHolds core st
        (wotsChainCell core (wotsInstanceAdrs pos) i (steps i)) v[i] :=
  (QueryImpl.EqDistTriple.ofFnM (fun _ ↦ True) _ (fun _ _ _ _ hle h ↦ h.mono hle) fun i ↦
    (labChain_labTriple core hd pkSeed pos i (hs i)).mono (fun _ h ↦ h)
      fun _ _ h ↦ ⟨trivial, h⟩).mono (fun _ h ↦ h) fun _ _ h ↦ h.2

include hd in
/-- **WOTS+ chain tops.** The honest chain tops from the secrets are related to the lab tops, and
each chain cell at `w - 1` then holds its top. -/
theorem wotsPkGenTopsWithSecret_labTriple :
    LabTriple core pkSeed (fun _ ↦ True)
      (wotsPkGenTopsWithSecret core (PublicHash.f core pkSeed) (labSecret core)
        (wotsInstanceAdrs pos))
      (labWotsPkGenTops core (wotsInstanceAdrs pos))
      fun tops st ↦ ∀ i : Fin vp.params.len, CellHolds core st
        (wotsChainCell core (wotsInstanceAdrs pos) i (vp.params.w - 1)) tops[i] :=
  ofFnM_labChain_labTriple core hd pkSeed pos (fun _ ↦ _) fun _ ↦ le_rfl

include hd in
/-- **WOTS+ signing.** Honest WOTS+ signing from the secrets is related to lab signing, and each
chain cell at its step count then holds its signature value. -/
theorem wotsSignWithSecret_labTriple (msg : core.Y) :
    LabTriple core pkSeed (fun _ ↦ True)
      (wotsSignWithSecret core (PublicHash.f core pkSeed) (labSecret core) msg
        (wotsInstanceAdrs pos))
      (labWotsSign core msg (wotsInstanceAdrs pos))
      fun sig st ↦ ∀ i : Fin vp.params.len, CellHolds core st
        (wotsChainCell core (wotsInstanceAdrs pos) i (chainStepsCore core msg i)) sig[i] :=
  ofFnM_labChain_labTriple core hd pkSeed pos _ fun i ↦ chainStepsCore_le core msg i

include hd in
/-- **The WOTS+ public key.** The honest WOTS+ public key from the secrets is related to the lab
public key, and the cell of the public-key compression then holds it. -/
theorem wotsPkGenWithSecret_labTriple :
    LabTriple core pkSeed (fun _ ↦ True)
      (wotsPkGenWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
        (labSecret core) (wotsInstanceAdrs pos))
      (labXmssLeaf core pos.toAdrs pos.leaf.val)
      fun y st ↦ CellHolds core st (childCell core (.inr (wotsPkAdrs (wotsInstanceAdrs pos)))) y :=
  (wotsPkGenTopsWithSecret_labTriple core hd pkSeed pos).bind fun tops ↦
    (tl_labTriple core hd pkSeed (wotsPkAdrs_mem_constructionAddresses pos) _).mono
      (fun st h ↦ by
        rw [map_childCell_childAdrs_wotsPkAdrs]
        exact Vector.forall₂_map_range_toList_iff.2 h) fun _ _ h ↦ h

include hd in
/-- **WOTS+ recovery.** From a state holding each signature value at the chain cell of its step
count, honest recovery is related to recovery at the lab callbacks, and the cell of the
public-key compression then holds the recovered key. -/
theorem wotsPkFromSigWith_labTriple (sig : WotsSig vp.params core) (msg : core.Y) :
    LabTriple core pkSeed
      (fun st ↦ ∀ i : Fin vp.params.len, CellHolds core st
        (wotsChainCell core (wotsInstanceAdrs pos) i (chainStepsCore core msg i)) sig[i])
      (wotsPkFromSigWith core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed) sig msg
        (wotsInstanceAdrs pos))
      (wotsPkFromSigWith core (labF core) (labTl core) sig msg (wotsInstanceAdrs pos))
      fun y st ↦
        CellHolds core st (childCell core (.inr (wotsPkAdrs (wotsInstanceAdrs pos)))) y := by
  refine (QueryImpl.EqDistTriple.ofFnM _ (fun (i : Fin vp.params.len) y st ↦ CellHolds core st
      (wotsChainCell core (wotsInstanceAdrs pos) i (vp.params.w - 1)) y)
    (fun _ _ _ _ hle h ↦ h.mono hle) fun i ↦ ?_).bind fun tops ↦ ?_
  · have hs := chainStepsCore_le core msg i
    refine ((chainWith_labTriple core hd pkSeed pos i sig[i] _ _ (by omega)).frame
      (F := fun st ↦ ∀ i : Fin vp.params.len, CellHolds core st
        (wotsChainCell core (wotsInstanceAdrs pos) i (chainStepsCore core msg i)) sig[i])
      fun _ _ hle h i ↦ (h i).mono hle).mono (fun _ h ↦ ⟨h i, h⟩) fun _ _ h ↦ ⟨h.2, ?_⟩
    rw [← Nat.add_sub_of_le hs]
    exact h.1
  · exact (tl_labTriple core hd pkSeed (wotsPkAdrs_mem_constructionAddresses pos) _).mono
      (fun st h ↦ by
        rw [map_childCell_childAdrs_wotsPkAdrs]
        exact Vector.forall₂_map_range_toList_iff.2 h.2) fun _ _ h ↦ h

end Wots

/-! ## XMSS -/

section Xmss

variable (coord : LayerTreeCoord vp)

include hd in
/-- **An XMSS leaf.** At leaf `t < 2 ^ h'` of a reachable tree, the honest leaf from the secrets
is related to the lab leaf, and the leaf's cell then holds it. -/
theorem xmssLeafWithSecret_labTriple {t : ℕ} (ht : t < 2 ^ vp.params.hp) :
    LabTriple core pkSeed (fun _ ↦ True)
      (xmssLeafWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
        (labSecret core) coord.toAdrs t)
      (labXmssLeaf core coord.toAdrs t)
      fun y st ↦ True ∧ XmssHolds core coord.toAdrs 0 t y st :=
  (wotsPkGenWithSecret_labTriple core hd pkSeed ⟨coord.layer, coord.tree, ⟨t, ht⟩⟩).mono
    (fun _ h ↦ h) fun _ _ h ↦ ⟨trivial, h⟩

include hd in
/-- **An XMSS node.** At an internal node `(h + 1, i)` of a reachable tree, from a state holding
its children at `l` and `r`, the honest `H` and the lab `H` are related, and the node's cell then
holds the result. -/
theorem xmssNodeHashWith_labTriple {h i : ℕ} (hh : h < vp.params.hp)
    (hi : i < 2 ^ (vp.params.hp - (h + 1))) (l r : core.Y) :
    LabTriple core pkSeed
      (fun st ↦ True ∧ XmssHolds core coord.toAdrs h (2 * i) l st ∧
        XmssHolds core coord.toAdrs h (2 * i + 1) r st)
      (xmssNodeHashWith (PublicHash.h core pkSeed) coord.toAdrs (h + 1) i l r)
      (xmssNodeHashWith (labH core) coord.toAdrs (h + 1) i l r)
      fun y st ↦ True ∧ XmssHolds core coord.toAdrs (h + 1) i y st :=
  (h_labTriple core hd pkSeed
    (xmssNodeAdrs_mem_constructionAddresses coord (by omega) (by omega) hi)
    (map_childCell_childAdrs_xmssNodeAdrs core _ h i) l r).mono (fun _ h ↦ h.2)
    fun _ _ h ↦ ⟨trivial, h⟩

include hd in
/-- **An XMSS root.** The honest root of a reachable tree from the secrets is related to the lab
root, and the root's cell then holds it. -/
theorem xmssNodeWithSecret_labTriple :
    LabTriple core pkSeed (fun _ ↦ True)
      (xmssNodeWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
        (PublicHash.h core pkSeed) (labSecret core) coord.toAdrs vp.params.hp 0)
      (labXmssNode core coord.toAdrs vp.params.hp 0)
      fun y st ↦ XmssHolds core coord.toAdrs vp.params.hp 0 y st :=
  (QueryImpl.EqDistTriple.merkleRootM _ (XmssHolds core coord.toAdrs)
    (fun _ _ _ _ _ hle h ↦ h.mono hle) _ _
    (fun _ hi ↦ xmssLeafWithSecret_labTriple core hd pkSeed coord
      ((Nat.div_eq_zero_iff_lt (by positivity)).1 hi))
    fun _ _ hh hi ↦ xmssNodeHashWith_labTriple core hd pkSeed coord hh
      ((Nat.div_eq_zero_iff_lt (by positivity)).1 hi)).mono (fun _ h ↦ h) fun _ _ h ↦ h.2

include hd in
/-- **An XMSS authentication path.** For leaf `idx < 2 ^ h'` of a reachable tree, the honest
authentication path is related to the lab one, and the cell of each sibling node then holds its
entry. -/
theorem xmssAuthPath_labTriple {idx : ℕ} (hidx : idx < 2 ^ vp.params.hp) :
    LabTriple core pkSeed (fun _ ↦ True)
      (intrinsicAuthPathM
        (xmssLeafWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
          (labSecret core) coord.toAdrs)
        (xmssNodeHashWith (PublicHash.h core pkSeed) coord.toAdrs) idx vp.params.hp)
      (intrinsicAuthPathM (labXmssLeaf core coord.toAdrs)
        (xmssNodeHashWith (labH core) coord.toAdrs) idx vp.params.hp)
      fun path st ↦ ∀ j (hj : j < vp.params.hp),
        XmssHolds core coord.toAdrs j (sibling (idx / 2 ^ j)) path[j] st := by
  have hz : idx / 2 ^ vp.params.hp = 0 := Nat.div_eq_of_lt hidx
  exact (QueryImpl.EqDistTriple.intrinsicAuthPathM _ (XmssHolds core coord.toAdrs)
    (fun _ _ _ _ _ hle h ↦ h.mono hle) _ _
    (fun _ hi ↦ xmssLeafWithSecret_labTriple core hd pkSeed coord
      ((Nat.div_eq_zero_iff_lt (by positivity)).1 (hi.trans hz)))
    fun _ _ hh hi ↦ xmssNodeHashWith_labTriple core hd pkSeed coord hh
      ((Nat.div_eq_zero_iff_lt (by positivity)).1 (hi.trans hz))).mono (fun _ h ↦ h)
    fun _ _ h ↦ h.2

include hd in
/-- **XMSS signing.** At a reachable position, honest XMSS signing from the secrets is related to
lab signing, and the state then holds the signature (`XmssSigHolds`). -/
theorem xmssSignWithSecret_labTriple (pos : LayerPosition vp) (msg : core.Y) :
    LabTriple core pkSeed (fun _ ↦ True)
      (xmssSignWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
        (PublicHash.h core pkSeed) (labSecret core) msg pos.toAdrs pos.leaf.val)
      (labXmssSign core msg pos.toAdrs pos.leaf.val)
      fun sig st ↦ XmssSigHolds core pos msg sig st :=
  (xmssAuthPath_labTriple core hd pkSeed ⟨pos.layer, pos.tree⟩ pos.leaf.isLt).bind
    fun path ↦ (((wotsSignWithSecret_labTriple core hd pkSeed pos msg).frame
      (F := fun st ↦ ∀ j (hj : j < vp.params.hp),
        XmssHolds core pos.toAdrs j (sibling (pos.leaf.val / 2 ^ j)) path[j] st)
      fun _ _ hle h j hj ↦ (h j hj).mono hle).mono (fun _ h ↦ ⟨trivial, h⟩)
        fun _ _ h ↦ h).bind fun sig ↦
      QueryImpl.EqDistTriple.pure _ fun _ h ↦ ⟨h.1, h.2⟩

include hd in
/-- **XMSS recovery.** At a reachable position, from a state holding the signature
(`XmssSigHolds`), honest root recovery is related to recovery at the lab callbacks, and the
tree's root cell then holds the recovered root. -/
theorem xmssPkFromSigWith_labTriple (pos : LayerPosition vp) (sig : XmssSig vp.params core)
    (msg : core.Y) :
    LabTriple core pkSeed (XmssSigHolds core pos msg sig)
      (xmssPkFromSigWith core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
        (PublicHash.h core pkSeed) pos.leaf.val sig msg pos.toAdrs)
      (xmssPkFromSigWith core (labF core) (labTl core) (labH core) pos.leaf.val sig msg
        pos.toAdrs)
      fun y st ↦ XmssHolds core pos.toAdrs vp.params.hp 0 y st := by
  refine (((wotsPkFromSigWith_labTriple core hd pkSeed pos sig.wots msg).frame
    (F := fun st ↦ ∀ j (hj : j < vp.params.hp),
      XmssHolds core pos.toAdrs j (sibling (pos.leaf.val / 2 ^ j)) sig.auth[j] st)
    fun _ _ hle h j hj ↦ (h j hj).mono hle).mono (fun _ h ↦ h) fun _ _ h ↦ h).bind
      fun leaf ↦ ?_
  have climb := QueryImpl.EqDistTriple.climbM (fun _ ↦ True) (XmssHolds core pos.toAdrs)
    (fun _ _ _ _ _ hle h ↦ h.mono hle) pos.leaf.val leaf sig.auth.toList
    fun h hh l r ↦ xmssNodeHashWith_labTriple core hd pkSeed ⟨pos.layer, pos.tree⟩
      (h := h) (i := pos.leaf.val / 2 ^ (h + 1)) (by simpa using hh) (by
        simp only [Vector.length_toList] at hh
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hh]
        exact pos.leaf.isLt) l r
  simp only [Vector.length_toList, Vector.getElem_toList,
    Nat.div_eq_of_lt pos.leaf.isLt] at climb
  exact climb.mono (fun _ h ↦ ⟨trivial, h.1, h.2⟩) fun _ _ h ↦ h.2

end Xmss

/-! ## FORS -/

section Fors

variable (pos : BottomPosition vp)

include hd in
/-- **A FORS node.** At an internal node `(h + 1, i)` of tree `tree` at a reachable bottom
position, from a state holding its children at `l` and `r`, the honest `H` and the lab `H` are
related, and the node's cell then holds the result. -/
theorem forsNodeHashWith_labTriple (tree : Fin vp.params.k) {h i : ℕ} (hh : h < vp.params.a)
    (hi : i / 2 ^ (vp.params.a - (h + 1)) = tree.val) (l r : core.Y) :
    LabTriple core pkSeed
      (fun st ↦ True ∧ ForsHolds core pos.forsAdrs h (2 * i) l st ∧
        ForsHolds core pos.forsAdrs h (2 * i + 1) r st)
      (forsNodeHashWith (PublicHash.h core pkSeed) pos.forsAdrs (h + 1) i l r)
      (forsNodeHashWith (labH core) pos.forsAdrs (h + 1) i l r)
      fun y st ↦ True ∧ ForsHolds core pos.forsAdrs (h + 1) i y st :=
  (h_labTriple core hd pkSeed
    (forsTreeAdrs_mem_constructionAddresses pos tree (by omega) (by omega) hi)
    (map_childCell_childAdrs_forsNodeAdrs core _ h i) l r).mono (fun _ h ↦ h.2)
    fun _ _ h ↦ ⟨trivial, h⟩

include hd in
/-- **A FORS authentication path.** For the leaf of tree `i` that the digest `md` opens, at a
reachable bottom position, the honest authentication path is related to the lab one, and the cell
of each sibling node then holds its entry. -/
theorem forsAuthPath_labTriple (md : List Byte) (i : Fin vp.params.k) :
    LabTriple core pkSeed (fun _ ↦ True)
      (intrinsicAuthPathM
        (forsLeafWithSecret core (PublicHash.f core pkSeed) (labSecret core) pos.forsAdrs)
        (forsNodeHashWith (PublicHash.h core pkSeed) pos.forsAdrs)
        (forsLeafIndex vp.params md i) vp.params.a)
      (intrinsicAuthPathM (labForsLeaf core pos.forsAdrs)
        (forsNodeHashWith (labH core) pos.forsAdrs) (forsLeafIndex vp.params md i) vp.params.a)
      fun path st ↦ ∀ j (hj : j < vp.params.a), ForsHolds core pos.forsAdrs j
        (sibling (forsLeafIndex vp.params md i / 2 ^ j)) path[j] st := by
  have hdiv := forsLeafIndex_div vp.params md i
  exact (QueryImpl.EqDistTriple.intrinsicAuthPathM _ (ForsHolds core pos.forsAdrs)
    (fun _ _ _ _ _ hle h ↦ h.mono hle) _ _
    (fun _ hj ↦ (labForsLeaf_labTriple core hd pkSeed pos i (hj.trans hdiv)).mono (fun _ h ↦ h)
      fun _ _ h ↦ ⟨trivial, h⟩)
    fun _ _ hh hj ↦ forsNodeHashWith_labTriple core hd pkSeed pos i hh (hj.trans hdiv)).mono
    (fun _ h ↦ h) fun _ _ h ↦ h.2

include hd in
/-- **FORS signing.** At a reachable bottom position, honest FORS signing from the secrets is
related to lab signing, and the state then holds the signature (`ForsSigHolds`). -/
theorem forsSignWithSecret_labTriple (md : List Byte) :
    LabTriple core pkSeed (fun _ ↦ True)
      (forsSignWithSecret core (PublicHash.f core pkSeed) (PublicHash.h core pkSeed)
        (labSecret core) md pos.forsAdrs)
      (labForsSign core md pos.forsAdrs)
      fun sig st ↦ ForsSigHolds core pos md sig st :=
  (QueryImpl.EqDistTriple.ofFnM (fun _ ↦ True)
    (fun (i : Fin vp.params.k) (sig : ForsTreeSigCore vp.params core) st ↦
      CellHolds core st (childCell core (.inl (forsSkAdrs pos.forsAdrs
        (forsLeafIndex vp.params md i)))) sig.sk ∧
      ∀ j (hj : j < vp.params.a), ForsHolds core pos.forsAdrs j
        (sibling (forsLeafIndex vp.params md i / 2 ^ j)) sig.auth[j] st)
    (fun _ _ _ _ hle h ↦ ⟨h.1.mono hle, fun j hj ↦ (h.2 j hj).mono hle⟩) fun i ↦
      (forsAuthPath_labTriple core hd pkSeed pos md i).bind fun path ↦
        (((labSecret_labTriple core pkSeed (Adrs.isSecretKey_forsSkAdrs _ _)).frame
          (F := fun st ↦ ∀ j (hj : j < vp.params.a), ForsHolds core pos.forsAdrs j
            (sibling (forsLeafIndex vp.params md i / 2 ^ j)) path[j] st)
          fun _ _ hle h j hj ↦ (h j hj).mono hle).mono (fun _ h ↦ ⟨trivial, h⟩)
            fun _ _ h ↦ h).bind fun sk ↦
          QueryImpl.EqDistTriple.pure _ fun _ h ↦ ⟨trivial, h.1, h.2⟩).mono (fun _ h ↦ h)
    fun _ _ h ↦ h.2

include hd in
/-- **FORS recovery.** At a reachable bottom position, from a state holding the signature
(`ForsSigHolds`), honest FORS public-key recovery is related to recovery at the lab callbacks,
and the cell of the roots compression then holds the recovered key. -/
theorem forsPkFromSigWith_labTriple (sig : ForsSigCore vp.params core) (md : List Byte) :
    LabTriple core pkSeed (ForsSigHolds core pos md sig)
      (forsPkFromSigWith core (PublicHash.f core pkSeed) (PublicHash.h core pkSeed)
        (PublicHash.tl core pkSeed) sig md pos.forsAdrs)
      (forsPkFromSigWith core (labF core) (labH core) (labTl core) sig md pos.forsAdrs)
      fun y st ↦ CellHolds core st (childCell core (.inr (forsPkAdrs pos.forsAdrs))) y := by
  refine (QueryImpl.EqDistTriple.ofFnM _ (fun (i : Fin vp.params.k) y ↦
      ForsHolds core pos.forsAdrs vp.params.a i y) (fun _ _ _ _ hle h ↦ h.mono hle)
    fun i ↦ ?_).bind fun roots ↦ ?_
  · have hdiv := forsLeafIndex_div vp.params md i
    have hleaf := f_labTriple core hd pkSeed (forsLeafAdrs_mem_constructionAddresses pos i hdiv)
      (by rw [childAdrs_forsNodeAdrs_zero]; rfl) sig[i].sk
    have climb := fun leaf ↦ QueryImpl.EqDistTriple.climbM (fun _ ↦ True)
      (ForsHolds core pos.forsAdrs) (fun _ _ _ _ _ hle h ↦ h.mono hle)
      (forsLeafIndex vp.params md i) leaf sig[i].auth.toList
      fun h hh l r ↦ forsNodeHashWith_labTriple core hd pkSeed pos i (h := h)
        (by simpa using hh) (by
          simp only [Vector.length_toList] at hh
          rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hh, hdiv]) l r
    refine ((hleaf.frame (F := ForsSigHolds core pos md sig) fun _ _ ↦ ForsSigHolds.mono).mono
      (fun st h ↦ ⟨(h i).1, h⟩) fun _ _ h ↦ h).bind fun leaf ↦ ?_
    refine ((climb leaf).frame (F := ForsSigHolds core pos md sig)
      fun _ _ ↦ ForsSigHolds.mono).mono (fun st h ↦ ⟨⟨trivial, h.1, ?_⟩, h.2⟩)
        fun _ _ h ↦ ⟨h.2, ?_⟩
    · simpa using (h.2 i).2
    · simpa [hdiv] using h.1.2
  · exact (tl_labTriple core hd pkSeed (forsRootAdrs_mem_constructionAddresses pos) _).mono
      (fun st h ↦ by
        rw [map_childCell_childAdrs_forsPkAdrs]
        exact Vector.forall₂_map_range_toList_iff.2 h.2) fun _ _ h ↦ h

end Fors

end SLHDSA.Security
