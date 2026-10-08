/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.NodeGraph
public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# The lab scheme of SLH-DSA

The *lab* programs are SLH-DSA key generation and signing rewritten over the label operations of
the canonical graph `slhGraph core pkSeed` (`VCVio.OracleComp.QueryTracking.RandomOracle.Relabel`).
They run over `labSpec core`, the derivation world `deriveSpec core` extended by `touch` and
`read` on the cells of the graph, and `labScheme core optRand pkSeed` is the secret-free scheme
`deriveScheme` in this form.

* **The tweakable hash is a label.** In the lab, the tweakable hash at an address is the label of
  the address's node, whatever its input: the lab callbacks `labF`, `labH` and `labTl` all read
  the cell `childCell core (.inr a)` (`labNode`). At an address outside the union ledger there is
  no cell, and the read returns a fixed value, so the lab programs make no public `thash` query and
  draw nothing there.
* **Touch normal forms.** A callback cannot tell whether its output is used, so the two places
  where honest SLH-DSA consumes a secret are rewritten as touch-then-read programs
  (`OracleComp.touchRead`) along a hash path (`pathCell`): `labChain adrs i s` touches the secret
  and hash steps `0, …, s - 2` of WOTS+ chain `i` and reads step `s - 1` (the secret at `s = 0`),
  and `labForsLeaf adrs t` touches the leaf's secret and reads the leaf. In the graph, each cell of
  the path is the only child of the next node (`slhGraph_ch_wotsChainAdrs_setHashAddress`,
  `slhGraph_ch_forsNodeAdrs_zero`).
* **Components.** `labWotsPkGenTops`, `labWotsSign`, `labXmssLeaf`, `labXmssNode`, `labXmssSign`,
  `labForsSign`, `labSignFromPosition`, `labKeygen` and `labSignInternal` follow the
  provider-parametric programs of `HashSig.SLHDSA.SecretProvider` step for step, by the same
  combinators. Root recovery inside signing is `xmssPkFromSigWith` and `forsPkFromSigWith` at the
  lab callbacks. Only `labSignInternal` depends on the public seed, through its `H_msg` query.
* **Scheme and experiment.** `labScheme` signs at its public seed with the randomizer drawn as in
  `deriveScheme`, and verifies with FIPS 205 Algorithm 20 over public queries. `labAdversary` is
  `deriveAdversary` lifted to `labSpec`, and `labExperiment` is the transcript experiment of
  `labScheme` against it.

`deriveScheme` lifted to `labSpec` by `labLiftHom` is the provider-parametric scheme with every
secret drawn from `labSecret` and with the verification of `labScheme`, and its transcript
experiment runs the program of `labAdversary`; so it and `labExperiment` differ only in key
generation and signing. The `_pred` lemmas carry a predicate on programs, closed under `pure` and
`bind`, from the touches and reads of cells to every lab component, with no hypothesis on
addresses.

## References

- NIST FIPS 205, Algorithms 5–7 (WOTS+), 9–10 (XMSS), 12 (hypertree), 14–16 (FORS), 18–20
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Label operations -/

/-- Programs with uniform sampling, the hash oracles, derivation queries and the label operations
on the cells of the canonical graph of SLH-DSA. -/
abbrev labSpec := (hashSpec core).withLabels (DeriveQuery core) (NodeKey core) core.Y

/-- Lifting from the derivation world into `labSpec`, as a morphism that preserves the public hash
queries. -/
@[expose] noncomputable def labLiftHom :
    HasQuery.QueryHom (publicHashSpec core) (OracleComp (deriveSpec core))
      (OracleComp (labSpec core)) where
  toMonadHom := simulateQ' (QueryImpl.ofLift (deriveSpec core) (OracleComp (labSpec core)))
  map_query' _ := rfl

/-- The lifting morphism is `liftComp`. -/
theorem labLiftHom_apply {α : Type} (oa : OracleComp (deriveSpec core) α) :
    (labLiftHom core).toMonadHom oa = liftComp oa (labSpec core) := rfl

/-! ## Hash paths -/

/-- The cells of a hash path from the secret at `sk` through the nodes at `node 0, node 1, …`:
cell `0` is the cell of the secret and cell `j + 1` the cell of `node j` (`childCell`). -/
@[expose] def pathCell (sk : Adrs) (node : ℕ → Adrs) : ℕ → Option (DeriveQuery core ⊕ NodeKey core)
  | 0 => childCell core (.inl sk)
  | j + 1 => childCell core (.inr (node j))

/-- The first cell of a hash path from a secret-key address is the derivation at its key. -/
theorem pathCell_zero {sk : Adrs} (h : sk.IsSecretKey) (node : ℕ → Adrs) :
    pathCell core sk node 0 = some (.inl (.inl ⟨core.adrsToKey sk, sk, h, rfl⟩)) :=
  childCell_inl core h

/-- A later cell of a hash path, at a ledger node, is that node's label. -/
theorem pathCell_succ_of_mem (sk : Adrs) {node : ℕ → Adrs} {j : ℕ}
    (h : node j ∈ constructionAddresses vp) :
    pathCell core sk node (j + 1) = some (.inr ⟨core.adrsToKey (node j), node j, h, rfl⟩) :=
  childCell_inr core h

/-- **WOTS+ chain cells are children.** Under the key discipline, the children of hash step `j` of
a WOTS+ chain in the union ledger are cell `j` of the chain's hash path. -/
theorem slhGraph_ch_wotsChainAdrs_setHashAddress (hd : core.KeyDiscipline vp)
    (pkSeed : core.PkSeed) {adrs : Adrs} {i j : ℕ}
    (h : (wotsChainAdrs adrs i).setHashAddress j ∈ constructionAddresses vp) :
    (slhGraph core pkSeed).ch ⟨_, _, h, rfl⟩ =
      (pathCell core (wotsSkAdrs adrs i) ((wotsChainAdrs adrs i).setHashAddress ·) j).toList := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed (nodeKeyOf_of_mem core h)]
  rcases j with _ | j
  · rw [childAdrs_wotsChainAdrs_setHashAddress_zero, List.filterMap_cons, List.filterMap_nil,
      pathCell]
    cases childCell core (.inl (wotsSkAdrs adrs i)) <;> rfl
  · rw [childAdrs_wotsChainAdrs_setHashAddress_succ, List.filterMap_cons, List.filterMap_nil,
      pathCell]
    cases childCell core (.inr ((wotsChainAdrs adrs i).setHashAddress j)) <;> rfl

/-- **FORS leaf cells are children.** Under the key discipline, the children of a FORS leaf in the
union ledger are cell `0` of the leaf's hash path, its secret. -/
theorem slhGraph_ch_forsNodeAdrs_zero (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    {adrs : Adrs} {t : ℕ} (h : forsNodeAdrs adrs 0 t ∈ constructionAddresses vp) :
    (slhGraph core pkSeed).ch ⟨_, _, h, rfl⟩ =
      (pathCell core (forsSkAdrs adrs t) (fun _ => forsNodeAdrs adrs 0 t) 0).toList := by
  rw [hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed (nodeKeyOf_of_mem core h),
    childAdrs_forsNodeAdrs_zero, List.filterMap_cons, List.filterMap_nil, pathCell]
  cases childCell core (.inl (forsSkAdrs adrs t)) <;> rfl

/-! ## Lab callbacks and touch normal forms -/

variable [SampleableType core.Y]

/-- The secret value at an address, as `deriveSecret` reads it: the derivation at its key at a
secret-key address. -/
@[expose] def labSecret (a : Adrs) : OracleComp (labSpec core) core.Y :=
  liftComp (deriveSecret core a) (labSpec core)

/-- At a secret-key address the lab secret reads the derivation at its key. -/
theorem labSecret_of_isSecretKey {a : Adrs} (h : a.IsSecretKey) :
    labSecret core a = readCell (some (.inl (.inl ⟨core.adrsToKey a, a, h, rfl⟩))) := by
  simp only [labSecret, deriveSecret, h, ↓reduceDIte]
  rfl

/-- The value of the node at `a`: the label of its node at a ledger address, and a fixed value
elsewhere. -/
@[expose] noncomputable def labNode (a : Adrs) : OracleComp (labSpec core) core.Y :=
  readCell (childCell core (.inr a))

/-- At a ledger address the node value is the label of its node. -/
theorem labNode_of_mem {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    labNode core a = readCell (some (.inr ⟨core.adrsToKey a, a, ha, rfl⟩)) := by
  rw [labNode, childCell_inr core ha]

/-- The tweakable hash `T(PK.seed, a, xs)` in the lab: the value of the node at `a`. -/
@[expose] noncomputable def labTl (a : Adrs) (_xs : List core.Y) :
    OracleComp (labSpec core) core.Y :=
  labNode core a

/-- The tweakable hash `F` in the lab: the value of the node at `a`. -/
@[expose] noncomputable def labF (a : Adrs) (_y : core.Y) : OracleComp (labSpec core) core.Y :=
  labNode core a

/-- The tweakable hash `H` in the lab: the value of the node at `a`. -/
@[expose] noncomputable def labH (a : Adrs) (_l _r : core.Y) : OracleComp (labSpec core) core.Y :=
  labNode core a

/-- **The lab WOTS+ chain.** The value of chain `i` at `adrs` after `s` steps from its secret: the
cells `0, …, s - 1` of the chain's hash path touched, then cell `s` read. -/
@[expose] noncomputable def labChain (adrs : Adrs) (i s : ℕ) : OracleComp (labSpec core) core.Y :=
  touchRead (pathCell core (wotsSkAdrs adrs i) ((wotsChainAdrs adrs i).setHashAddress ·)) s

/-- **The lab FORS leaf.** The leaf at global index `t` under `adrs`: its secret touched, then the
leaf read. -/
@[expose] noncomputable def labForsLeaf (adrs : Adrs) (t : ℕ) : OracleComp (labSpec core) core.Y :=
  touchRead (pathCell core (forsSkAdrs adrs t) fun _ => forsNodeAdrs adrs 0 t) 1

/-- At a ledger leaf the lab FORS leaf touches the leaf's secret and reads the leaf. -/
theorem labForsLeaf_of_mem {adrs : Adrs} {t : ℕ}
    (h : forsNodeAdrs adrs 0 t ∈ constructionAddresses vp) :
    labForsLeaf core adrs t = (do
      touchCell (some (.inl (.inl ⟨_, _, Adrs.isSecretKey_forsSkAdrs adrs t, rfl⟩)))
      readCell (some (.inr ⟨_, _, h, rfl⟩))) := by
  rw [labForsLeaf, touchRead, touchUpTo, touchUpTo, pure_bind,
    pathCell_zero core (Adrs.isSecretKey_forsSkAdrs adrs t),
    show pathCell core (forsSkAdrs adrs t) (fun _ => forsNodeAdrs adrs 0 t) 1 = _ from
      childCell_inr core h]

/-! ## Lab components -/

/-- The `len` WOTS+ chain tops at `adrs`, each a lab chain of `w - 1` steps. -/
@[expose] noncomputable def labWotsPkGenTops (adrs : Adrs) :
    OracleComp (labSpec core) (Vector core.Y vp.params.len) :=
  Vector.ofFnM fun i => labChain core adrs i.val (vp.params.w - 1)

/-- The WOTS+ signature on `msg` at `adrs`: chain `i` a lab chain of `chainStepsCore core msg i`
steps. -/
@[expose] noncomputable def labWotsSign (msg : core.Y) (adrs : Adrs) :
    OracleComp (labSpec core) (WotsSig vp.params core) :=
  Vector.ofFnM fun i => labChain core adrs i.val (chainStepsCore core msg i.val)

/-- The XMSS leaf at keypair index `t` under `adrs`: the lab chain tops compressed by the lab
`T_len`. -/
@[expose] noncomputable def labXmssLeaf (adrs : Adrs) (t : ℕ) : OracleComp (labSpec core) core.Y :=
  do
    let tops ← labWotsPkGenTops core (wotsLeafAdrs adrs t)
    labTl core (wotsPkAdrs (wotsLeafAdrs adrs t)) tops.toList

/-- The height-`z`, index-`t` node of the XMSS tree at `adrs`, over lab leaves and the lab `H`. -/
@[expose] noncomputable def labXmssNode (adrs : Adrs) (z t : ℕ) :
    OracleComp (labSpec core) core.Y :=
  PerfectMerkleTree.merkleRootM (labXmssLeaf core adrs) (xmssNodeHashWith (labH core) adrs) z t

/-- The XMSS signature at leaf `idx` on `msg`: the authentication path through the lab tree, then
the lab WOTS+ signature. -/
@[expose] noncomputable def labXmssSign (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    OracleComp (labSpec core) (XmssSig vp.params core) := do
  let path ← PerfectMerkleTree.intrinsicAuthPathM (labXmssLeaf core adrs)
    (xmssNodeHashWith (labH core) adrs) idx vp.params.hp
  let sig ← labWotsSign core msg (wotsLeafAdrs adrs idx)
  return ⟨sig, path⟩

/-- The FORS signature on digest `md` at `adrs`: for each tree, the authentication path through
the lab tree and the secret at the indexed leaf. -/
@[expose] noncomputable def labForsSign (md : List Byte) (adrs : Adrs) :
    OracleComp (labSpec core) (ForsSigCore vp.params core) :=
  Vector.ofFnM fun i : Fin vp.params.k => do
    let idx := i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val
    let path ← PerfectMerkleTree.intrinsicAuthPathM (labForsLeaf core adrs)
      (forsNodeHashWith (labH core) adrs) idx vp.params.a
    let sk ← labSecret core (forsSkAdrs adrs idx)
    return ⟨sk, path⟩

/-- The hypertree signature of `msg` from layer position `pos` upward over `layers` layers, with
every XMSS signature `labXmssSign` and every root recovered by `xmssPkFromSigWith` at the lab
callbacks. `recoverFinal` forces the redundant root recovery in the top layer. -/
@[expose] noncomputable def labSignFromPosition (recoverFinal : Bool) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      OracleComp (labSpec core) (Vector (XmssSig vp.params core) layers)
  | 0, _, _ => pure #v[]
  | 1, _, msg => do
      let sig ← labXmssSign core msg pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ ← xmssPkFromSigWith core (labF core) (labTl core) (labH core) pos.leaf.val sig msg
          pos.toAdrs
        return #v[sig]
      else
        return #v[sig]
  | layers + 2, hremaining, msg => do
      let sig ← labXmssSign core msg pos.toAdrs pos.leaf.val
      let root ← xmssPkFromSigWith core (labF core) (labTl core) (labH core) pos.leaf.val sig msg
        pos.toAdrs
      let next := pos.next (by omega)
      let rest ← labSignFromPosition false next (layers + 1) (by simp [next]; omega) root
      return rest.insertIdx 0 sig

/-- Key generation in the lab: the root of the top-layer XMSS tree. -/
@[expose] noncomputable def labKeygen : OracleComp (labSpec core) core.Y :=
  labXmssNode core (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) vp.params.hp 0

/-- Signing in the lab at public seed `pkSeed` and randomizer `R`: `H_msg` is a public query, FORS
signing is `labForsSign`, the FORS public key is recovered by `forsPkFromSigWith` at the lab
callbacks, and the hypertree signature is `labSignFromPosition`. -/
@[expose] noncomputable def labSignInternal (pkSeed : core.PkSeed) (msg : List Byte)
    (pkRoot R : core.Y) : OracleComp (labSpec core) (GeneralScheme.SignatureCore vp core) := do
  let digest ← PublicHash.hmsg core R pkSeed pkRoot msg
  let parts := splitDigest vp.params digest
  let forsSig ← labForsSign core parts.md.toList parts.forsAdrs
  let forsPk ← forsPkFromSigWith core (labF core) (labH core) (labTl core) forsSig
    parts.md.toList parts.forsAdrs
  let htSig ← labSignFromPosition core (vp.params.d == 1) (LayerPosition.initial vp parts)
    vp.params.d (by simp) forsPk
  return ⟨R, forsSig, htSig⟩

/-! ## Predicates on the lab programs -/

section Pred

variable {Q : ∀ {α : Type}, OracleComp (labSpec core) α → Prop}
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : OracleComp (labSpec core) α)
    (ob : α → OracleComp (labSpec core) β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  (htouch : ∀ c, Q (touchCell (some c))) (hread : ∀ c, Q (readCell (some c)))

include hpure hread in
/-- The node value at any address satisfies `Q` when every read of a cell does. -/
theorem labNode_pred (a : Adrs) : Q (labNode core a) :=
  readCell_pred hpure hread _

include hpure hbind htouch hread in
/-- A lab WOTS+ chain satisfies `Q` when every touch and read of a cell does. -/
theorem labChain_pred (adrs : Adrs) (i s : ℕ) : Q (labChain core adrs i s) :=
  touchRead_pred hpure hbind htouch hread _ _

include hpure hbind htouch hread in
/-- A lab FORS leaf satisfies `Q` when every touch and read of a cell does. -/
theorem labForsLeaf_pred (adrs : Adrs) (t : ℕ) : Q (labForsLeaf core adrs t) :=
  touchRead_pred hpure hbind htouch hread _ _

include hpure hbind htouch hread in
/-- The lab WOTS+ chain tops satisfy `Q`. -/
theorem labWotsPkGenTops_pred (adrs : Adrs) : Q (labWotsPkGenTops core adrs) :=
  Vector.ofFnM_pred Q hpure hbind _ fun _ => labChain_pred core hpure hbind htouch hread _ _ _

include hpure hbind htouch hread in
/-- The lab WOTS+ signature satisfies `Q`. -/
theorem labWotsSign_pred (msg : core.Y) (adrs : Adrs) : Q (labWotsSign core msg adrs) :=
  Vector.ofFnM_pred Q hpure hbind _ fun _ => labChain_pred core hpure hbind htouch hread _ _ _

include hpure hbind htouch hread in
/-- A lab XMSS leaf satisfies `Q`. -/
theorem labXmssLeaf_pred (adrs : Adrs) (t : ℕ) : Q (labXmssLeaf core adrs t) :=
  hbind _ _ (labWotsPkGenTops_pred core hpure hbind htouch hread _) fun _ =>
    labNode_pred core hpure hread _

include hpure hbind htouch hread in
/-- A lab XMSS node satisfies `Q`. -/
theorem labXmssNode_pred (adrs : Adrs) (z t : ℕ) : Q (labXmssNode core adrs z t) :=
  PerfectMerkleTree.merkleRootM_pred_of_subtree Q hbind _ _ z t
    (fun _ _ => labXmssLeaf_pred core hpure hbind htouch hread _ _)
    fun _ _ _ _ _ _ _ => labNode_pred core hpure hread _

include hpure hbind htouch hread in
/-- The lab XMSS signature satisfies `Q`. -/
theorem labXmssSign_pred (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    Q (labXmssSign core msg adrs idx) :=
  hbind _ _ (PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ idx _
    (fun _ _ => labXmssLeaf_pred core hpure hbind htouch hread _ _)
    fun _ _ _ _ _ _ _ => labNode_pred core hpure hread _)
    fun _ => hbind _ _ (labWotsSign_pred core hpure hbind htouch hread msg _) fun _ => hpure _

include hpure hbind htouch hread in
/-- The lab FORS signature satisfies `Q`. -/
theorem labForsSign_pred (md : List Byte) (adrs : Adrs) : Q (labForsSign core md adrs) :=
  Vector.ofFnM_pred Q hpure hbind _ fun _ =>
    hbind _ _ (PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ _ _
      (fun _ _ => labForsLeaf_pred core hpure hbind htouch hread _ _)
      fun _ _ _ _ _ _ _ => labNode_pred core hpure hread _) fun _ =>
    hbind _ _ ((labSecret_of_isSecretKey core (Adrs.isSecretKey_forsSkAdrs _ _)) ▸ hread _)
      fun _ => hpure _

include hpure hbind htouch hread in
/-- The lab hypertree signature satisfies `Q`. -/
theorem labSignFromPosition_pred (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      Q (labSignFromPosition core recoverFinal pos layers h msg)
  | 0, _, _ => hpure _
  | 1, _, msg => by
      rw [labSignFromPosition]
      refine hbind _ _ (labXmssSign_pred core hpure hbind htouch hread msg _ _) fun sig => ?_
      cases recoverFinal
      · exact hpure _
      · exact hbind _ _ (xmssPkFromSigWith_pred Q hpure hbind core
          (fun a _ _ => labNode_pred core hpure hread a)
          (fun a _ _ => labNode_pred core hpure hread a)
          (fun a _ _ _ => labNode_pred core hpure hread a) _ sig msg _) fun _ => hpure _
  | layers + 2, _, msg => by
      rw [labSignFromPosition]
      exact hbind _ _ (labXmssSign_pred core hpure hbind htouch hread msg _ _) fun sig =>
        hbind _ _ (xmssPkFromSigWith_pred Q hpure hbind core
          (fun a _ _ => labNode_pred core hpure hread a)
          (fun a _ _ => labNode_pred core hpure hread a)
          (fun a _ _ _ => labNode_pred core hpure hread a) _ sig msg _) fun root =>
        hbind _ _ (labSignFromPosition_pred false _ (layers + 1) _ root) fun _ => hpure _

include hpure hbind htouch hread in
/-- Lab key generation satisfies `Q`. -/
theorem labKeygen_pred : Q (labKeygen core) :=
  labXmssNode_pred core hpure hbind htouch hread _ _ _

include hpure hbind htouch hread in
/-- Lab signing satisfies `Q` when, besides the touches and reads of cells, its `H_msg` query
does. -/
theorem labSignInternal_pred (pkSeed : core.PkSeed) (msg : List Byte) (pkRoot R : core.Y)
    (hmsg : Q (PublicHash.hmsg core R pkSeed pkRoot msg)) :
    Q (labSignInternal core pkSeed msg pkRoot R) :=
  have hnode := labNode_pred core hpure hread
  hbind _ _ hmsg fun _ =>
    hbind _ _ (labForsSign_pred core hpure hbind htouch hread _ _) fun _ =>
      hbind _ _ (forsPkFromSigWith_pred Q hpure hbind core (fun a _ _ => hnode a)
        (fun a _ _ => hnode a) (fun a _ _ _ => hnode a) _ _ _) fun _ =>
        hbind _ _ (labSignFromPosition_pred core hpure hbind htouch hread _ _ _ _ _) fun _ =>
          hpure _

end Pred

/-! ## The lab scheme and experiment -/

variable [DecidableEq core.Y]

/-- **The lab scheme at public seed `pkSeed`.** Key generation is `labKeygen`; signing draws
`opt_rand` from `optRand`, the randomizer as the derivation at `(opt_rand, M)`, and signs with
`labSignInternal` at `pkSeed`; verification is FIPS 205 Algorithm 20, with public queries. The
secret key is the public key. Signing does not read the secret key's public seed: key generation
sets it to `pkSeed`. -/
@[expose] noncomputable def labScheme (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) :
    SignatureAlg (OracleComp (labSpec core)) (List Byte) (PublicKeyCore core)
      (PublicKeyCore core) (GeneralScheme.SignatureCore vp core) where
  keygen := do
    let pkRoot ← labKeygen core
    return (⟨pkSeed, pkRoot⟩, ⟨pkSeed, pkRoot⟩)
  sign pk sk msg := do
    let R ← liftComp ((do
      let addrnd ← (optRand pk : ProbComp core.Y)
      query (spec := deriveSpec core) (.inr (.inr (addrnd, msg)))) :
        OracleComp (deriveSpec core) core.Y) (labSpec core)
    labSignInternal core pkSeed msg sk.pkRoot R
  verify pk msg sig := GeneralScheme.verifyInternalM vp core msg sig pk

/-! ## The lifted secret-free scheme -/

section Lift

variable (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)

/-- Key generation of the lifted secret-free scheme is provider-parametric key generation with
every secret value drawn from `labSecret`. -/
theorem map_labLiftHom_deriveScheme_keygen :
    ((deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom).keygen = do
      let pkRoot ← GeneralScheme.keygenInternalWithSecretM core (labSecret core) pkSeed
      return (⟨pkSeed, pkRoot⟩, ⟨pkSeed, pkRoot⟩) := by
  rw [map_keygen, deriveScheme, MonadHom.mmap_bind,
    GeneralScheme.keygenInternalWithSecretM_natural core (labLiftHom core) (deriveSecret core)
      (labSecret core) (fun _ _ => rfl)]
  simp

/-- Signing of the lifted secret-free scheme draws the randomizer as `labScheme` does and signs
with every secret value drawn from `labSecret`. -/
theorem map_labLiftHom_deriveScheme_sign (pk sk : PublicKeyCore core) (msg : List Byte) :
    ((deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom).sign pk sk msg = (do
      let R ← liftComp ((do
        let addrnd ← (optRand pk : ProbComp core.Y)
        query (spec := deriveSpec core) (.inr (.inr (addrnd, msg)))) :
          OracleComp (deriveSpec core) core.Y) (labSpec core)
      GeneralScheme.signInternalWithSecretRandomizerM core (labSecret core) msg sk.pkSeed
        sk.pkRoot R) := by
  rw [map_sign, labLiftHom_apply]
  dsimp only [deriveScheme]
  simp only [liftComp_bind, bind_assoc]
  refine bind_congr fun _ => bind_congr fun R => ?_
  exact GeneralScheme.signInternalWithSecretRandomizerM_natural core (labLiftHom core)
    (deriveSecret core) (labSecret core) (fun _ _ => rfl) msg _ _ R

/-- Verification of the lifted secret-free scheme is verification of `labScheme`. -/
theorem map_labLiftHom_deriveScheme_verify (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    ((deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom).verify pk msg sig =
      (labScheme core optRand pkSeed).verify pk msg sig :=
  GeneralScheme.verifyInternalM_natural vp core (labLiftHom core) msg sig pk

end Lift

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- A forger of `romScheme` as a forger of the lab scheme: `deriveAdversary` with its queries
lifted to `labSpec`. -/
@[expose] noncomputable def labAdversary {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed) :
    UnforgeableAdversary (labScheme core optRand pkSeed) :=
  (deriveAdversary core adv pkSeed).mapOracles
    (QueryImpl.ofLift (deriveSpec core) (OracleComp (labSpec core)))

/-- **The lab experiment.** The transcript experiment of the lab scheme at public seed `pkSeed`
against `labAdversary`. -/
@[expose] noncomputable def labExperiment {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed) :
    OracleComp (labSpec core) (DeriveOutcome core) :=
  unforgeableTranscriptExperiment (labAdversary core adv pkSeed)

/-- **The two experiments share the forger.** The transcript experiment of the secret-free scheme
against `deriveAdversary`, lifted to `labSpec`, is the transcript experiment of the lifted scheme
against the program of `labAdversary`. -/
theorem liftComp_unforgeableTranscriptExperiment_deriveAdversary {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed) :
    liftComp (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed)) (labSpec core) =
      unforgeableTranscriptExperiment
        (sigAlg := (deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom)
        ⟨(labAdversary core adv pkSeed).main⟩ := by
  rw [liftComp_def]
  refine (simulateQ_unforgeableTranscriptExperiment
    (QueryImpl.ofLift (deriveSpec core) (OracleComp (labSpec core))) _).trans ?_
  congr 1
  change UnforgeableAdversary.mk _ = UnforgeableAdversary.mk _
  congr 1
  funext pk
  simp only [labAdversary, UnforgeableAdversary.mapOracles_main]

end SLHDSA.Security
