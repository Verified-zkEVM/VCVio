/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.NodeGraph

/-!
# The lab scheme of SLH-DSA

At a public seed `pkSeed`, `labScheme core optRand pkSeed` is the secret-free scheme
`deriveScheme` rewritten over the label operations of the canonical graph `slhGraph core pkSeed`
(`VCVio.OracleComp.QueryTracking.RandomOracle.Relabel`): every tweakable hash of key generation and
signing at a node of the graph is a read of that node's label, and every chain value or secret
whose value the honest program computes but does not use is touched instead of read. Its programs
run over `labSpec core`, the derivation world `deriveSpec core` extended by `touch` and `read` on
the cells of the graph.

* **Routing by key.** `nodeAt core k` is the node whose oracle key is `k`, if `k` is the key of a
  ledger address. The lab callbacks `labF`, `labH` and `labTl` answer the tweakable hash at an
  address by reading the label of the node at its key (`labNode`), and issue the public query
  otherwise, so they are total and a lab program makes a public `thash` query only at a key that is
  no node's. A secret value is the derivation `deriveSecret` draws (`labSecret`).
* **Touch normal forms.** A callback cannot tell whether its output is used, so the two places
  where honest SLH-DSA consumes a secret are rewritten. `labChain adrs i s` touches cells
  `0, …, s - 1` of WOTS+ chain `i` (the secret, then hash steps `0, …, s - 2`) and reads cell `s`
  (`labChainTouch`, `labChainRead`); `labForsLeaf adrs t` touches the leaf's secret and reads the
  leaf. Hash steps whose key is no node's fall back to the public `F`.
* **Components.** `labWotsPkGenTops`, `labWotsSign`, `labXmssLeaf`, `labXmssNode`, `labXmssSign`,
  `labForsSign`, `labSignFromPosition`, `labKeygen` and `labSignInternal` follow the
  provider-parametric programs of `HashSig.SLHDSA.SecretProvider` step for step, built from the
  touch normal forms by the same combinators (`Vector.ofFnM`, `PerfectMerkleTree.merkleRootM`,
  `PerfectMerkleTree.intrinsicAuthPathM`). Root recovery inside signing is the callback-parametric
  `xmssPkFromSigWith` and `forsPkFromSigWith` at the lab callbacks.
* **Scheme and experiment.** `labScheme` signs at `pkSeed` with the randomizer drawn exactly as in
  `deriveScheme`, and verifies with FIPS 205 Algorithm 20 over public queries. `labAdversary` is
  `deriveAdversary` lifted to `labSpec`, and `labExperiment` is the transcript experiment of
  `labScheme` against it.

The lifted secret-free scheme, `deriveScheme` mapped by `labLiftHom` (which is `liftComp`), is the
provider-parametric scheme with every secret drawn from `labSecret`
(`map_labLiftHom_deriveScheme_keygen`, `map_labLiftHom_deriveScheme_sign`), with the verification of
`labScheme` (`map_labLiftHom_deriveScheme_verify`), and the lifted transcript experiment of
`deriveScheme` runs the program of `labAdversary`
(`liftComp_unforgeableTranscriptExperiment_deriveAdversary`). So the lifted experiment and
`labExperiment` differ only in key generation and signing.

At a ledger address the label operations unfold to a single touch or read (`labTouchNode_of_mem`,
`labNode_of_mem`, `labChainRead_succ_of_mem`, `labForsLeaf_of_mem`). The `_pred` lemmas carry a
predicate on programs, closed under `pure` and `bind`, through the label operations, the lab
callbacks and the touch normal forms, in the style of `HashSig.SLHDSA.AddressDiscipline`;
`isQueryBoundP_labChain_wotsInstanceAdrs` is the instance stating that a lab chain at a reachable
WOTS+ instance makes no public hash query.

## References

- NIST FIPS 205, Algorithms 5–7 (WOTS+), 9–10 (XMSS), 12 (hypertree), 14–16 (FORS), 18–20
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The node at a key -/

open Classical in
/-- The node of the canonical graph whose key is `k`, if `k` is the key of an address of the
union ledger. -/
noncomputable def nodeAt (k : core.AdrsKey) : Option (NodeKey core) :=
  if h : ∃ a ∈ constructionAddresses vp, core.adrsToKey a = k then some ⟨k, h⟩ else none

/-- The node at a key is the node with that key. -/
theorem nodeAt_eq_some_iff {k : core.AdrsKey} {κ : NodeKey core} :
    nodeAt core k = some κ ↔ k = κ.1 := by
  unfold nodeAt
  split_ifs with h
  · exact ⟨fun h' => by rw [← Option.some.inj h'], fun h' => by subst h'; rfl⟩
  · exact ⟨fun h' => absurd h' (by simp), fun h' => absurd (h' ▸ κ.2) h⟩

/-- The node at a node's key is that node. -/
@[simp]
theorem nodeAt_val (κ : NodeKey core) : nodeAt core κ.1 = some κ :=
  (nodeAt_eq_some_iff core).2 rfl

/-- The node at the key of a ledger address is its node key. -/
theorem nodeAt_adrsToKey_of_mem {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    nodeAt core (core.adrsToKey a) = some ⟨core.adrsToKey a, a, ha, rfl⟩ :=
  nodeAt_val core ⟨_, a, ha, rfl⟩

/-- The node keys place a tweakable-hash query at the public seed at the node at its key. -/
theorem slhNodeKeys_node_thash_self (pkSeed : core.PkSeed) (k : core.AdrsKey)
    (xs : List core.Y) :
    (slhNodeKeys core pkSeed).node (.inl (.thash pkSeed k xs)) = nodeAt core k := by
  refine Option.ext fun κ => ?_
  rw [slhNodeKeys_node_thash_eq_some_iff, nodeAt_eq_some_iff, eq_self, true_and]

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

/-- Read the label of node `κ`. -/
@[expose] def labRead (κ : NodeKey core) : OracleComp (labSpec core) core.Y :=
  query (spec := labSpec core) (.inr (.inr κ))

/-- Touch a cell: a derivation or a node label. -/
@[expose] def labTouch (c : DeriveQuery core ⊕ NodeKey core) : OracleComp (labSpec core) Unit :=
  query (spec := labSpec core) (.inr (.inl c))

/-- Touch the secret at a secret-key address; elsewhere do nothing. -/
@[expose] def labTouchSecret (a : Adrs) : OracleComp (labSpec core) Unit :=
  (prfKeyOf core a).elim (pure ()) fun k => labTouch core (.inl (.inl k))

/-- Touch the label of the node at the key of `a`; at an address whose key is no node's, do
nothing. -/
@[expose] noncomputable def labTouchNode (a : Adrs) : OracleComp (labSpec core) Unit :=
  (nodeAt core (core.adrsToKey a)).elim (pure ()) fun κ => labTouch core (.inr κ)

/-- The value of the node at the key of `a`: its label, or `fallback` at an address whose key is
no node's. -/
@[expose] noncomputable def labNode (a : Adrs) (fallback : OracleComp (labSpec core) core.Y) :
    OracleComp (labSpec core) core.Y :=
  (nodeAt core (core.adrsToKey a)).elim fallback (labRead core)

/-- At a secret-key address the secret touch touches the derivation at its key. -/
theorem labTouchSecret_of_isSecretKey {a : Adrs} (h : a.IsSecretKey) :
    labTouchSecret core a = labTouch core (.inl (.inl ⟨core.adrsToKey a, a, h, rfl⟩)) := by
  simp only [labTouchSecret, prfKeyOf_of_isSecretKey core h, Option.elim_some]

/-- At a ledger address the node touch touches the label of its node. -/
theorem labTouchNode_of_mem {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    labTouchNode core a = labTouch core (.inr ⟨core.adrsToKey a, a, ha, rfl⟩) := by
  simp only [labTouchNode, nodeAt_adrsToKey_of_mem core ha, Option.elim_some]

/-- At a ledger address the node value is the label of its node. -/
theorem labNode_of_mem {a : Adrs} (ha : a ∈ constructionAddresses vp)
    (fallback : OracleComp (labSpec core) core.Y) :
    labNode core a fallback = labRead core ⟨core.adrsToKey a, a, ha, rfl⟩ := by
  simp only [labNode, nodeAt_adrsToKey_of_mem core ha, Option.elim_some]

/-- At an address whose key is no node's the node value is the fallback. -/
theorem labNode_of_nodeAt_eq_none {a : Adrs} (h : nodeAt core (core.adrsToKey a) = none)
    (fallback : OracleComp (labSpec core) core.Y) : labNode core a fallback = fallback := by
  simp only [labNode, h, Option.elim_none]

variable (pkSeed : core.PkSeed)

/-! ## Lab callbacks -/

/-- The tweakable hash `T(PK.seed, a, xs)` in the lab: the label of the node at the key of `a`,
or the public query itself at an address whose key is no node's. -/
@[expose] noncomputable def labTl (a : Adrs) (xs : List core.Y) :
    OracleComp (labSpec core) core.Y :=
  labNode core a (PublicHash.tl core pkSeed a xs)

/-- The tweakable hash `F` in the lab. -/
@[expose] noncomputable def labF (a : Adrs) (y : core.Y) : OracleComp (labSpec core) core.Y :=
  labTl core pkSeed a [y]

/-- The tweakable hash `H` in the lab. -/
@[expose] noncomputable def labH (a : Adrs) (l r : core.Y) : OracleComp (labSpec core) core.Y :=
  labTl core pkSeed a [l, r]

/-! ## WOTS+ chain touches -/

/-- Touch cell `j` of WOTS+ chain `i` at `adrs`: the chain's secret at `j = 0`, the label of hash
step `j - 1` otherwise. -/
@[expose] noncomputable def labChainTouchCell (adrs : Adrs) (i : ℕ) :
    ℕ → OracleComp (labSpec core) Unit
  | 0 => labTouchSecret core (wotsSkAdrs adrs i)
  | j + 1 => labTouchNode core ((wotsChainAdrs adrs i).setHashAddress j)

/-- Touch cells `0, …, s - 1` of WOTS+ chain `i` at `adrs`, in order. -/
@[expose] noncomputable def labChainTouch (adrs : Adrs) (i : ℕ) :
    ℕ → OracleComp (labSpec core) Unit
  | 0 => pure ()
  | j + 1 => do
      labChainTouch adrs i j
      labChainTouchCell core adrs i j

section PredLabels

variable {Q : ∀ {α : Type}, OracleComp (labSpec core) α → Prop}
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : OracleComp (labSpec core) α)
    (ob : α → OracleComp (labSpec core) β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  (htouch : ∀ c, Q (labTouch core c)) (hread : ∀ κ, Q (labRead core κ))

include hpure htouch in
/-- A node touch satisfies `Q` when every touch does. -/
theorem labTouchNode_pred (a : Adrs) : Q (labTouchNode core a) := by
  unfold labTouchNode
  cases nodeAt core (core.adrsToKey a) <;> simp only [Option.elim_none, Option.elim_some]
  exacts [hpure (), htouch _]

include hpure htouch in
/-- A secret touch satisfies `Q` when every touch does. -/
theorem labTouchSecret_pred (a : Adrs) : Q (labTouchSecret core a) := by
  unfold labTouchSecret
  cases prfKeyOf core a <;> simp only [Option.elim_none, Option.elim_some]
  exacts [hpure (), htouch _]

include hread in
/-- A lab tweakable hash satisfies `Q` when every label read does and the public query at its
address does, should its key be no node's. -/
theorem labTl_pred {a : Adrs} {xs : List core.Y}
    (hpub : nodeAt core (core.adrsToKey a) = none → Q (PublicHash.tl core pkSeed a xs)) :
    Q (labTl core pkSeed a xs) := by
  unfold labTl labNode
  cases h : nodeAt core (core.adrsToKey a) <;> simp only [Option.elim_none, Option.elim_some]
  exacts [hpub h, hread _]

include hpure hbind htouch in
/-- The touches of a lab WOTS+ chain satisfy `Q` when every touch does. -/
theorem labChainTouch_pred (adrs : Adrs) (i : ℕ) : ∀ s, Q (labChainTouch core adrs i s)
  | 0 => hpure ()
  | j + 1 => hbind _ _ (labChainTouch_pred adrs i j) fun _ => by
      cases j
      exacts [labTouchSecret_pred core hpure htouch _, labTouchNode_pred core hpure htouch _]

end PredLabels

/-! ## Touch normal forms -/

section Secret

variable [SampleableType core.Y]

/-- The secret value at an address, as `deriveSecret` reads it: the derivation at its key at a
secret-key address. -/
@[expose] def labSecret (a : Adrs) : OracleComp (labSpec core) core.Y :=
  liftComp (deriveSecret core a) (labSpec core)

/-- At a secret-key address the lab secret is the derivation at its key. -/
theorem labSecret_of_isSecretKey {a : Adrs} (h : a.IsSecretKey) :
    labSecret core a =
      query (spec := labSpec core) (.inl (.inr (.inl ⟨core.adrsToKey a, a, h, rfl⟩))) := by
  simp only [labSecret, deriveSecret, h, ↓reduceDIte]
  rfl

/-- Read cell `s` of WOTS+ chain `i` at `adrs`: the secret at `s = 0`, the label of hash step
`s - 1` otherwise. At a step whose key is no node's, the step is computed from cell `s - 1` by the
public `F`. -/
@[expose] noncomputable def labChainRead (adrs : Adrs) (i : ℕ) :
    ℕ → OracleComp (labSpec core) core.Y
  | 0 => labSecret core (wotsSkAdrs adrs i)
  | j + 1 => labNode core ((wotsChainAdrs adrs i).setHashAddress j) do
      let y ← labChainRead adrs i j
      PublicHash.f core pkSeed ((wotsChainAdrs adrs i).setHashAddress j) y

/-- **The lab WOTS+ chain.** The value of chain `i` at `adrs` after `s` steps from its secret:
cells `0, …, s - 1` touched, then cell `s` read. -/
@[expose] noncomputable def labChain (adrs : Adrs) (i s : ℕ) : OracleComp (labSpec core) core.Y :=
  do
    labChainTouch core adrs i s
    labChainRead core pkSeed adrs i s

/-- **The lab FORS leaf.** The leaf at global index `t` under `adrs`: its secret touched, then the
leaf read. At a leaf whose key is no node's, the leaf is the public `F` of the secret. -/
@[expose] noncomputable def labForsLeaf (adrs : Adrs) (t : ℕ) : OracleComp (labSpec core) core.Y :=
  do
    labTouchSecret core (forsSkAdrs adrs t)
    labNode core (forsNodeAdrs adrs 0 t) do
      let x ← labSecret core (forsSkAdrs adrs t)
      PublicHash.f core pkSeed (forsNodeAdrs adrs 0 t) x

/-- At a ledger step the read of the next cell of a WOTS+ chain is the label of the step. -/
theorem labChainRead_succ_of_mem {adrs : Adrs} {i j : ℕ}
    (h : (wotsChainAdrs adrs i).setHashAddress j ∈ constructionAddresses vp) :
    labChainRead core pkSeed adrs i (j + 1) = labRead core ⟨_, _, h, rfl⟩ :=
  labNode_of_mem core h _

/-- At a ledger leaf the lab FORS leaf touches the leaf's secret and reads the leaf. -/
theorem labForsLeaf_of_mem {adrs : Adrs} {t : ℕ}
    (h : forsNodeAdrs adrs 0 t ∈ constructionAddresses vp) :
    labForsLeaf core pkSeed adrs t = (do
      labTouch core (.inl (.inl ⟨_, _, Adrs.isSecretKey_forsSkAdrs adrs t, rfl⟩))
      labRead core ⟨_, _, h, rfl⟩) := by
  rw [labForsLeaf, labTouchSecret_of_isSecretKey core (Adrs.isSecretKey_forsSkAdrs adrs t),
    labNode_of_mem core h]

section Pred

variable {Q : ∀ {α : Type}, OracleComp (labSpec core) α → Prop}
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : OracleComp (labSpec core) α)
    (ob : α → OracleComp (labSpec core) β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  (htouch : ∀ c, Q (labTouch core c)) (hread : ∀ κ, Q (labRead core κ))
  (hsecret : ∀ a : Adrs, a.IsSecretKey → Q (labSecret core a))

include hbind hread hsecret in
/-- The read of a lab WOTS+ chain satisfies `Q` when every label read does, the secret does at
secret-key addresses, and the public `F` does at every step below `s` whose key is no node's. -/
theorem labChainRead_pred (adrs : Adrs) (i : ℕ) : ∀ s,
    (∀ j < s, nodeAt core (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress j)) = none →
      ∀ y, Q (PublicHash.f core pkSeed ((wotsChainAdrs adrs i).setHashAddress j) y)) →
    Q (labChainRead core pkSeed adrs i s)
  | 0, _ => hsecret _ (Adrs.isSecretKey_wotsSkAdrs _ _)
  | j + 1, hpub => by
      unfold labChainRead labNode
      cases h : nodeAt core (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress j)) <;>
        simp only [Option.elim_none, Option.elim_some]
      · exact hbind _ _ (labChainRead_pred adrs i j fun j' hj' => hpub j' (by omega))
          (hpub j (by omega) h)
      · exact hread _

include hpure hbind htouch hread hsecret in
/-- A lab WOTS+ chain satisfies `Q` when every touch and label read does, the secret does at
secret-key addresses, and the public `F` does at every step below `s` whose key is no node's. -/
theorem labChain_pred (adrs : Adrs) (i s : ℕ)
    (hpub : ∀ j < s,
      nodeAt core (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress j)) = none →
      ∀ y, Q (PublicHash.f core pkSeed ((wotsChainAdrs adrs i).setHashAddress j) y)) :
    Q (labChain core pkSeed adrs i s) :=
  hbind _ _ (labChainTouch_pred core hpure hbind htouch adrs i s) fun _ =>
    labChainRead_pred core pkSeed hbind hread hsecret adrs i s hpub

include hpure hbind htouch hread hsecret in
/-- A lab FORS leaf satisfies `Q` when every touch and label read does, the secret does at
secret-key addresses, and the public `F` does at the leaf, should its key be no node's. -/
theorem labForsLeaf_pred (adrs : Adrs) (t : ℕ)
    (hpub : nodeAt core (core.adrsToKey (forsNodeAdrs adrs 0 t)) = none →
      ∀ x, Q (PublicHash.f core pkSeed (forsNodeAdrs adrs 0 t) x)) :
    Q (labForsLeaf core pkSeed adrs t) := by
  refine hbind _ _ (labTouchSecret_pred core hpure htouch _) fun _ => ?_
  unfold labNode
  cases h : nodeAt core (core.adrsToKey (forsNodeAdrs adrs 0 t)) <;>
    simp only [Option.elim_none, Option.elim_some]
  · exact hbind _ _ (hsecret _ (Adrs.isSecretKey_forsSkAdrs _ _)) (hpub h)
  · exact hread _

end Pred

/-- **The lab chain issues no public query.** At a WOTS+ instance of a layer position, a lab
chain of at most `w - 1` steps makes no query that a predicate holding only at public hash
queries counts. -/
theorem isQueryBoundP_labChain_wotsInstanceAdrs (pos : LayerPosition vp)
    (i : Fin vp.params.len) {s : ℕ} (hs : s ≤ vp.params.w - 1)
    (p : (labSpec core).Domain → Prop) [DecidablePred p]
    (hp : ∀ t, p t → ∃ q, t = .inl (.inl (.inr q))) :
    IsQueryBoundP (labChain core pkSeed (wotsInstanceAdrs pos) i s) p 0 := by
  have hq : ∀ t : (labSpec core).Domain, (∀ q, t ≠ .inl (.inl (.inr q))) →
      IsQueryBoundP (liftM ((labSpec core).query t) : OracleComp (labSpec core) _) p 0 :=
    fun t ht => (isQueryBoundP_query_iff p t 0).2 fun hpt => absurd (hp t hpt) fun ⟨q, hq⟩ =>
      ht q hq
  refine labChain_pred core pkSeed (Q := fun oa => IsQueryBoundP oa p 0)
    (fun x => isQueryBoundP_pure p x 0) (fun _ _ h h' => isQueryBoundP_bind h fun x _ => h' x)
    (fun c => hq _ fun _ => nofun) (fun κ => hq _ fun _ => nofun)
    (fun a ha => ?_) _ i s fun j hj h => ?_
  · rw [labSecret_of_isSecretKey core ha]
    exact hq _ fun _ => nofun
  · rw [nodeAt_adrsToKey_of_mem core
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (by omega))] at h
    exact absurd h nofun

/-! ## Lab components -/

/-- The `len` WOTS+ chain tops at `adrs`, each a lab chain of `w - 1` steps. -/
@[expose] noncomputable def labWotsPkGenTops (adrs : Adrs) :
    OracleComp (labSpec core) (Vector core.Y vp.params.len) :=
  Vector.ofFnM fun i => labChain core pkSeed adrs i.val (vp.params.w - 1)

/-- The WOTS+ signature on `msg` at `adrs`: chain `i` a lab chain of `chainStepsCore core msg i`
steps. -/
@[expose] noncomputable def labWotsSign (msg : core.Y) (adrs : Adrs) :
    OracleComp (labSpec core) (WotsSig vp.params core) :=
  Vector.ofFnM fun i => labChain core pkSeed adrs i.val (chainStepsCore core msg i.val)

/-- The XMSS leaf at keypair index `t` under `adrs`: the lab chain tops compressed by the lab
`T_len`. -/
@[expose] noncomputable def labXmssLeaf (adrs : Adrs) (t : ℕ) : OracleComp (labSpec core) core.Y :=
  do
    let tops ← labWotsPkGenTops core pkSeed (wotsLeafAdrs adrs t)
    labTl core pkSeed (wotsPkAdrs (wotsLeafAdrs adrs t)) tops.toList

/-- The height-`z`, index-`t` node of the XMSS tree at `adrs`, over lab leaves and the lab `H`. -/
@[expose] noncomputable def labXmssNode (adrs : Adrs) (z t : ℕ) :
    OracleComp (labSpec core) core.Y :=
  PerfectMerkleTree.merkleRootM (labXmssLeaf core pkSeed adrs)
    (xmssNodeHashWith (labH core pkSeed) adrs) z t

/-- The XMSS signature at leaf `idx` on `msg`: the authentication path through the lab tree, then
the lab WOTS+ signature. -/
@[expose] noncomputable def labXmssSign (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    OracleComp (labSpec core) (XmssSig vp.params core) := do
  let path ← PerfectMerkleTree.intrinsicAuthPathM (labXmssLeaf core pkSeed adrs)
    (xmssNodeHashWith (labH core pkSeed) adrs) idx vp.params.hp
  let sig ← labWotsSign core pkSeed msg (wotsLeafAdrs adrs idx)
  return ⟨sig, path⟩

/-- The FORS signature on digest `md` at `adrs`: for each tree, the authentication path through
the lab tree and the secret at the indexed leaf. -/
@[expose] noncomputable def labForsSign (md : List Byte) (adrs : Adrs) :
    OracleComp (labSpec core) (ForsSigCore vp.params core) :=
  Vector.ofFnM fun i : Fin vp.params.k => do
    let idx := i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val
    let path ← PerfectMerkleTree.intrinsicAuthPathM (labForsLeaf core pkSeed adrs)
      (forsNodeHashWith (labH core pkSeed) adrs) idx vp.params.a
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
      let sig ← labXmssSign core pkSeed msg pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ ← xmssPkFromSigWith core (labF core pkSeed) (labTl core pkSeed) (labH core pkSeed)
          pos.leaf.val sig msg pos.toAdrs
        return #v[sig]
      else
        return #v[sig]
  | layers + 2, hremaining, msg => do
      let sig ← labXmssSign core pkSeed msg pos.toAdrs pos.leaf.val
      let root ← xmssPkFromSigWith core (labF core pkSeed) (labTl core pkSeed)
        (labH core pkSeed) pos.leaf.val sig msg pos.toAdrs
      let next := pos.next (by omega)
      let rest ← labSignFromPosition false next (layers + 1) (by simp [next]; omega) root
      return rest.insertIdx 0 sig

/-- Key generation in the lab: the root of the top-layer XMSS tree. -/
@[expose] noncomputable def labKeygen : OracleComp (labSpec core) core.Y :=
  labXmssNode core pkSeed (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) vp.params.hp 0

/-- Signing in the lab at randomizer `R`: `H_msg` is a public query, FORS signing is
`labForsSign`, the FORS public key is recovered by `forsPkFromSigWith` at the lab callbacks, and
the hypertree signature is `labSignFromPosition`. -/
@[expose] noncomputable def labSignInternal (msg : List Byte) (pkRoot R : core.Y) :
    OracleComp (labSpec core) (GeneralScheme.SignatureCore vp core) := do
  let digest ← PublicHash.hmsg core R pkSeed pkRoot msg
  let parts := splitDigest vp.params digest
  let forsSig ← labForsSign core pkSeed parts.md.toList parts.forsAdrs
  let forsPk ← forsPkFromSigWith core (labF core pkSeed) (labH core pkSeed) (labTl core pkSeed)
    forsSig parts.md.toList parts.forsAdrs
  let htSig ← labSignFromPosition core pkSeed (vp.params.d == 1) (LayerPosition.initial vp parts)
    vp.params.d (by simp) forsPk
  return ⟨R, forsSig, htSig⟩

/-! ## The lab scheme and experiment -/

variable [DecidableEq core.Y]

/-- **The lab scheme at public seed `pkSeed`.** Key generation is `labKeygen`; signing draws
`opt_rand` from `optRand`, the randomizer as the derivation at `(opt_rand, M)`, and signs with
`labSignInternal` at `pkSeed`; verification is FIPS 205 Algorithm 20, with public queries. The
secret key is the public key. -/
@[expose] noncomputable def labScheme (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) :
    SignatureAlg (OracleComp (labSpec core)) (List Byte) (PublicKeyCore core)
      (PublicKeyCore core) (GeneralScheme.SignatureCore vp core) where
  keygen := do
    let pkRoot ← labKeygen core pkSeed
    return (⟨pkSeed, pkRoot⟩, ⟨pkSeed, pkRoot⟩)
  sign pk sk msg := do
    let R ← liftComp ((do
      let addrnd ← (optRand pk : ProbComp core.Y)
      query (spec := deriveSpec core) (.inr (.inr (addrnd, msg)))) :
        OracleComp (deriveSpec core) core.Y) (labSpec core)
    labSignInternal core pkSeed msg sk.pkRoot R
  verify pk msg sig := GeneralScheme.verifyInternalM vp core msg sig pk

/-! ## The lifted secret-free scheme -/

/-- Key generation of the lifted secret-free scheme is provider-parametric key generation with
every secret value drawn from `labSecret`. -/
theorem map_labLiftHom_deriveScheme_keygen (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) :
    ((deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom).keygen = do
      let pkRoot ← GeneralScheme.keygenInternalWithSecretM core (labSecret core) pkSeed
      return (⟨pkSeed, pkRoot⟩, ⟨pkSeed, pkRoot⟩) := by
  rw [map_keygen, deriveScheme, MonadHom.mmap_bind,
    GeneralScheme.keygenInternalWithSecretM_natural core (labLiftHom core) (deriveSecret core)
      (labSecret core) (fun _ _ => rfl)]
  simp

/-- Signing of the lifted secret-free scheme draws the randomizer as `labScheme` does and signs
with every secret value drawn from `labSecret`. -/
theorem map_labLiftHom_deriveScheme_sign (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (pk sk : PublicKeyCore core) (msg : List Byte) :
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
theorem map_labLiftHom_deriveScheme_verify (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    ((deriveScheme core optRand pkSeed).map (labLiftHom core).toMonadHom).verify pk msg sig =
      (labScheme core optRand pkSeed).verify pk msg sig :=
  GeneralScheme.verifyInternalM_natural vp core (labLiftHom core) msg sig pk

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

end Secret

end SLHDSA.Security
