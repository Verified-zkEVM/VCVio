/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CacheDecomposition
public import HashSig.SLHDSA.Security.HmsgWitnesses
public import HashSig.SLHDSA.Security.RomTranscript
public import HashSig.SLHDSA.WotsInjectivity
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Collision

/-!
# The random-oracle bad events and the descent from the cached root

A transcript `o : RomOutcome vp core` of the EUF-CMA game together with the final cache
`c : PublicHash.Cache core` of the lazy public-hash oracle is what `romRunFull` returns.  This
module defines three events over such a pair and proves the deterministic case analyses that
descend a verified forgery from the public root, through the hypertree layers the forgery's own
verification replays, into one of them.  Honest values are read off the cache through the
readers of `HashSig.SLHDSA.Security.CacheReaders`, never through a total hash function.

**Same-address target collision** (`TargetCollision`).  Two cache entries at one tweakable-hash
key (same public seed, same encoded address) with equal answers and different inputs, one of
which is an *honest entry* (`HonestEntry`): a `thash` query whose input is a value the key holder
computes, with the honest values that input rests on settled in the cache.  The honest side is
what makes this a target collision on at most one honest entry per address rather than a free
collision search over the whole cache.

**Hidden-value hit** (`HiddenHit`).  The forgery's verification replay under the cache produces a
value the signing oracle never revealed: a WOTS+ chain value at a step below the one the honest
message at that leaf selects (or at any step of an unused leaf), reached by the forger's own chain
segment from its signature entry; or a FORS secret at a coordinate no logged signature opened,
carried verbatim in the forgery.  This is a predicate on the forger's replay under the cache, not
on the cache alone: the signer itself caches every hidden chain value while computing the chain
tops, so the presence of such a value in the cache says nothing.  What the event records is that
the *forger's* signature entry, run forward at the address verification uses, lands on it.

**Interleaved-target coverage** (`ItsrCovered`).  Every FORS coordinate the forgery's `H_msg`
digest selects is selected by the digest of some logged signature.  A cache predicate over the
forger's digest (`ForgerDigest`) and the logged digests (`LoggedDigest`); freshness of the
forger's `H_msg` point is not part of it.

The case analyses.  `xmssPkFromSig?_cases` is the XMSS stop: an XMSS signature whose recovered
root is settled at the settled honest root of the same tree yields a target collision or settled
forger chain tops equal to the settled honest ones (`PerfectMerkleTree.climbM_merkleRootM_cases`
on the leaf's root path).  `xmss_top_cases` applies it to the top tree on the support of
`romRunFull`, where key generation settles the honest root at the public root.  `wotsChain_cases`
and `wotsLeaf_cases` descend through the WOTS+ leaf: equal settled chain tops give a target
collision on some `F` entry or the forger's signature entry on every chain is the honest chain
value at the step its message selects.  `xmssLayer_cases` is one hypertree layer: a target
collision, a hidden-value hit (an unused leaf, or a used leaf with a different message through
`chainStepsCore_two_encodings`), or the leaf is used with the same honest message, so the descent
continues from the settled honest child root.  `forgerLayers_of_recoverFromPositionM` reads the
forger's message and settled XMSS recovery at every layer off a settled verification replay.
`fors_cases` is the FORS stop: a target collision on the `T_k` compression, an `H` node or an `F`
leaf, or interleaved-target coverage, or an uncovered coordinate at which the forgery carries the
honest secret.

## Scope

* Everything here is deterministic on the support of `romRunFull`: no probability is bounded and
  the query budget does not appear.  The cache is a classical table.
* The glue that composes these case analyses into a single statement that a winning forgery
  leaves one of the three events in the final cache is not in this module.  In particular, the
  fact that a used leaf's honest message is settled by the logged signature's own signing run is
  a hypothesis of `xmssLayer_cases`, not a theorem here.
* No relation between the events and any tweakable-hash or ITSR game is proved here.
* Nothing here is quantum.

## Labels

Twenty-six declarations.

*Honest entries and the target collision*: `HonestEntry`, `TargetCollision`.

*Digests, used leaves and honest messages*: `LoggedDigest`, `ForgerDigest`, `UsedLeaf`,
`childTreeAdrs`, `childTreeAdrs_next`, `forsInstanceAdrs`, `forsInstanceAdrs_initial`,
`honestMessage?`, `HiddenChainValue`, `UnopenedCoord`.

*The forger's replay*: `forgerMessage?`, `ForgerLayer`, `HiddenHit`, `ItsrCovered`.

*XMSS stops*: `xmssPkFromSig?_cases`, `exists_xmssPkFromSigM_top_of_recoverFromPositionM`,
`xmss_top_cases`.

*WOTS+ chains and one XMSS layer*: `wotsChain_cases`, `wotsLeaf_cases`, `xmssLayer_cases`.

*The forger's layers*: `recoverFromPositionM_pos_congr`, `forgerLayers_of_recoverFromPositionM`.

*The FORS stop*: `unopenedCoord_of_notMem`, `fors_cases`.

## References

- NIST FIPS 205, §6--§9, Algorithms 9--20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec GeneralHypertree SignatureAlg CanonicalGames

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## Honest entries and the target collision -/

/-- A `thash` query whose input is a value the key holder computes, read off the cache.  Each
constructor names the honest values that must be settled for the input to be the honest one: the
two honest children of a node of positive height (`xmssNode`, `forsNode`), the honest chain tops
(`wotsPk`), the honest chain prefix (`wotsChain`), the honest tree roots (`forsRoots`).  A FORS
leaf secret is a `PRF` value and needs nothing settled.  Addresses are unconstrained; the height
bound keeps the two-element node entries off the height-`0` keys, which are the leaf keys. -/
inductive HonestEntry (o : RomOutcome vp core) (c : PublicHash.Cache core) :
    (publicHashSpec core).Domain → Prop
  | xmssNode (adrs : Adrs) (h i : ℕ) (l r : core.Y) (hh : 0 < h)
      (hl : xmssNode? core c o.sk.skSeed o.pk.pkSeed adrs (h - 1) (2 * i) = some l)
      (hr : xmssNode? core c o.sk.skSeed o.pk.pkSeed adrs (h - 1) (2 * i + 1) = some r) :
      HonestEntry o c (.thash o.pk.pkSeed (core.adrsToKey (xmssNodeAdrs adrs h i)) [l, r])
  | wotsPk (adrs : Adrs) (tops : Vector core.Y vp.params.len)
      (h : wotsPkGenTops? core c o.sk.skSeed o.pk.pkSeed adrs = some tops) :
      HonestEntry o c (.thash o.pk.pkSeed (core.adrsToKey (wotsPkAdrs adrs)) tops.toList)
  | wotsChain (adrs : Adrs) (i t : ℕ) (v : core.Y)
      (h : chain? core c o.pk.pkSeed (wotsChainAdrs adrs i)
        (core.PRF o.pk.pkSeed o.sk.skSeed (wotsSkAdrs adrs i)) 0 t = some v) :
      HonestEntry o c
        (.thash o.pk.pkSeed (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress t)) [v])
  | forsLeaf (adrs : Adrs) (t : ℕ) :
      HonestEntry o c (.thash o.pk.pkSeed (core.adrsToKey (forsNodeAdrs adrs 0 t))
        [forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t])
  | forsNode (adrs : Adrs) (h i : ℕ) (l r : core.Y) (hh : 0 < h)
      (hl : forsNode? core c o.sk.skSeed o.pk.pkSeed adrs (h - 1) (2 * i) = some l)
      (hr : forsNode? core c o.sk.skSeed o.pk.pkSeed adrs (h - 1) (2 * i + 1) = some r) :
      HonestEntry o c (.thash o.pk.pkSeed (core.adrsToKey (forsNodeAdrs adrs h i)) [l, r])
  | forsRoots (adrs : Adrs) (roots : Vector core.Y vp.params.k)
      (h : ∀ i : Fin vp.params.k,
        forsNode? core c o.sk.skSeed o.pk.pkSeed adrs vp.params.a i.val = some roots[i]) :
      HonestEntry o c (.thash o.pk.pkSeed (core.adrsToKey (forsPkAdrs adrs)) roots.toList)

/-- Two cache entries at one `thash` key (same public seed, same encoded address) with equal
answers and different inputs, one of which is an honest entry. -/
@[expose] def TargetCollision (o : RomOutcome vp core) (c : PublicHash.Cache core) : Prop :=
  ∃ (pkSeed : core.PkSeed) (key : core.AdrsKey) (xs ys : List core.Y) (v : core.Y),
    HonestEntry o c (.thash pkSeed key xs) ∧ xs ≠ ys ∧
    c (.thash pkSeed key xs) = some v ∧ c (.thash pkSeed key ys) = some v

/-! ## Digests, used leaves and honest messages -/

/-- The `H_msg` digest of a logged signature, read off the cache. -/
@[expose] def LoggedDigest (o : RomOutcome vp core) (c : PublicHash.Cache core)
    (e : (t : (List Byte →ₒ GeneralScheme.SignatureCore vp core).Domain) ×
      (List Byte →ₒ GeneralScheme.SignatureCore vp core).Range t)
    (digest : Bytes vp.params.m) : Prop :=
  c (.hmsg e.2.randomness o.pk.pkSeed o.pk.pkRoot (emptyContextMessage e.1)) = some digest

/-- The `H_msg` digest of the forgery, read off the cache. -/
@[expose] def ForgerDigest (o : RomOutcome vp core) (c : PublicHash.Cache core)
    (digest : Bytes vp.params.m) : Prop :=
  c (.hmsg o.sig.randomness o.pk.pkSeed o.pk.pkRoot (emptyContextMessage o.msg)) = some digest

/-- Some logged signature's hypertree position at layer `j` is `pos`. -/
@[expose] def UsedLeaf (o : RomOutcome vp core) (c : PublicHash.Cache core) (j : Fin vp.params.d)
    (pos : LayerPosition vp) : Prop :=
  ∃ e ∈ o.log, ∃ digest, LoggedDigest o c e digest ∧
    LayerPosition.atLayer vp (splitDigest vp.params digest) j = pos

/-- The address of the XMSS tree one layer below `pos` whose root the leaf at `pos` signs
(`LayerPosition.next` in reverse).  Meaningful at `0 < pos.layer`. -/
@[expose] def childTreeAdrs (pos : LayerPosition vp) : Adrs :=
  layerAdrs (pos.layer.val - 1) (pos.tree.val * 2 ^ vp.params.hp + pos.leaf.val)

/-- The child tree of the next position is the current tree. -/
theorem childTreeAdrs_next (pos : LayerPosition vp) (h : pos.layer.val + 1 < vp.params.d) :
    childTreeAdrs (pos.next h) = pos.toAdrs := by
  simp only [childTreeAdrs, LayerPosition.next_layer_val, Nat.add_sub_cancel,
    LayerPosition.next_tree_val, LayerPosition.next_leaf_val, Nat.div_add_mod']
  rfl

/-- The FORS instance address the leaf at a layer-zero position signs for
(`DigestParts.forsAdrs` at `LayerPosition.initial`). -/
@[expose] def forsInstanceAdrs (pos : LayerPosition vp) : Adrs :=
  ((Adrs.zero.setTreeAddress pos.tree.val).setTypeAndClear .forsTree).setKeyPairAddress
    pos.leaf.val

/-- The FORS instance address of the initial position is the digest's. -/
theorem forsInstanceAdrs_initial (parts : DigestParts vp.params) :
    forsInstanceAdrs (LayerPosition.initial vp parts) = parts.forsAdrs := by rfl

/-- The honest message signed at `pos`, read off the cache: the honest FORS public key of the
instance at layer `0`, the honest root of the child tree above (FIPS 205 Algorithms 12 and 19).
A used leaf reveals exactly the chain steps this message selects. -/
@[expose] def honestMessage? (c : PublicHash.Cache core) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) : Option core.Y :=
  if pos.layer.val = 0 then forsPkGen? core c sk pk (forsInstanceAdrs pos)
  else xmssRoot? core c sk pk (childTreeAdrs pos)

/-- The chain value at step `t` of chain `i` of the WOTS+ leaf at `pos` is hidden: the leaf is
unused, or it is used and `t` is below the step its honest message selects on chain `i`. -/
@[expose]
def HiddenChainValue (o : RomOutcome vp core) (c : PublicHash.Cache core) (j : Fin vp.params.d)
    (pos : LayerPosition vp) (i t : ℕ) : Prop :=
  UsedLeaf o c j pos →
    ∃ m, honestMessage? c o.sk.skSeed o.pk.pkSeed pos = some m ∧ t < chainStepsCore core m i

/-- No logged signature opened the FORS coordinate (instance `adrs`, global leaf `t`). -/
@[expose]
def UnopenedCoord (o : RomOutcome vp core) (c : PublicHash.Cache core) (adrs : Adrs) (t : ℕ) :
    Prop :=
  ∀ e ∈ o.log, ∀ digest, LoggedDigest o c e digest → ∀ i : Fin vp.params.k,
    ¬ ((splitDigest vp.params digest).forsAdrs = adrs ∧
      forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val = t)

/-! ## The forger's replay -/

/-- The message the verification replay presents to hypertree layer `j`, read off the cache:
the FORS public key at layer `0`, then the root each XMSS signature recovers. -/
@[expose]
def forgerMessage? (c : PublicHash.Cache core) (pk : core.PkSeed) (parts : DigestParts vp.params)
    (sig : GeneralHypertree.Signature vp core) (forsPk : core.Y) :
    (j : ℕ) → j < vp.params.d → Option core.Y
  | 0, _ => some forsPk
  | j + 1, hj => (forgerMessage? c pk parts sig forsPk j (by omega)).bind fun m =>
      xmssPkFromSig? core c (LayerPosition.atLayer vp parts ⟨j, by omega⟩).leaf.val sig[j] m pk
        (LayerPosition.atLayer vp parts ⟨j, by omega⟩).toAdrs

/-- The verification replay of the forgery enters layer `j` at position `pos` with message
`m`: the forger's digest and FORS public key are settled, and so is every XMSS recovery below
layer `j`. -/
@[expose] def ForgerLayer (o : RomOutcome vp core) (c : PublicHash.Cache core) (j : Fin vp.params.d)
    (pos : LayerPosition vp) (m : core.Y) : Prop :=
  ∃ digest forsPk, ForgerDigest o c digest ∧
    forsPkFromSig? core c o.sig.fors (splitDigest vp.params digest).md.toList o.pk.pkSeed
      (splitDigest vp.params digest).forsAdrs = some forsPk ∧
    pos = LayerPosition.atLayer vp (splitDigest vp.params digest) j ∧
    forgerMessage? c o.pk.pkSeed (splitDigest vp.params digest) o.sig.hypertree forsPk j j.isLt =
      some m

/-- The forgery's replay under the cache produces a hidden honest value.  Either a WOTS+ chain
value at a hidden step `t` of chain `i` of the leaf the replay enters at layer `j`, reached by the
forger's chain from its own signature entry at the step its message selects; or a FORS secret at
a coordinate no logged signature opened, carried verbatim in the forgery.  In the WOTS+ case the
forger's digest, FORS public key and lower-layer roots, the honest chain prefix and the forger's
chain segment are settled, and for a used leaf so is the honest message.  A FORS secret is a
`PRF` value and needs nothing settled. -/
@[expose] def HiddenHit (o : RomOutcome vp core) (c : PublicHash.Cache core) : Prop :=
  (∃ (j : Fin vp.params.d) (pos : LayerPosition vp) (m : core.Y) (i : Fin vp.params.len)
      (t : ℕ) (v : core.Y),
    ForgerLayer o c j pos m ∧ HiddenChainValue o c j pos i.val t ∧
    chain? core c o.pk.pkSeed (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)
      (core.PRF o.pk.pkSeed o.sk.skSeed (wotsSkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val))
      0 t = some v ∧
    chainStepsCore core m i.val ≤ t ∧
    chain? core c o.pk.pkSeed (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)
      (o.sig.hypertree[j]).wots[i] (chainStepsCore core m i.val)
      (t - chainStepsCore core m i.val) = some v) ∨
  (∃ (digest : Bytes vp.params.m) (i : Fin vp.params.k),
    ForgerDigest o c digest ∧
    UnopenedCoord o c (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val) ∧
    (o.sig.fors[i]).sk = forsSkGenCore core o.sk.skSeed o.pk.pkSeed
      (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val))

/-- Every FORS coordinate the forgery's `H_msg` digest selects is selected by the digest of some
logged signature, all digests read off the cache. -/
@[expose] def ItsrCovered (o : RomOutcome vp core) (c : PublicHash.Cache core) : Prop :=
  ∃ digest, ForgerDigest o c digest ∧
    ∀ idx ∈ hmsgIndices vp.params digest, ∃ e ∈ o.log, ∃ digest',
      LoggedDigest o c e digest' ∧ idx ∈ hmsgIndices vp.params digest'

/-! ## XMSS stops -/

/-- An XMSS signature at leaf `idx` whose recovered root is settled at the settled honest root of
the same tree yields either a same-address target collision, or settled forger chain tops equal
to the settled honest chain tops at that leaf.  Both collision entries are cached: the honest one
because the honest root settles the whole tree, the forger's because verification replayed
it. -/
theorem xmssPkFromSig?_cases (o : RomOutcome vp core) (c : PublicHash.Cache core) (adrs : Adrs)
    (idx : ℕ) (hidx : idx < 2 ^ vp.params.hp) (sig : XmssSig vp.params core) (msg : core.Y)
    {r : core.Y} (hforge : xmssPkFromSig? core c idx sig msg o.pk.pkSeed adrs = some r)
    (hhonest : xmssRoot? core c o.sk.skSeed o.pk.pkSeed adrs = some r) :
    TargetCollision o c ∨
    ∃ tops : Vector core.Y vp.params.len,
      simulateQ c.toPartialImpl
        (wotsPkFromSigTopsM core sig.wots msg o.pk.pkSeed (wotsLeafAdrs adrs idx)) = some tops ∧
      wotsPkGenTops? core c o.sk.skSeed o.pk.pkSeed (wotsLeafAdrs adrs idx) = some tops := by
  obtain ⟨leaf', ⟨tops', htops', hTl'⟩, hclimb⟩ :=
    (simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff core c idx sig msg o.pk.pkSeed adrs).mp
      hforge
  have hroot : simulateQ c.toPartialImpl (PerfectMerkleTree.merkleRootM
      (xmssLeafM core o.sk.skSeed o.pk.pkSeed adrs) (xmssNodeHashM core o.pk.pkSeed adrs)
      vp.params.hp 0) = some r := hhonest
  rcases PerfectMerkleTree.climbM_merkleRootM_cases c.toPartialImpl _ _ idx vp.params.hp 0
      (Nat.div_eq_of_lt hidx) leaf' sig.auth.toList (by simp) hclimb hroot with
    hleaf | ⟨h, l, rr, l', r', v, hh, -, hne, hl, hr, hq, hq'⟩
  · simp only [xmssLeafM, xmssLeafWith, wotsPkGenWith, simulateQ_bind_eq_some_iff,
      simulateQ_toPartialImpl_tl] at hleaf
    obtain ⟨tops, htops, hTl⟩ := hleaf
    by_cases heq : tops = tops'
    · subst heq
      exact Or.inr ⟨tops, htops', htops⟩
    · exact Or.inl ⟨o.pk.pkSeed, core.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs idx)),
        tops.toList, tops'.toList, leaf', HonestEntry.wotsPk _ tops htops,
        mt Vector.toList_inj.mp heq, hTl, hTl'⟩
  · simp only [xmssNodeHashM, xmssNodeHashWith, simulateQ_toPartialImpl_h] at hq hq'
    refine Or.inl ⟨o.pk.pkSeed, core.adrsToKey (xmssNodeAdrs adrs h (idx / 2 ^ h)), [l, rr],
      [l', r'], v, HonestEntry.xmssNode adrs h (idx / 2 ^ h) l rr hh hl hr, fun hlist => hne ?_,
      hq, hq'⟩
    simp only [List.cons.injEq, and_true] at hlist
    exact Prod.ext hlist.1 hlist.2

/-- A settled hypertree recovery (FIPS 205 Algorithm 13) over `layers > 0` layers ends with a
settled XMSS recovery on its last signature at a final-layer position. -/
theorem exists_xmssPkFromSigM_top_of_recoverFromPositionM (c : PublicHash.Cache core)
    (pk : core.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : core.Y) (sigs : Vector (XmssSig vp.params core) layers) {root : core.Y},
      0 < layers →
      simulateQ c.toPartialImpl (recoverFromPositionM vp core pk pos layers h msg sigs) =
        some root →
      ∃ (top : LayerPosition vp) (m : core.Y), top.layer.val + 1 = vp.params.d ∧
        simulateQ c.toPartialImpl
          (xmssPkFromSigM core top.leaf.val (sigs[layers - 1]'(by omega)) m pk top.toAdrs) =
            some root
  | 0, _, _, _, _, _, hl, _ => absurd hl (Nat.lt_irrefl 0)
  | 1, pos, h, msg, sigs, root, _, hrec => ⟨pos, msg, h,
      (simulateQ_toPartialImpl_recoverFromPositionM_one_eq_some_iff core c pk pos h msg sigs).mp
        hrec⟩
  | k + 2, pos, h, msg, sigs, root, _, hrec => by
    obtain ⟨r, -, hrest⟩ :=
      (simulateQ_toPartialImpl_recoverFromPositionM_add_two_eq_some_iff core c pk pos k h msg
        sigs).mp hrec
    obtain ⟨top, m, htop, hx⟩ := exists_xmssPkFromSigM_top_of_recoverFromPositionM c pk (k + 1)
      _ _ r sigs.tail (Nat.succ_pos k) hrest
    exact ⟨top, m, htop, by simpa [Nat.add_comm] using hx⟩

section Run

variable [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType core.PkSeed]

/-- On the support of the instrumented run, a verified forgery yields either a same-address
target collision in the final cache, or a final-layer position of the top tree at which the
forger's settled WOTS+ chain tops equal the settled honest ones. -/
theorem xmss_top_cases
    (adv : unforgeableAdv (generalAlgM (m := OracleComp (unifSpec + publicHashSpec core)) vp core))
    {z : RomOutcome vp core × PublicHash.Cache core} (hz : z ∈ support (romRunFull core adv))
    (hv : z.1.verified = true) :
    TargetCollision z.1 z.2 ∨
    ∃ (top : LayerPosition vp) (m : core.Y) (tops : Vector core.Y vp.params.len),
      top.layer.val + 1 = vp.params.d ∧ top.toAdrs = layerAdrs (vp.params.d - 1) 0 ∧
      simulateQ z.2.toPartialImpl (wotsPkFromSigTopsM core
        (z.1.sig.hypertree[vp.params.d - 1]'(Nat.sub_one_lt vp.valid.d_pos.ne')).wots m
        z.1.pk.pkSeed (wotsLeafAdrs top.toAdrs top.leaf.val)) = some tops ∧
      wotsPkGenTops? core z.2 z.1.sk.skSeed z.1.pk.pkSeed (wotsLeafAdrs top.toAdrs top.leaf.val) =
        some tops := by
  obtain ⟨⟨skSeed, skPrf, pkSeed, hk⟩, -, hver⟩ :=
    simulateQ_toPartialImpl_eq_some_of_mem_support_romRunFull core adv hz
  rw [hv, simulateQ_toPartialImpl_verifyInternalM_eq_some_true_iff] at hver
  obtain ⟨digest, forsPk, -, -, hpk⟩ := hver
  rw [simulateQ_toPartialImpl_pkFromSigM_eq] at hpk
  obtain ⟨top, m, htop, hx⟩ := exists_xmssPkFromSigM_top_of_recoverFromPositionM z.2 _ _ _ _ _ _
    vp.valid.d_pos hpk
  rw [simulateQ_toPartialImpl_keygenInternalM_eq_some_iff] at hk
  obtain ⟨pkRoot, hroot, hpkeq, hskeq⟩ := hk
  have hadrs := LayerPosition.toAdrs_eq_layerAdrs_of_isFinal top htop
  have hhonest :
      xmssRoot? core z.2 z.1.sk.skSeed z.1.pk.pkSeed top.toAdrs = some z.1.pk.pkRoot := by
    rw [hadrs, ← hpkeq, ← hskeq]
    exact hroot
  exact (xmssPkFromSig?_cases z.1 z.2 top.toAdrs top.leaf.val top.leaf.isLt _ m hx hhonest).imp
    id fun ⟨tops, htops', htops⟩ => ⟨top, m, tops, htop, hadrs, htops', htops⟩

end Run

/-! ## WOTS+ chains and one XMSS layer -/

/-- A settled forger chain from `x` at step `a` that reaches the settled honest chain top of
chain `i` either collides with the honest chain (a same-address `F` target collision, both entries
cached) or starts at the honest chain value at step `a`. -/
theorem wotsChain_cases (o : RomOutcome vp core) (c : PublicHash.Cache core) (adrs : Adrs)
    (i a : ℕ) (ha : a ≤ vp.params.w - 1) (x top : core.Y)
    (hforge : chain? core c o.pk.pkSeed (wotsChainAdrs adrs i) x a (vp.params.w - 1 - a) =
      some top)
    (hhonest : chain? core c o.pk.pkSeed (wotsChainAdrs adrs i)
      (core.PRF o.pk.pkSeed o.sk.skSeed (wotsSkAdrs adrs i)) 0 (vp.params.w - 1) = some top) :
    TargetCollision o c ∨
      chain? core c o.pk.pkSeed (wotsChainAdrs adrs i)
        (core.PRF o.pk.pkSeed o.sk.skSeed (wotsSkAdrs adrs i)) 0 a = some x := by
  obtain ⟨b, hb⟩ : ∃ b, vp.params.w - 1 = a + b := ⟨vp.params.w - 1 - a, by omega⟩
  rw [show vp.params.w - 1 - a = b by omega] at hforge
  rw [hb, chain?_add_eq_some_iff, Nat.zero_add] at hhonest
  obtain ⟨va, hva, hsuffix⟩ := hhonest
  rcases chain?_diverge core c o.pk.pkSeed _ x va a b hforge hsuffix with
    h | ⟨j, hj, u', v', w', hne, hu', hv', hqu, hqv⟩
  · exact Or.inr (h ▸ hva)
  · refine Or.inl ⟨o.pk.pkSeed, core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress (a + j)),
      [v'], [u'], w', HonestEntry.wotsChain adrs i (a + j) v' ?_, fun h => hne ?_, hqv, hqu⟩
    · rw [chain?_add_eq_some_iff]
      exact ⟨va, hva, by rwa [Nat.zero_add]⟩
    · simp only [List.cons.injEq, and_true] at h
      exact h.symm

/-- Forger chain tops settled at the settled honest chain tops yield either a same-address
target collision, or the forger's WOTS+ signature entry on every chain is the honest chain value
at the step its message selects. -/
theorem wotsLeaf_cases (o : RomOutcome vp core) (c : PublicHash.Cache core) (adrs : Adrs)
    (sig : WotsSig vp.params core) (m' : core.Y) (tops : Vector core.Y vp.params.len)
    (hforge : simulateQ c.toPartialImpl (wotsPkFromSigTopsM core sig m' o.pk.pkSeed adrs) =
      some tops)
    (hhonest : wotsPkGenTops? core c o.sk.skSeed o.pk.pkSeed adrs = some tops) :
    TargetCollision o c ∨
      ∀ i : Fin vp.params.len, chain? core c o.pk.pkSeed (wotsChainAdrs adrs i.val)
        (core.PRF o.pk.pkSeed o.sk.skSeed (wotsSkAdrs adrs i.val)) 0
        (chainStepsCore core m' i.val) = some sig[i] := by
  rw [simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff] at hforge
  rw [wotsPkGenTops?, simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_iff] at hhonest
  refine or_iff_not_imp_left.mpr fun hcoll i => ?_
  exact (wotsChain_cases o c adrs i.val _ (chainStepsCore_le core m' i.val) sig[i.val] tops[i]
    (hforge i) (hhonest i)).resolve_left hcoll

/-- One XMSS layer of the descent.  At a position the forger's replay enters at layer `j` with
message `m'`, if the forger's XMSS recovery is settled at the settled honest root there, then
either a same-address target collision, or a hidden-value hit (the leaf is unused, or it is used
with a different honest message, so some chain has a strictly lower honest step), or the leaf is
used and `m'` is its honest message.  The hypothesis `hmsg` supplies the settled honest message of
a used leaf. -/
theorem xmssLayer_cases (laws : core.ByteLaws) (o : RomOutcome vp core)
    (c : PublicHash.Cache core) (j : Fin vp.params.d) (pos : LayerPosition vp) (m' : core.Y)
    {r : core.Y} (hlayer : ForgerLayer o c j pos m')
    (hforge : xmssPkFromSig? core c pos.leaf.val (o.sig.hypertree[j]) m' o.pk.pkSeed pos.toAdrs =
      some r)
    (hhonest : xmssRoot? core c o.sk.skSeed o.pk.pkSeed pos.toAdrs = some r)
    (hmsg : UsedLeaf o c j pos → ∃ m, honestMessage? c o.sk.skSeed o.pk.pkSeed pos = some m) :
    TargetCollision o c ∨ HiddenHit o c ∨
      (UsedLeaf o c j pos ∧ honestMessage? c o.sk.skSeed o.pk.pkSeed pos = some m') := by
  rcases xmssPkFromSig?_cases o c pos.toAdrs pos.leaf.val pos.leaf.isLt _ m' hforge hhonest with
    h | ⟨tops, htops', htops⟩
  · exact Or.inl h
  rcases wotsLeaf_cases o c _ _ m' tops htops' htops with h | hall
  · exact Or.inl h
  by_cases hused : UsedLeaf o c j pos
  · obtain ⟨m, hm⟩ := hmsg hused
    by_cases hmm : m = m'
    · exact Or.inr (Or.inr ⟨hused, hmm ▸ hm⟩)
    · obtain ⟨i, hi, hlt⟩ := chainStepsCore_two_encodings (core := core) vp.valid laws (Ne.symm hmm)
      exact Or.inr (Or.inl (Or.inl ⟨j, pos, m', ⟨i, hi⟩, chainStepsCore core m' i, _, hlayer,
        fun _ => ⟨m, hm, hlt⟩, hall ⟨i, hi⟩, le_rfl, by simp⟩))
  · exact Or.inr (Or.inl (Or.inl ⟨j, pos, m', ⟨0, Params.len_pos _⟩, chainStepsCore core m' 0, _,
      hlayer, fun h => absurd h hused, hall ⟨0, Params.len_pos _⟩, le_rfl, by simp⟩))

/-! ## The forger's layers -/

/-- Algorithm 13 at two equal positions, with the layer-count proof transported along the
equality: the proof depends on the position, so the position cannot be rewritten in place. -/
theorem recoverFromPositionM_pos_congr (c : PublicHash.Cache core) (pk : core.PkSeed)
    {pos pos' : LayerPosition vp} (hpos : pos = pos') (layers : ℕ)
    (h : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    simulateQ c.toPartialImpl (recoverFromPositionM vp core pk pos layers h msg sigs) =
      simulateQ c.toPartialImpl
        (recoverFromPositionM vp core pk pos' layers (hpos ▸ h) msg sigs) := by
  subst hpos; rfl

/-- From a settled Algorithm 13 run started at the layer-`n` position with `layers` layers left,
every layer `j ≥ n` has a settled forger message (`forgerMessage?`) and a settled XMSS recovery on
the forgery's layer-`j` signature at the layer-`j` position, whose value is the run's result at
the final layer. -/
theorem forgerLayers_of_recoverFromPositionM (c : PublicHash.Cache core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (full : Signature vp core) (forsPk : core.Y) :
    ∀ (layers n : ℕ) (hnl : n + layers = vp.params.d) (hl : 0 < layers) (msg : core.Y)
      (sigs : Vector (XmssSig vp.params core) layers) {root : core.Y},
      forgerMessage? c pk parts full forsPk n (by omega) = some msg →
      (∀ k (hk : k < layers), sigs[k] = full[n + k]'(by omega)) →
      simulateQ c.toPartialImpl (recoverFromPositionM vp core pk
        (LayerPosition.atLayer vp parts ⟨n, by omega⟩) layers (by simp; omega) msg sigs) =
          some root →
      ∀ j : Fin vp.params.d, n ≤ j.val → ∃ m r,
        forgerMessage? c pk parts full forsPk j.val j.isLt = some m ∧
        xmssPkFromSig? core c (LayerPosition.atLayer vp parts j).leaf.val full[j] m pk
          (LayerPosition.atLayer vp parts j).toAdrs = some r ∧
        (j.val + 1 = vp.params.d → r = root)
  | 0, _, _, hl, _, _, _, _, _, _, _, _ => absurd hl (Nat.lt_irrefl 0)
  | 1, n, hnl, _, msg, sigs, root, hmsg, hsigs, hrec, j, hj => by
    rw [simulateQ_toPartialImpl_recoverFromPositionM_one_eq_some_iff] at hrec
    obtain ⟨jv, hjlt⟩ := j
    obtain rfl : jv = n := by simp at hj; omega
    refine ⟨msg, root, hmsg, ?_, fun _ => rfl⟩
    have h0 := hsigs 0 Nat.zero_lt_one
    simp only [Nat.add_zero] at h0
    rw [Fin.getElem_fin, ← h0]
    exact hrec
  | k + 2, n, hnl, _, msg, sigs, root, hmsg, hsigs, hrec, j, hj => by
    obtain ⟨r, hx, hrest⟩ :=
      (simulateQ_toPartialImpl_recoverFromPositionM_add_two_eq_some_iff core c pk _ k _ msg
        sigs).mp hrec
    have h0 := hsigs 0 (Nat.zero_lt_succ _)
    simp only [Nat.add_zero] at h0
    rcases Nat.eq_or_lt_of_le hj with hjn | hjn
    · obtain ⟨jv, hjlt⟩ := j
      simp only at hjn
      subst hjn
      refine ⟨msg, r, hmsg, ?_, fun h => by simp only at h; omega⟩
      rw [Fin.getElem_fin, ← h0]
      exact hx
    have hmsg' : forgerMessage? c pk parts full forsPk (n + 1) (by omega) = some r := by
      change (forgerMessage? c pk parts full forsPk n _).bind _ = some r
      rw [hmsg, Option.bind_some, ← h0]
      exact hx
    have hsigs' : ∀ k' (hk' : k' < k + 1), sigs.tail[k'] = full[n + 1 + k']'(by omega) :=
      fun k' hk' => by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hsigs (k' + 1) (by omega)
    have hrest' : simulateQ c.toPartialImpl (recoverFromPositionM vp core pk
        (LayerPosition.atLayer vp parts ⟨n + 1, by omega⟩) (k + 1) (by simp; omega) r
          sigs.tail) = some root := by
      have hnext := LayerPosition.atLayer_succ_eq_next vp parts ⟨n, by omega⟩ (by simp; omega)
      simp only at hnext
      rw [recoverFromPositionM_pos_congr c pk hnext]
      exact hrest
    exact forgerLayers_of_recoverFromPositionM c pk parts full forsPk (k + 1) (n + 1) (by omega)
      (Nat.succ_pos k) r sigs.tail hmsg' hsigs' hrest' j hjn

/-! ## The FORS stop -/

/-- An index of the forger's digest that no logged digest selects names a FORS coordinate no
logged signature opened. -/
theorem unopenedCoord_of_notMem (o : RomOutcome vp core) (c : PublicHash.Cache core)
    {digest : Bytes vp.params.m} {idx : HmsgIndex vp.params}
    (hmem : idx ∈ hmsgIndices vp.params digest)
    (huncov : ¬ ∃ e ∈ o.log, ∃ digest', LoggedDigest o c e digest' ∧
      idx ∈ hmsgIndices vp.params digest') :
    UnopenedCoord o c (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList idx.tree.val) := by
  rintro e he digest' hd i ⟨hadrs, hleaf⟩
  refine huncov ⟨e, he, digest', hd, ?_⟩
  set parts' := splitDigest vp.params digest'
  have hjmem : (⟨parts'.idxTree, parts'.idxLeaf, i, ⟨forsIdx vp.params parts'.md.toList i.val,
      forsIdx_lt vp.params parts'.md.toList i.val⟩⟩ : HmsgIndex vp.params) ∈
      hmsgIndices vp.params digest' := by
    rw [mem_hmsgIndices]
    exact ⟨rfl, rfl, rfl⟩
  have hjadrs := HmsgIndex.forsAdrs_of_mem hjmem
  have hjleaf := HmsgIndex.globalLeaf_of_mem hjmem
  rw [hadrs, ← HmsgIndex.forsAdrs_of_mem hmem] at hjadrs
  rw [hleaf, ← HmsgIndex.globalLeaf_of_mem hmem] at hjleaf
  rwa [HmsgIndex.ext_of_coords hjadrs hjleaf] at hjmem

/-- The FORS stop.  At the FORS instance the forger's digest names, if the forger's recovered FORS
public key is settled at the settled honest one, then either a same-address target collision (on
the `T_k` compression of the roots, on an `H` node of an opened root path, or on an `F` leaf), or
every FORS coordinate the digest selects is covered by a logged digest, or an uncovered coordinate
at which the forgery carries the honest secret. -/
theorem fors_cases (o : RomOutcome vp core) (c : PublicHash.Cache core) (digest : Bytes vp.params.m)
    (hd : ForgerDigest o c digest) (forsPk : core.Y)
    (hforge : forsPkFromSig? core c o.sig.fors (splitDigest vp.params digest).md.toList
      o.pk.pkSeed (splitDigest vp.params digest).forsAdrs = some forsPk)
    (hhonest : forsPkGen? core c o.sk.skSeed o.pk.pkSeed (splitDigest vp.params digest).forsAdrs =
      some forsPk) :
    TargetCollision o c ∨ HiddenHit o c ∨ ItsrCovered o c := by
  set md := (splitDigest vp.params digest).md.toList
  set adrs := (splitDigest vp.params digest).forsAdrs
  rw [forsPkFromSig?, simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff] at hforge
  rw [forsPkGen?, simulateQ_toPartialImpl_forsPkGenM_eq_some_iff] at hhonest
  obtain ⟨roots', hper', hTk'⟩ := hforge
  obtain ⟨roots, hper, hTk⟩ := hhonest
  by_cases hroots : roots = roots'
  swap
  · exact Or.inl ⟨o.pk.pkSeed, core.adrsToKey (forsPkAdrs adrs), roots.toList, roots'.toList,
      forsPk, HonestEntry.forsRoots adrs roots hper, mt Vector.toList_inj.mp hroots, hTk, hTk'⟩
  subst hroots
  suffices hsk : TargetCollision o c ∨ ∀ i : Fin vp.params.k,
      (o.sig.fors[i.val]).sk =
        forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs (forsSigLeafIndex vp.params md i.val) by
    refine hsk.imp id fun hsk => ?_
    by_cases hcov : ∀ idx ∈ hmsgIndices vp.params digest, ∃ e ∈ o.log, ∃ digest',
        LoggedDigest o c e digest' ∧ idx ∈ hmsgIndices vp.params digest'
    · exact Or.inr ⟨digest, hd, hcov⟩
    · push Not at hcov
      obtain ⟨idx, hmem, huncov⟩ := hcov
      exact Or.inl (Or.inr ⟨digest, idx.tree, hd, unopenedCoord_of_notMem o c hmem
        fun ⟨e, he, digest', hd', hmem'⟩ => huncov e he digest' hd' hmem', hsk idx.tree⟩)
  refine or_iff_not_imp_left.mpr fun hcoll i => ?_
  by_contra hi
  refine hcoll ?_
  obtain ⟨leaf', hF', hclimb⟩ := hper' i
  rcases PerfectMerkleTree.climbM_merkleRootM_cases c.toPartialImpl _ _
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) vp.params.a i.val
      (by rw [← forsSigLeafIndex_eq]; exact forsSigLeafIndex_div_pow_a vp.params md i.val) leaf'
      (o.sig.fors[i.val]).auth.toList (by simp) hclimb (hper i) with
    hleaf | ⟨h, l, rr, l', r', v, hh, -, hne, hl, hr, hq, hq'⟩
  · simp only [forsLeafWith, simulateQ_toPartialImpl_f] at hleaf
    refine ⟨o.pk.pkSeed, core.adrsToKey (forsNodeAdrs adrs 0
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)), _, [(o.sig.fors[i.val]).sk], leaf',
      HonestEntry.forsLeaf adrs _, fun h => hi ?_, hleaf, hF'⟩
    simp only [List.cons.injEq, and_true] at h
    rw [forsSigLeafIndex_eq]
    exact h.symm
  · simp only [forsNodeHashWith, simulateQ_toPartialImpl_h] at hq hq'
    refine ⟨o.pk.pkSeed, core.adrsToKey (forsNodeAdrs adrs h _), [l, rr], [l', r'], v,
      HonestEntry.forsNode adrs h _ l rr hh hl hr, fun hlist => hne ?_, hq, hq'⟩
    simp only [List.cons.injEq, and_true] at hlist
    exact Prod.ext hlist.1 hlist.2

end SLHDSA.Security
