/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CacheSecret
public import HashSig.SLHDSA.Security.HmsgWitnesses
public import HashSig.SLHDSA.Security.TraceTargets
public import HashSig.SLHDSA.WotsInjectivity
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Collision
import HashSig.SLHDSA.Security.ComponentTraces

/-!
# The random-oracle bad events at a secret provider, and the descent from the cached root

The random-oracle bad events of a forgery, and the case analyses of the descent from the cached
root, for key holders whose WOTS+ and FORS secrets come from a provider `secret : Adrs →
OracleComp (publicHashSpec core) core.Y`, read off the cache through the readers of
`HashSig.SLHDSA.Security.CacheSecret`.
At the oracle-backed provider `oracleSecret core e pkSeed skSeed` of
`HashSig.SLHDSA.Security.Target`, every secret the key holder uses is itself a cache entry, the
answer of the `F` query of the secret seed at the secret's `PRF` address, so a *settled* secret is
one some party has queried.  The digest events read the internal messages of FIPS 205
Algorithms 19 and 20, with no context wrapper, so they apply to the outcomes of the oracle-backed
run of `HashSig.SLHDSA.Security.RomSchemeRun`, which signs and verifies internal messages.

**Same-address target collision** (`TargetCollision`).  Two cache entries at one tweakable-hash
key with equal answers and different inputs, one of them an honest entry (`HonestEntry`).  Every
honest entry sits at an address of the union ledger `constructionAddresses` of
`HashSig.SLHDSA.Security.TraceTargets`, so in particular a WOTS+ chain entry is at a hash address
below `w - 1`.  The two secret-consuming constructors, a WOTS+ chain entry and a FORS leaf, carry
the settled secret they start from as a premise, so an honest entry never rests on a secret the
cache does not record.  The honest relation reads only the provider, the public seed and the
cache.

**Hidden-value hit** (`HiddenHit`).  The forgery's WOTS+ signature entry on some chain of the leaf
the verification replay enters is the honest chain value at the step its message selects, that
step is one the honest message at that leaf does not reveal, and it is below the top step `w - 1`;
or the forgery carries, at a FORS coordinate no logged signature opened, the settled secret there.

**Interleaved-target coverage** (`ItsrCovered`).  Every FORS coordinate the forgery's digest
selects is selected by the digest of some logged signature.

The case analyses `xmssPkFromSig?_cases`, `wotsChain_cases`, `wotsLeaf_cases`, `xmssLayer_cases`
and `fors_cases` split a settled verification step into these events or the next step of the
descent.  The first three take the ledger membership of the addresses they may name as
hypotheses; `xmssLayer_cases` and `fors_cases` discharge the ledger memberships from the hypertree
position and the digest-derived FORS instance through the membership lemmas of
`HashSig.SLHDSA.Security.ComponentTraces`.  In `xmssLayer_cases` the hidden-value hit at a used
leaf with a different honest message is on a chain where the forgery's message selects a smaller
step (`chainStepsCore_two_encodings`), and at an unused leaf it is on a chain where that message
selects a step below the top (`exists_chainStepsCore_lt_pred_w`).  The positional facts draw no
secret: `childTreeAdrs` and `forsInstanceAdrs` name the tree and FORS instance a hypertree position
signs, `forgerMessage?` is the message the verification replay presents to each layer, and
`forgerLayers_of_recoverFromPositionM` reads every layer of a settled Algorithm 13 run off the
cache.  The root of the child tree and the roots compression of the FORS instance are
union-ledger targets (`xmssNodeAdrs_childTreeAdrs_mem_constructionAddresses`,
`forsPkAdrs_forsInstanceAdrs_mem_constructionAddresses`), so at every position so is the address
`msgAdrs pos` whose value is the honest message signed there
(`msgAdrs_mem_constructionAddresses`).

## Scope

* Everything here is deterministic: no probability is bounded and no query budget appears.
* The composition of these case analyses into a statement about a run of an experiment is not in
  this module.
* A settled secret is settled by whichever party queried it first.  A forger query that names
  the secret seed settles the secret itself, and `HiddenHit` can then fire on it, so a bound on
  `HiddenHit` must charge the queries that name the secret seed.  The cache records no
  provenance, so that charge is read off the forger's query log, not off the cache.
* `ItsrCovered` does not exclude the forger's point being a logged message and randomizer;
  freshness of the forged message for the signing log, as EUF-CMA requires, excludes it.
* Nothing here is quantum.

## Labels

Thirty declarations, none private.

*Positions and the verifier's replay*: `childTreeAdrs`, `childTreeAdrs_next`, `forsInstanceAdrs`,
`forsInstanceAdrs_initial`, `forsPkAdrs_forsInstanceAdrs_mem_constructionAddresses`,
`xmssNodeAdrs_childTreeAdrs_mem_constructionAddresses`, `forgerMessage?`, `forgerMessage?_mono`,
`recoverFromPositionM_pos_congr`, `forgerLayers_of_recoverFromPositionM`.

*Honest entries and the target collision*: `HonestEntry`, `TargetCollision`.

*Digests, used leaves and honest messages*: `LoggedDigest`, `ForgerDigest`, `UsedLeaf`,
`honestMessage?`, `msgAdrs`, `msgAdrs_mem_constructionAddresses`, `HiddenChainValue`,
`UnopenedCoord`.

*The forger's replay*: `ForgerLayer`, `HiddenHit`, `ItsrCovered`.

*XMSS stop, WOTS+ chains and one XMSS layer*: `xmssPkFromSig?_cases`, `wotsChain_cases`,
`wotsLeaf_cases`, `xmssLayer_cases`.

*Position congruence*: `signFromPositionWithSecret_pos_congr`.

*The FORS stop*: `unopenedCoord_of_notMem`, `fors_cases`.

## References

- NIST FIPS 205, §6--§9, Algorithms 9--20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec GeneralHypertree SignatureAlg CanonicalGames

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## Positions and the verifier's replay

These read nothing a key holder computes: the child tree and FORS instance a hypertree position
signs, and the message the verification replay presents to each layer. -/

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

/-- The FORS roots compression of the instance a layer-zero position signs is a union-ledger
target. -/
theorem forsPkAdrs_forsInstanceAdrs_mem_constructionAddresses (pos : LayerPosition vp)
    (h0 : pos.layer.val = 0) :
    forsPkAdrs (forsInstanceAdrs pos) ∈ constructionAddresses vp :=
  forsRootAdrs_mem_constructionAddresses
    (⟨⟨pos.tree.val, by simpa [h0] using pos.tree.isLt⟩, pos.leaf⟩ : BottomPosition vp)

/-- The root of the child tree a position above layer zero signs is a union-ledger target. -/
theorem xmssNodeAdrs_childTreeAdrs_mem_constructionAddresses (pos : LayerPosition vp)
    (h0 : 0 < pos.layer.val) :
    xmssNodeAdrs (childTreeAdrs pos) vp.params.hp 0 ∈ constructionAddresses vp := by
  have hh : layerTreeHeight vp (pos.layer.val - 1) =
      layerTreeHeight vp pos.layer.val + vp.params.hp := by
    have := pos.layer.isLt
    rw [layerTreeHeight, layerTreeHeight, show vp.params.d - (pos.layer.val - 1 + 1) =
      vp.params.d - (pos.layer.val + 1) + 1 by omega, Nat.add_mul, one_mul]
  have hlt : pos.tree.val * 2 ^ vp.params.hp + pos.leaf.val <
      2 ^ layerTreeHeight vp (pos.layer.val - 1) := by
    rw [hh, pow_add]
    calc _ < (pos.tree.val + 1) * 2 ^ vp.params.hp := by have := pos.leaf.isLt; linarith
      _ ≤ _ := Nat.mul_le_mul_right _ pos.tree.isLt
  exact xmssNodeAdrs_mem_constructionAddresses
    (⟨⟨pos.layer.val - 1, by omega⟩, ⟨_, hlt⟩⟩ : LayerTreeCoord vp) vp.valid.hp_pos le_rfl
    (by simp)

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

/-- The message the verification replay presents to a layer only grows with the cache. -/
theorem forgerMessage?_mono {c c' : PublicHash.Cache core} (hle : c ≤ c') (pk : core.PkSeed)
    (parts : DigestParts vp.params) (sig : GeneralHypertree.Signature vp core) (forsPk : core.Y) :
    ∀ (j : ℕ) (hj : j < vp.params.d) {m : core.Y},
      forgerMessage? c pk parts sig forsPk j hj = some m →
        forgerMessage? c' pk parts sig forsPk j hj = some m
  | 0, _, _, h => h
  | j + 1, hj, m, h => by
    obtain ⟨m', hm', hx⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2 ⟨m', forgerMessage?_mono hle pk parts sig forsPk j _ hm',
      QueryCache.simulateQ_toPartialImpl_mono hle _ hx⟩

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

/-! ## Honest entries and the target collision -/

/-- A `thash` query whose input is a value the key holder computes from the provider `secret` at
public seed `pk`, read off the cache.  Each constructor names the honest values that must be
settled for the input to be the honest one; the two that consume a secret, `wotsChain` and
`forsLeaf`, name the settled secret.

Each constructor also requires its entry address, the address whose key the query is at, to be in
the union ledger `constructionAddresses vp`.  That ranges every entry over the addresses an honest
run of the construction hashes at: an XMSS node at height `1 ≤ h ≤ hp` and index
`i < 2 ^ (hp - h)` of a reachable tree; the public-key compression of a reachable WOTS+ instance; a
WOTS+ hash step at hash address `t < w - 1` on chain `i < len` of a reachable instance; a FORS leaf
of a reachable instance at global index `t < k * 2 ^ a`; a FORS node at height `1 ≤ h ≤ a` and
index `i < k * 2 ^ (a - h)`; the root compression of a reachable FORS instance.  The range is on
addresses: where the key encoding `core.adrsToKey` is not injective on these addresses, one key
can still carry several honest inputs.  In `forsNode`, `hh : 0 < h` keeps a two-input node off the
key of a FORS leaf, since the height-0 addresses of a FORS tree are ledger addresses (its leaves);
in `xmssNode` the bound `0 < h` already follows from `hmem`. -/
inductive HonestEntry (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (pk : core.PkSeed) (c : PublicHash.Cache core) : (publicHashSpec core).Domain → Prop
  | xmssNode (adrs : Adrs) (h i : ℕ) (l r : core.Y) (hh : 0 < h)
      (hmem : xmssNodeAdrs adrs h i ∈ constructionAddresses vp)
      (hl : xmssNodeWithSecret? core c secret pk adrs (h - 1) (2 * i) = some l)
      (hr : xmssNodeWithSecret? core c secret pk adrs (h - 1) (2 * i + 1) = some r) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (xmssNodeAdrs adrs h i)) [l, r])
  | wotsPk (adrs : Adrs) (tops : Vector core.Y vp.params.len)
      (hmem : wotsPkAdrs adrs ∈ constructionAddresses vp)
      (h : wotsPkGenTopsWithSecret? core c secret pk adrs = some tops) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (wotsPkAdrs adrs)) tops.toList)
  | wotsChain (adrs : Adrs) (i t : ℕ) (x v : core.Y)
      (hmem : (wotsChainAdrs adrs i).setHashAddress t ∈ constructionAddresses vp)
      (hx : simulateQ c.toPartialImpl (secret (wotsSkAdrs adrs i)) = some x)
      (h : chain? core c pk (wotsChainAdrs adrs i) x 0 t = some v) :
      HonestEntry secret pk c
        (.thash pk (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress t)) [v])
  | forsLeaf (adrs : Adrs) (t : ℕ) (x : core.Y)
      (hmem : forsNodeAdrs adrs 0 t ∈ constructionAddresses vp)
      (hx : simulateQ c.toPartialImpl (secret (forsSkAdrs adrs t)) = some x) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (forsNodeAdrs adrs 0 t)) [x])
  | forsNode (adrs : Adrs) (h i : ℕ) (l r : core.Y) (hh : 0 < h)
      (hmem : forsNodeAdrs adrs h i ∈ constructionAddresses vp)
      (hl : forsNodeWithSecret? core c secret pk adrs (h - 1) (2 * i) = some l)
      (hr : forsNodeWithSecret? core c secret pk adrs (h - 1) (2 * i + 1) = some r) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (forsNodeAdrs adrs h i)) [l, r])
  | forsRoots (adrs : Adrs) (roots : Vector core.Y vp.params.k)
      (hmem : forsPkAdrs adrs ∈ constructionAddresses vp)
      (h : ∀ i : Fin vp.params.k,
        forsNodeWithSecret? core c secret pk adrs vp.params.a i.val = some roots[i]) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (forsPkAdrs adrs)) roots.toList)

/-- Two cache entries at one `thash` key with equal answers and different inputs, one of which is
an honest entry for the provider `secret` at public seed `pk`. -/
@[expose] def TargetCollision (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (pk : core.PkSeed) (c : PublicHash.Cache core) : Prop :=
  ∃ (key : core.AdrsKey) (xs ys : List core.Y) (v : core.Y),
    HonestEntry secret pk c (.thash pk key xs) ∧ xs ≠ ys ∧
    c (.thash pk key xs) = some v ∧ c (.thash pk key ys) = some v

/-! ## Digests, used leaves and honest messages -/

/-- The `H_msg` digest of a logged signature on an internal message, read off the cache. -/
@[expose] def LoggedDigest (o : RomOutcome vp core) (c : PublicHash.Cache core)
    (e : (t : (List Byte →ₒ GeneralScheme.SignatureCore vp core).Domain) ×
      (List Byte →ₒ GeneralScheme.SignatureCore vp core).Range t)
    (digest : Bytes vp.params.m) : Prop :=
  c (.hmsg e.2.randomness o.pk.pkSeed o.pk.pkRoot e.1) = some digest

/-- The `H_msg` digest of the forgery on its internal message, read off the cache. -/
@[expose] def ForgerDigest (o : RomOutcome vp core) (c : PublicHash.Cache core)
    (digest : Bytes vp.params.m) : Prop :=
  c (.hmsg o.sig.randomness o.pk.pkSeed o.pk.pkRoot o.msg) = some digest

/-- Some logged signature's hypertree position at layer `j` is `pos`. -/
@[expose] def UsedLeaf (o : RomOutcome vp core) (c : PublicHash.Cache core) (j : Fin vp.params.d)
    (pos : LayerPosition vp) : Prop :=
  ∃ e ∈ o.log, ∃ digest, LoggedDigest o c e digest ∧
    LayerPosition.atLayer vp (splitDigest vp.params digest) j = pos

/-- The honest message signed at `pos` for the provider `secret`, read off the cache: the honest
FORS public key of the instance at layer `0`, the honest root of the child tree above. -/
@[expose] def honestMessage? (c : PublicHash.Cache core)
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (pk : core.PkSeed)
    (pos : LayerPosition vp) : Option core.Y :=
  if pos.layer.val = 0 then forsPkGenWithSecret? core c secret pk (forsInstanceAdrs pos)
  else xmssRootWithSecret? core c secret pk (childTreeAdrs pos)

/-- The address of the tweakable hash whose value is the honest message signed at `pos`: the
FORS roots compression of the instance at layer `0`, the root of the child tree above. -/
@[expose] def msgAdrs (pos : LayerPosition vp) : Adrs :=
  if pos.layer.val = 0 then forsPkAdrs (forsInstanceAdrs pos)
  else xmssNodeAdrs (childTreeAdrs pos) vp.params.hp 0

/-- The address of the honest message at every position is a union-ledger target. -/
theorem msgAdrs_mem_constructionAddresses (pos : LayerPosition vp) :
    msgAdrs pos ∈ constructionAddresses vp := by
  unfold msgAdrs
  split_ifs with h0
  · exact forsPkAdrs_forsInstanceAdrs_mem_constructionAddresses pos h0
  · exact xmssNodeAdrs_childTreeAdrs_mem_constructionAddresses pos (Nat.pos_of_ne_zero h0)

/-- The chain value at step `t` of chain `i` of the WOTS+ leaf at `pos` is hidden: the leaf is
unused, or it is used and `t` is below the step its honest message selects on chain `i`. -/
@[expose]
def HiddenChainValue (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (o : RomOutcome vp core) (c : PublicHash.Cache core) (j : Fin vp.params.d)
    (pos : LayerPosition vp) (i t : ℕ) : Prop :=
  UsedLeaf o c j pos →
    ∃ m, honestMessage? c secret o.pk.pkSeed pos = some m ∧ t < chainStepsCore core m i

/-- No logged signature opened the FORS coordinate (instance `adrs`, global leaf `t`). -/
@[expose]
def UnopenedCoord (o : RomOutcome vp core) (c : PublicHash.Cache core) (adrs : Adrs) (t : ℕ) :
    Prop :=
  ∀ e ∈ o.log, ∀ digest, LoggedDigest o c e digest → ∀ i : Fin vp.params.k,
    ¬ ((splitDigest vp.params digest).forsAdrs = adrs ∧
      forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val = t)

/-! ## The forger's replay -/

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

/-- The forgery's replay under the cache produces a hidden honest value for the provider
`secret`.  Either the forgery's WOTS+ signature entry on chain `i` of the leaf the replay enters at
layer `j` with message `m` is the honest chain value from the settled secret `x` at the step
`t = chainStepsCore core m i` that `m` selects, that step is hidden, and it is below the top step,
`t < w - 1`; or, at a FORS coordinate no logged signature opened, the forgery carries the settled
secret there. -/
@[expose] def HiddenHit (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (o : RomOutcome vp core) (c : PublicHash.Cache core) : Prop :=
  (∃ (j : Fin vp.params.d) (pos : LayerPosition vp) (m : core.Y) (i : Fin vp.params.len)
      (x : core.Y),
    ForgerLayer o c j pos m ∧
    HiddenChainValue secret o c j pos i.val (chainStepsCore core m i.val) ∧
    chainStepsCore core m i.val < vp.params.w - 1 ∧
    simulateQ c.toPartialImpl
      (secret (wotsSkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)) = some x ∧
    chain? core c o.pk.pkSeed (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val) x 0
      (chainStepsCore core m i.val) = some (o.sig.hypertree[j]).wots[i]) ∨
  (∃ (digest : Bytes vp.params.m) (i : Fin vp.params.k),
    ForgerDigest o c digest ∧
    UnopenedCoord o c (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val) ∧
    simulateQ c.toPartialImpl (secret (forsSkAdrs (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val))) =
        some (o.sig.fors[i]).sk)

/-- Every FORS coordinate the forgery's `H_msg` digest selects is selected by the digest of some
logged signature, all digests read off the cache. -/
@[expose] def ItsrCovered (o : RomOutcome vp core) (c : PublicHash.Cache core) : Prop :=
  ∃ digest, ForgerDigest o c digest ∧
    ∀ idx ∈ hmsgIndices vp.params digest, ∃ e ∈ o.log, ∃ digest',
      LoggedDigest o c e digest' ∧ idx ∈ hmsgIndices vp.params digest'

/-! ## XMSS stop, WOTS+ chains and one XMSS layer -/

section Descent

variable (secret : Adrs → OracleComp (publicHashSpec core) core.Y)

/-- An XMSS signature at leaf `idx` whose recovered root is settled at the settled honest root of
the same tree yields either a same-address target collision, or settled forger chain tops equal
to the settled honest chain tops at that leaf.  The hypotheses `hnode` and `hpk` place the tree's
internal nodes and the leaf's public-key compression in the union ledger. -/
theorem xmssPkFromSig?_cases (pk : core.PkSeed) (c : PublicHash.Cache core) (adrs : Adrs)
    (idx : ℕ) (hidx : idx < 2 ^ vp.params.hp)
    (hnode : ∀ h i, 0 < h → h ≤ vp.params.hp → i < 2 ^ (vp.params.hp - h) →
      xmssNodeAdrs adrs h i ∈ constructionAddresses vp)
    (hpk : wotsPkAdrs (wotsLeafAdrs adrs idx) ∈ constructionAddresses vp)
    (sig : XmssSig vp.params core) (msg : core.Y)
    {r : core.Y} (hforge : xmssPkFromSig? core c idx sig msg pk adrs = some r)
    (hhonest : xmssRootWithSecret? core c secret pk adrs = some r) :
    TargetCollision secret pk c ∨
    ∃ tops : Vector core.Y vp.params.len,
      simulateQ c.toPartialImpl
        (wotsPkFromSigTopsM core sig.wots msg pk (wotsLeafAdrs adrs idx)) = some tops ∧
      wotsPkGenTopsWithSecret? core c secret pk (wotsLeafAdrs adrs idx) = some tops := by
  obtain ⟨leaf', ⟨tops', htops', hTl'⟩, hclimb⟩ :=
    (simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff core c idx sig msg pk adrs).mp hforge
  rcases PerfectMerkleTree.climbM_merkleRootM_cases c.toPartialImpl _ _ idx vp.params.hp 0
      (Nat.div_eq_of_lt hidx) leaf' sig.auth.toList (by simp) hclimb hhonest with
    hleaf | ⟨h, l, rr, l', r', v, hh, hhp, hne, hl, hr, hq, hq'⟩
  · simp only [xmssLeafWithSecret, wotsPkGenWithSecret, simulateQ_bind_eq_some_iff,
      simulateQ_toPartialImpl_tl] at hleaf
    obtain ⟨tops, htops, hTl⟩ := hleaf
    by_cases heq : tops = tops'
    · subst heq
      exact Or.inr ⟨tops, htops', htops⟩
    · exact Or.inl ⟨core.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs idx)), tops.toList,
        tops'.toList, leaf', HonestEntry.wotsPk _ tops hpk htops, mt Vector.toList_inj.mp heq,
        hTl, hTl'⟩
  · simp only [xmssNodeHashM, xmssNodeHashWith, simulateQ_toPartialImpl_h] at hq hq'
    have hi : idx / 2 ^ h < 2 ^ (vp.params.hp - h) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hhp]
      exact hidx
    refine Or.inl ⟨core.adrsToKey (xmssNodeAdrs adrs h (idx / 2 ^ h)), [l, rr], [l', r'], v,
      HonestEntry.xmssNode adrs h (idx / 2 ^ h) l rr hh (hnode h _ hh hhp hi) hl hr,
      fun hlist => hne ?_, hq, hq'⟩
    simp only [List.cons.injEq, and_true] at hlist
    exact Prod.ext hlist.1 hlist.2

/-- A settled forger chain from `x` at step `a` that reaches the settled honest chain top of
chain `i`, whose settled secret is `x₀`, either collides with the honest chain (a same-address `F`
target collision, both entries cached) or starts at the honest chain value at step `a`.  The
hypothesis `hmem` places the chain's hash steps below `w - 1` in the union ledger. -/
theorem wotsChain_cases (pk : core.PkSeed) (c : PublicHash.Cache core) (adrs : Adrs) (i a : ℕ)
    (hmem : ∀ s, s < vp.params.w - 1 →
      (wotsChainAdrs adrs i).setHashAddress s ∈ constructionAddresses vp)
    (ha : a ≤ vp.params.w - 1) (x x₀ top : core.Y)
    (hx₀ : simulateQ c.toPartialImpl (secret (wotsSkAdrs adrs i)) = some x₀)
    (hforge : chain? core c pk (wotsChainAdrs adrs i) x a (vp.params.w - 1 - a) = some top)
    (hhonest : chain? core c pk (wotsChainAdrs adrs i) x₀ 0 (vp.params.w - 1) = some top) :
    TargetCollision secret pk c ∨ chain? core c pk (wotsChainAdrs adrs i) x₀ 0 a = some x := by
  obtain ⟨b, hb⟩ : ∃ b, vp.params.w - 1 = a + b := ⟨vp.params.w - 1 - a, by omega⟩
  rw [show vp.params.w - 1 - a = b by omega] at hforge
  rw [hb, chain?_add_eq_some_iff, Nat.zero_add] at hhonest
  obtain ⟨va, hva, hsuffix⟩ := hhonest
  rcases chain?_diverge core c pk _ x va a b hforge hsuffix with
    h | ⟨j, hj, u', v', w', hne, hu', hv', hqu, hqv⟩
  · exact Or.inr (h ▸ hva)
  · refine Or.inl ⟨core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress (a + j)), [v'], [u'],
      w', HonestEntry.wotsChain adrs i (a + j) x₀ v' (hmem _ (by omega)) hx₀ ?_,
      fun h => hne ?_, hqv, hqu⟩
    · rw [chain?_add_eq_some_iff]
      exact ⟨va, hva, by rwa [Nat.zero_add]⟩
    · simp only [List.cons.injEq, and_true] at h
      exact h.symm

/-- Forger chain tops settled at the settled honest chain tops yield either a same-address
target collision, or, on every chain, the secret is settled and the forger's WOTS+ signature entry
is the honest chain value at the step its message selects.  The hypothesis `hmem` places every
chain's hash steps below `w - 1` in the union ledger. -/
theorem wotsLeaf_cases (pk : core.PkSeed) (c : PublicHash.Cache core) (adrs : Adrs)
    (hmem : ∀ i, i < vp.params.len → ∀ s, s < vp.params.w - 1 →
      (wotsChainAdrs adrs i).setHashAddress s ∈ constructionAddresses vp)
    (sig : WotsSig vp.params core) (m' : core.Y) (tops : Vector core.Y vp.params.len)
    (hforge : simulateQ c.toPartialImpl (wotsPkFromSigTopsM core sig m' pk adrs) = some tops)
    (hhonest : wotsPkGenTopsWithSecret? core c secret pk adrs = some tops) :
    TargetCollision secret pk c ∨
      ∀ i : Fin vp.params.len, ∃ x₀,
        simulateQ c.toPartialImpl (secret (wotsSkAdrs adrs i.val)) = some x₀ ∧
        chain? core c pk (wotsChainAdrs adrs i.val) x₀ 0 (chainStepsCore core m' i.val) =
          some sig[i] := by
  rw [simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff] at hforge
  rw [wotsPkGenTopsWithSecret?_eq_some_iff] at hhonest
  refine or_iff_not_imp_left.mpr fun hcoll i => ?_
  obtain ⟨x₀, hx₀, hchain⟩ := hhonest i
  exact ⟨x₀, hx₀, (wotsChain_cases secret pk c adrs i.val _ (hmem i.val i.isLt)
    (chainStepsCore_le core m' i.val) sig[i.val] x₀ tops[i] hx₀ (hforge i) hchain).resolve_left
    hcoll⟩

/-- One XMSS layer of the descent.  At a position the forger's replay enters at layer `j` with
message `m'`, if the forger's XMSS recovery is settled at the settled honest root there, then
either a same-address target collision, or a hidden-value hit, or the leaf is used and `m'` is its
honest message.  The hypothesis `hmsg` supplies the settled honest message of a used leaf. -/
theorem xmssLayer_cases (laws : core.ByteLaws) (o : RomOutcome vp core)
    (c : PublicHash.Cache core) (j : Fin vp.params.d) (pos : LayerPosition vp) (m' : core.Y)
    {r : core.Y} (hlayer : ForgerLayer o c j pos m')
    (hforge : xmssPkFromSig? core c pos.leaf.val (o.sig.hypertree[j]) m' o.pk.pkSeed pos.toAdrs =
      some r)
    (hhonest : xmssRootWithSecret? core c secret o.pk.pkSeed pos.toAdrs = some r)
    (hmsg : UsedLeaf o c j pos → ∃ m, honestMessage? c secret o.pk.pkSeed pos = some m) :
    TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨
      (UsedLeaf o c j pos ∧ honestMessage? c secret o.pk.pkSeed pos = some m') := by
  rcases xmssPkFromSig?_cases secret o.pk.pkSeed c pos.toAdrs pos.leaf.val pos.leaf.isLt
      (fun _ _ hh hhp hi => xmssNodeAdrs_mem_constructionAddresses_of_position pos hh hhp hi)
      (wotsPkAdrs_mem_constructionAddresses pos) _ m' hforge hhonest with h | ⟨tops, htops', htops⟩
  · exact Or.inl h
  rcases wotsLeaf_cases secret o.pk.pkSeed c _
      (fun i hi _ hs => wotsChainAdrs_setHashAddress_mem_constructionAddresses pos ⟨i, hi⟩ hs) _
      m' tops htops' htops with h | hall
  · exact Or.inl h
  by_cases hused : UsedLeaf o c j pos
  · obtain ⟨m, hm⟩ := hmsg hused
    by_cases hmm : m = m'
    · exact Or.inr (Or.inr ⟨hused, hmm ▸ hm⟩)
    · obtain ⟨i, hi, hlt⟩ := chainStepsCore_two_encodings (core := core) vp.valid laws (Ne.symm hmm)
      obtain ⟨x₀, hx₀, hchain⟩ := hall ⟨i, hi⟩
      exact Or.inr (Or.inl (Or.inl ⟨j, pos, m', ⟨i, hi⟩, x₀, hlayer, fun _ => ⟨m, hm, hlt⟩,
        lt_of_lt_of_le hlt (chainStepsCore_le core m i), hx₀, hchain⟩))
  · obtain ⟨i, hi, htop⟩ := exists_chainStepsCore_lt_pred_w (core := core) vp.valid m'
    obtain ⟨x₀, hx₀, hchain⟩ := hall ⟨i, hi⟩
    exact Or.inr (Or.inl (Or.inl ⟨j, pos, m', ⟨i, hi⟩, x₀, hlayer, fun h => absurd h hused, htop,
      hx₀, hchain⟩))

/-- Algorithm 12 over a provider at two equal positions, with the layer-count proof transported
along the equality: the proof depends on the position, so the position cannot be rewritten in
place. -/
theorem signFromPositionWithSecret_pos_congr (c : PublicHash.Cache core) (pk : core.PkSeed)
    (recoverFinal : Bool) {pos pos' : LayerPosition vp} (hpos : pos = pos') (layers : ℕ)
    (h : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    simulateQ c.toPartialImpl (signFromPositionWithSecret core (PublicHash.f core pk)
        (PublicHash.tl core pk) (PublicHash.h core pk) secret recoverFinal pos layers h msg) =
      simulateQ c.toPartialImpl (signFromPositionWithSecret core (PublicHash.f core pk)
        (PublicHash.tl core pk) (PublicHash.h core pk) secret recoverFinal pos' layers
        (hpos ▸ h) msg) := by
  subst hpos; rfl

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
every FORS coordinate the digest selects is covered by a logged digest, or at an uncovered
coordinate the forgery carries the settled secret. -/
theorem fors_cases (o : RomOutcome vp core) (c : PublicHash.Cache core)
    (digest : Bytes vp.params.m) (hd : ForgerDigest o c digest) (forsPk : core.Y)
    (hforge : forsPkFromSig? core c o.sig.fors (splitDigest vp.params digest).md.toList
      o.pk.pkSeed (splitDigest vp.params digest).forsAdrs = some forsPk)
    (hhonest : forsPkGenWithSecret? core c secret o.pk.pkSeed
      (splitDigest vp.params digest).forsAdrs = some forsPk) :
    TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨ ItsrCovered o c := by
  have hrootMem :
      forsPkAdrs (splitDigest vp.params digest).forsAdrs ∈ constructionAddresses vp := by
    rw [← BottomPosition.forsAdrs_ofDigestParts]
    exact forsRootAdrs_mem_constructionAddresses _
  have hleafMem : ∀ i : Fin vp.params.k, forsNodeAdrs (splitDigest vp.params digest).forsAdrs 0
      (i.val * 2 ^ vp.params.a + forsIdx vp.params (splitDigest vp.params digest).md.toList i.val)
        ∈ constructionAddresses vp := fun i => by
    rw [← BottomPosition.forsAdrs_ofDigestParts]
    exact forsLeafAdrs_mem_constructionAddresses _ i (forsLeafIndex_div vp.params _ i.val)
  have hnodeMem : ∀ (i : Fin vp.params.k) (h : ℕ), 0 < h → h ≤ vp.params.a →
      forsNodeAdrs (splitDigest vp.params digest).forsAdrs h ((i.val * 2 ^ vp.params.a +
        forsIdx vp.params (splitDigest vp.params digest).md.toList i.val) / 2 ^ h) ∈
          constructionAddresses vp := fun i h hh hha => by
    rw [← BottomPosition.forsAdrs_ofDigestParts]
    refine forsTreeAdrs_mem_constructionAddresses _ i hh hha ?_
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hha]
    exact forsLeafIndex_div vp.params _ i.val
  set md := (splitDigest vp.params digest).md.toList
  set adrs := (splitDigest vp.params digest).forsAdrs
  rw [forsPkFromSig?, simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff] at hforge
  rw [forsPkGenWithSecret?_eq_some_iff] at hhonest
  obtain ⟨roots', hper', hTk'⟩ := hforge
  obtain ⟨roots, hper, hTk⟩ := hhonest
  by_cases hroots : roots = roots'
  swap
  · exact Or.inl ⟨core.adrsToKey (forsPkAdrs adrs), roots.toList, roots'.toList, forsPk,
      HonestEntry.forsRoots adrs roots hrootMem hper, mt Vector.toList_inj.mp hroots, hTk, hTk'⟩
  subst hroots
  suffices hsk : TargetCollision secret o.pk.pkSeed c ∨ ∀ i : Fin vp.params.k,
      simulateQ c.toPartialImpl (secret (forsSkAdrs adrs (forsSigLeafIndex vp.params md i.val))) =
        some (o.sig.fors[i.val]).sk by
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
    hleaf | ⟨h, l, rr, l', r', v, hh, hha, hne, hl, hr, hq, hq'⟩
  · simp only [forsLeafWithSecret, simulateQ_bind_eq_some_iff, simulateQ_toPartialImpl_f]
      at hleaf
    obtain ⟨x, hx, hleaf⟩ := hleaf
    refine ⟨core.adrsToKey (forsNodeAdrs adrs 0
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)), [x], [(o.sig.fors[i.val]).sk],
      leaf', HonestEntry.forsLeaf adrs _ x (hleafMem i) hx, fun h => hi ?_, hleaf, hF'⟩
    simp only [List.cons.injEq, and_true] at h
    rw [forsSigLeafIndex_eq, ← h]
    exact hx
  · simp only [forsNodeHashWith, simulateQ_toPartialImpl_h] at hq hq'
    refine ⟨core.adrsToKey (forsNodeAdrs adrs h _), [l, rr], [l', r'], v,
      HonestEntry.forsNode adrs h _ l rr hh (hnodeMem i h hh hha) hl hr, fun hlist => hne ?_, hq,
      hq'⟩
    simp only [List.cons.injEq, and_true] at hlist
    exact Prod.ext hlist.1 hlist.2

end Descent

end SLHDSA.Security
