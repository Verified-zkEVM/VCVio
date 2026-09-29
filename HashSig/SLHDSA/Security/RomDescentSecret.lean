/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CacheSecret
public import HashSig.SLHDSA.Security.RomDescent

/-!
# The random-oracle bad events at a secret provider, and the descent from the cached root

The events and case analyses of `HashSig.SLHDSA.Security.RomDescent`, restated for key holders
whose WOTS+ and FORS secrets come from a provider `secret : Adrs → OracleComp (publicHashSpec
core) core.Y`, read off the cache through the readers of `HashSig.SLHDSA.Security.CacheSecret`.
At the oracle-backed provider `oracleSecret core e pkSeed skSeed` of
`HashSig.SLHDSA.Security.Target`, every secret the key holder uses is itself a cache entry, the
answer of the `F` query of the secret seed at the secret's `PRF` address, so a *settled* secret is
one some party has queried.  The digest events read the internal messages of FIPS 205
Algorithms 19 and 20, with no context wrapper, so they apply to the outcomes of the oracle-backed
run of `HashSig.SLHDSA.Security.RomSchemeRun`, which signs and verifies internal messages.

**Same-address target collision** (`TargetCollision`).  Two cache entries at one tweakable-hash
key with equal answers and different inputs, one of them an honest entry (`HonestEntry`).  The two
secret-consuming constructors, a WOTS+ chain entry and a FORS leaf, carry the settled secret they
start from as a premise, so an honest entry never rests on a secret the cache does not record.
The honest relation reads only the provider, the public seed and the cache, and is monotone in the
cache (`HonestEntry.mono`).

**Hidden-value hit** (`HiddenHit`).  The forgery's verification replay reaches a WOTS+ chain value
at a step the honest message at that leaf does not reveal, from the forger's own signature entry;
or the forgery carries, at a FORS coordinate no logged signature opened, the settled secret there.

**Interleaved-target coverage** (`ItsrCovered`).  Every FORS coordinate the forgery's digest
selects is selected by the digest of some logged signature.

The case analyses `xmssPkFromSig?_cases`, `wotsChain_cases`, `wotsLeaf_cases`, `xmssLayer_cases`
and `fors_cases` are those of `HashSig.SLHDSA.Security.RomDescent` over the provider.  The
verifier-side facts that draw no secret, `exists_xmssPkFromSigM_top_of_recoverFromPositionM`,
`recoverFromPositionM_pos_congr`, `forgerLayers_of_recoverFromPositionM`, `forgerMessage?`,
`childTreeAdrs` and `forsInstanceAdrs`, are used from that module unchanged.

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

Nineteen declarations, none private.

*Honest entries and the target collision*: `HonestEntry`, `HonestEntry.mono`, `TargetCollision`.

*Digests, used leaves and honest messages*: `LoggedDigest`, `ForgerDigest`, `UsedLeaf`,
`honestMessage?`, `HiddenChainValue`, `UnopenedCoord`.

*The forger's replay*: `ForgerLayer`, `HiddenHit`, `ItsrCovered`.

*XMSS stop, WOTS+ chains and one XMSS layer*: `xmssPkFromSig?_cases`, `wotsChain_cases`,
`wotsLeaf_cases`, `xmssLayer_cases`.

*Position congruence*: `signFromPositionWithSecret_pos_congr`.

*The FORS stop*: `unopenedCoord_of_notMem`, `fors_cases`.

## References

- NIST FIPS 205, §6--§9, Algorithms 9--20
-/

public section

namespace SLHDSA.Security.WithSecret

open OracleComp OracleSpec GeneralHypertree SignatureAlg CanonicalGames

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## Honest entries and the target collision -/

/-- A `thash` query whose input is a value the key holder computes from the provider `secret` at
public seed `pk`, read off the cache.  Each constructor names the honest values that must be
settled for the input to be the honest one; the two that consume a secret, `wotsChain` and
`forsLeaf`, name the settled secret.  Addresses are unconstrained; the height bound keeps the
two-element node entries off the height-`0` keys. -/
inductive HonestEntry (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (pk : core.PkSeed) (c : PublicHash.Cache core) : (publicHashSpec core).Domain → Prop
  | xmssNode (adrs : Adrs) (h i : ℕ) (l r : core.Y) (hh : 0 < h)
      (hl : xmssNodeWithSecret? core c secret pk adrs (h - 1) (2 * i) = some l)
      (hr : xmssNodeWithSecret? core c secret pk adrs (h - 1) (2 * i + 1) = some r) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (xmssNodeAdrs adrs h i)) [l, r])
  | wotsPk (adrs : Adrs) (tops : Vector core.Y vp.params.len)
      (h : wotsPkGenTopsWithSecret? core c secret pk adrs = some tops) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (wotsPkAdrs adrs)) tops.toList)
  | wotsChain (adrs : Adrs) (i t : ℕ) (x v : core.Y)
      (hx : simulateQ c.toPartialImpl (secret (wotsSkAdrs adrs i)) = some x)
      (h : chain? core c pk (wotsChainAdrs adrs i) x 0 t = some v) :
      HonestEntry secret pk c
        (.thash pk (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress t)) [v])
  | forsLeaf (adrs : Adrs) (t : ℕ) (x : core.Y)
      (hx : simulateQ c.toPartialImpl (secret (forsSkAdrs adrs t)) = some x) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (forsNodeAdrs adrs 0 t)) [x])
  | forsNode (adrs : Adrs) (h i : ℕ) (l r : core.Y) (hh : 0 < h)
      (hl : forsNodeWithSecret? core c secret pk adrs (h - 1) (2 * i) = some l)
      (hr : forsNodeWithSecret? core c secret pk adrs (h - 1) (2 * i + 1) = some r) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (forsNodeAdrs adrs h i)) [l, r])
  | forsRoots (adrs : Adrs) (roots : Vector core.Y vp.params.k)
      (h : ∀ i : Fin vp.params.k,
        forsNodeWithSecret? core c secret pk adrs vp.params.a i.val = some roots[i]) :
      HonestEntry secret pk c (.thash pk (core.adrsToKey (forsPkAdrs adrs)) roots.toList)

/-- An honest entry stays honest in a larger cache. -/
theorem HonestEntry.mono {secret : Adrs → OracleComp (publicHashSpec core) core.Y}
    {pk : core.PkSeed} {c c' : PublicHash.Cache core} (h : c ≤ c')
    {t : (publicHashSpec core).Domain} (ht : HonestEntry secret pk c t) :
    HonestEntry secret pk c' t := by
  induction ht with
  | xmssNode adrs height i l r hheight hl hr =>
    exact .xmssNode adrs height i l r hheight (QueryCache.simulateQ_toPartialImpl_mono h _ hl)
      (QueryCache.simulateQ_toPartialImpl_mono h _ hr)
  | wotsPk adrs tops hw =>
    exact .wotsPk adrs tops (QueryCache.simulateQ_toPartialImpl_mono h _ hw)
  | wotsChain adrs i steps x v hx hv =>
    exact .wotsChain adrs i steps x v (QueryCache.simulateQ_toPartialImpl_mono h _ hx)
      (QueryCache.simulateQ_toPartialImpl_mono h _ hv)
  | forsLeaf adrs leaf x hx =>
    exact .forsLeaf adrs leaf x (QueryCache.simulateQ_toPartialImpl_mono h _ hx)
  | forsNode adrs height i l r hheight hl hr =>
    exact .forsNode adrs height i l r hheight (QueryCache.simulateQ_toPartialImpl_mono h _ hl)
      (QueryCache.simulateQ_toPartialImpl_mono h _ hr)
  | forsRoots adrs roots hr =>
    exact .forsRoots adrs roots fun i => QueryCache.simulateQ_toPartialImpl_mono h _ (hr i)

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
`secret`.  Either a WOTS+ chain value at a hidden step `t` of chain `i` of the leaf the replay
enters at layer `j`, on the honest chain from the settled secret `x`, reached by the forger's chain
from its own signature entry at the step its message selects; or, at a FORS coordinate no logged
signature opened, the forgery carries the settled secret there. -/
@[expose] def HiddenHit (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (o : RomOutcome vp core) (c : PublicHash.Cache core) : Prop :=
  (∃ (j : Fin vp.params.d) (pos : LayerPosition vp) (m : core.Y) (i : Fin vp.params.len)
      (t : ℕ) (x v : core.Y),
    ForgerLayer o c j pos m ∧ HiddenChainValue secret o c j pos i.val t ∧
    simulateQ c.toPartialImpl
      (secret (wotsSkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)) = some x ∧
    chain? core c o.pk.pkSeed (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val) x 0 t =
      some v ∧
    chainStepsCore core m i.val ≤ t ∧
    chain? core c o.pk.pkSeed (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)
      (o.sig.hypertree[j]).wots[i] (chainStepsCore core m i.val)
      (t - chainStepsCore core m i.val) = some v) ∨
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
to the settled honest chain tops at that leaf. -/
theorem xmssPkFromSig?_cases (pk : core.PkSeed) (c : PublicHash.Cache core) (adrs : Adrs)
    (idx : ℕ) (hidx : idx < 2 ^ vp.params.hp) (sig : XmssSig vp.params core) (msg : core.Y)
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
    hleaf | ⟨h, l, rr, l', r', v, hh, -, hne, hl, hr, hq, hq'⟩
  · simp only [xmssLeafWithSecret, wotsPkGenWithSecret, simulateQ_bind_eq_some_iff,
      simulateQ_toPartialImpl_tl] at hleaf
    obtain ⟨tops, htops, hTl⟩ := hleaf
    by_cases heq : tops = tops'
    · subst heq
      exact Or.inr ⟨tops, htops', htops⟩
    · exact Or.inl ⟨core.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs idx)), tops.toList,
        tops'.toList, leaf', HonestEntry.wotsPk _ tops htops, mt Vector.toList_inj.mp heq, hTl,
        hTl'⟩
  · simp only [xmssNodeHashM, xmssNodeHashWith, simulateQ_toPartialImpl_h] at hq hq'
    refine Or.inl ⟨core.adrsToKey (xmssNodeAdrs adrs h (idx / 2 ^ h)), [l, rr], [l', r'], v,
      HonestEntry.xmssNode adrs h (idx / 2 ^ h) l rr hh hl hr, fun hlist => hne ?_, hq, hq'⟩
    simp only [List.cons.injEq, and_true] at hlist
    exact Prod.ext hlist.1 hlist.2

/-- A settled forger chain from `x` at step `a` that reaches the settled honest chain top of
chain `i`, whose settled secret is `x₀`, either collides with the honest chain (a same-address `F`
target collision, both entries cached) or starts at the honest chain value at step `a`. -/
theorem wotsChain_cases (pk : core.PkSeed) (c : PublicHash.Cache core) (adrs : Adrs) (i a : ℕ)
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
      w', HonestEntry.wotsChain adrs i (a + j) x₀ v' hx₀ ?_, fun h => hne ?_, hqv, hqu⟩
    · rw [chain?_add_eq_some_iff]
      exact ⟨va, hva, by rwa [Nat.zero_add]⟩
    · simp only [List.cons.injEq, and_true] at h
      exact h.symm

/-- Forger chain tops settled at the settled honest chain tops yield either a same-address
target collision, or, on every chain, the secret is settled and the forger's WOTS+ signature entry
is the honest chain value at the step its message selects. -/
theorem wotsLeaf_cases (pk : core.PkSeed) (c : PublicHash.Cache core) (adrs : Adrs)
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
  exact ⟨x₀, hx₀, (wotsChain_cases secret pk c adrs i.val _ (chainStepsCore_le core m' i.val)
    sig[i.val] x₀ tops[i] hx₀ (hforge i) hchain).resolve_left hcoll⟩

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
  rcases xmssPkFromSig?_cases secret o.pk.pkSeed c pos.toAdrs pos.leaf.val pos.leaf.isLt _ m'
      hforge hhonest with h | ⟨tops, htops', htops⟩
  · exact Or.inl h
  rcases wotsLeaf_cases secret o.pk.pkSeed c _ _ m' tops htops' htops with h | hall
  · exact Or.inl h
  by_cases hused : UsedLeaf o c j pos
  · obtain ⟨m, hm⟩ := hmsg hused
    by_cases hmm : m = m'
    · exact Or.inr (Or.inr ⟨hused, hmm ▸ hm⟩)
    · obtain ⟨i, hi, hlt⟩ := chainStepsCore_two_encodings (core := core) vp.valid laws (Ne.symm hmm)
      obtain ⟨x₀, hx₀, hchain⟩ := hall ⟨i, hi⟩
      exact Or.inr (Or.inl (Or.inl ⟨j, pos, m', ⟨i, hi⟩, chainStepsCore core m' i, x₀, _, hlayer,
        fun _ => ⟨m, hm, hlt⟩, hx₀, hchain, le_rfl, by simp⟩))
  · obtain ⟨x₀, hx₀, hchain⟩ := hall ⟨0, Params.len_pos _⟩
    exact Or.inr (Or.inl (Or.inl ⟨j, pos, m', ⟨0, Params.len_pos _⟩, chainStepsCore core m' 0, x₀,
      _, hlayer, fun h => absurd h hused, hx₀, hchain, le_rfl, by simp⟩))

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
  set md := (splitDigest vp.params digest).md.toList
  set adrs := (splitDigest vp.params digest).forsAdrs
  rw [forsPkFromSig?, simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff] at hforge
  rw [forsPkGenWithSecret?_eq_some_iff] at hhonest
  obtain ⟨roots', hper', hTk'⟩ := hforge
  obtain ⟨roots, hper, hTk⟩ := hhonest
  by_cases hroots : roots = roots'
  swap
  · exact Or.inl ⟨core.adrsToKey (forsPkAdrs adrs), roots.toList, roots'.toList, forsPk,
      HonestEntry.forsRoots adrs roots hper, mt Vector.toList_inj.mp hroots, hTk, hTk'⟩
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
    hleaf | ⟨h, l, rr, l', r', v, hh, -, hne, hl, hr, hq, hq'⟩
  · simp only [forsLeafWithSecret, simulateQ_bind_eq_some_iff, simulateQ_toPartialImpl_f]
      at hleaf
    obtain ⟨x, hx, hleaf⟩ := hleaf
    refine ⟨core.adrsToKey (forsNodeAdrs adrs 0
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)), [x], [(o.sig.fors[i.val]).sk],
      leaf', HonestEntry.forsLeaf adrs _ x hx, fun h => hi ?_, hleaf, hF'⟩
    simp only [List.cons.injEq, and_true] at h
    rw [forsSigLeafIndex_eq, ← h]
    exact hx
  · simp only [forsNodeHashWith, simulateQ_toPartialImpl_h] at hq hq'
    refine ⟨core.adrsToKey (forsNodeAdrs adrs h _), [l, rr], [l', r'], v,
      HonestEntry.forsNode adrs h _ l rr hh hl hr, fun hlist => hne ?_, hq, hq'⟩
    simp only [List.cons.injEq, and_true] at hlist
    exact Prod.ext hlist.1 hlist.2

end Descent

end SLHDSA.Security.WithSecret
