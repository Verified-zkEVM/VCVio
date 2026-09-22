/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CacheDecomposition
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.OptionCoverage
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Sibling

/-!
# Coverage of a signed-through XMSS tree under a public-hash cache

An XMSS tree is *signed through* at leaf `idx` in a cache `c` when the signature program
(FIPS 205 Algorithm 10) and the signer's own recovery of the root from that signature
(Algorithm 11) are both settled under `QueryCache.toPartialImpl c`.  This module shows that such
a tree is settled in its entirety: every honest subtree root `xmssNodeM core sk pk adrs z t`
with `z ≤ p.hp` and `t < 2 ^ (p.hp - z)` reads to `some _`, the honest root reads to the
recovered root, and at every internal node the honest `H` entry at the node's `TREE` address is
in the cache with the settled honest children as its input.

The argument has two halves.  On the root path of `idx`, the signer's WOTS+ chain prefixes and
the recovery's chain suffixes compose to the honest leaf
(`simulateQ_toPartialImpl_xmssLeafM_eq_some_of_xmssSignM`), and the settled climb from that leaf
along the settled authentication path settles every ancestor
(`simulateQ_toPartialImpl_xmssNodeM_div_pow_eq_some_of_xmssSignM`).  Off the root path, every
node lies under a sibling subtree whose root is an entry of the settled authentication path
(`exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_sibling`).  The classification
`PerfectMerkleTree.eq_div_pow_or_exists_sibling` joins the halves.  For the top tree, key
generation alone (`GeneralHypertree.rootM`) settles every node and every full WOTS+ chain.  The
same climb argument applies to a FORS instance: a settled FORS signature whose recovered public
key is settled settles the honest FORS public key, at the recovered value
(`simulateQ_toPartialImpl_forsPkGenM_eq_some_of_forsSignM`).

Coverage read the other way round bounds the cache from below: a settled honest subtree at height
`z` forces `2 ^ z` cache entries, once the leaves' certifying entries are pairwise distinct
(`pow_le_enncard_of_forsNode?`, `pow_le_enncard_of_xmssNode?`, over the generic
`PerfectMerkleTree.pow_le_enncard_of_simulateQ_merkleRootM`).  The distinctness hypothesis is
**necessary for an arbitrary core** — the unconditional form is false, refuted generically by
`PerfectMerkleTree.not_forall_pow_le_enncard_of_simulateQ_merkleRootM` and at `forsNode?` itself
by the degenerate core of `HashSigTest.SLHDSA.RomKeyed` — but it is not an extra assumption at a
shipped bundle: `injOn_forsLeafKey_of_injOn_adrsToKey` and `injOn_xmssLeafKey_of_injOn_adrsToKey`
reduce it to injectivity of the address encoding on a set containing the leaf addresses, which at
the FIPS SHA-2 bundle is an address-range fact with no hash assumption
(`HashSigTest.SLHDSA.RomKeyed`).

## Scope

* No property of any particular cache is proved here; which entries a run of the counted
  random-oracle experiment settles belongs to `HashSig.SLHDSA.Security.RomTranscript`.
* The generic Merkle facts are in `VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Sibling`
  and `…NatIndexed.OptionCoverage`; the one-query, WOTS+ and XMSS decompositions are in
  `HashSig.SLHDSA.Security.CacheDecomposition`.
* Nothing here is probabilistic, and nothing here is quantum: the cache is a classical table.

## Labels

Fifteen declarations.

*Signed-through tree*: `simulateQ_toPartialImpl_xmssLeafM_eq_some_of_xmssSignM`,
`simulateQ_toPartialImpl_xmssNodeM_div_pow_eq_some_of_xmssSignM`,
`exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_sibling`,
`exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_xmssSignM`,
`simulateQ_toPartialImpl_xmssRootM_eq_some_of_xmssSignM`,
`exists_xmssNodeHash_entry_of_xmssSignM`.

*Top tree from key generation*: `exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_rootM`,
`exists_simulateQ_toPartialImpl_chainM_eq_some_of_rootM`.

*FORS instance*: `simulateQ_toPartialImpl_forsPkGenM_eq_some_of_forsSignM`.

*Leaf-key functions*: `forsLeafKey`, `xmssLeafKey`.

*Cache-size lower bounds*: `pow_le_enncard_of_forsNode?`, `pow_le_enncard_of_xmssNode?`,
`injOn_forsLeafKey_of_injOn_adrsToKey`, `injOn_xmssLeafKey_of_injOn_adrsToKey`.

## References

- NIST FIPS 205, §6.2--§6.3 and §8.2--§8.4, Algorithms 9--11 and 14--17
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

/-! ## A signed-through XMSS tree -/

section Xmss

variable {p : Params} (core : CorePrimitives p) (c : PublicHash.Cache core)
  (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ)
  {sig : XmssSig p core}
  (hsign : simulateQ c.toPartialImpl (xmssSignM core msg sk pk adrs idx) = some sig)
include hsign

/-- The honest leaf at the signed index of a signed-through tree is settled, at the leaf the
signer's own recovery climbed from, and that climb is settled at the recovered root. -/
theorem simulateQ_toPartialImpl_xmssLeafM_eq_some_of_xmssSignM {root : core.Y}
    (hrec : simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs) = some root) :
    ∃ leaf : core.Y, simulateQ c.toPartialImpl (xmssLeafM core sk pk adrs idx) = some leaf ∧
      simulateQ c.toPartialImpl (PerfectMerkleTree.climbM
        (xmssNodeHashM core pk adrs) idx leaf sig.auth.toList) = some root := by
  obtain ⟨-, hwots⟩ := (simulateQ_toPartialImpl_xmssSignM_eq_some_iff core c msg sk pk adrs
    idx).mp hsign
  obtain ⟨leaf, ⟨tops, htops, hleaf⟩, hclimb⟩ :=
    (simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff core c idx sig msg pk adrs).mp hrec
  refine ⟨leaf, ?_, hclimb⟩
  simp only [xmssLeafM, xmssLeafWith, wotsPkGenWith, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_tl]
  exact ⟨tops, simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_of_wotsSignM core c msg sk pk
    (wotsLeafAdrs adrs idx) hwots htops, hleaf⟩

/-- Every honest ancestor of the signed leaf of a signed-through tree is settled, the root at
the recovered value. -/
theorem simulateQ_toPartialImpl_xmssNodeM_div_pow_eq_some_of_xmssSignM {root : core.Y}
    (hrec : simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs) = some root) :
    simulateQ c.toPartialImpl (xmssNodeM core sk pk adrs p.hp (idx / 2 ^ p.hp)) = some root ∧
      ∀ z ≤ p.hp, ∃ v, simulateQ c.toPartialImpl (xmssNodeM core sk pk adrs z (idx / 2 ^ z)) =
        some v := by
  obtain ⟨hpath, -⟩ := (simulateQ_toPartialImpl_xmssSignM_eq_some_iff core c msg sk pk adrs
    idx).mp hsign
  obtain ⟨leaf, hleaf, hclimb⟩ :=
    simulateQ_toPartialImpl_xmssLeafM_eq_some_of_xmssSignM core c msg sk pk adrs idx hsign hrec
  have hroot := PerfectMerkleTree.simulateQ_merkleRootM_div_pow_eq_some_of_climbM
    c.toPartialImpl (xmssLeafM core sk pk adrs) (xmssNodeHashM core pk adrs) idx hleaf hpath hclimb
  refine ⟨hroot, fun z hz => ?_⟩
  rw [xmssNodeM_eq_merkleRootM]
  exact PerfectMerkleTree.exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq _ _ _ hroot hz
    (PerfectMerkleTree.div_pow_eq_div_pow_div_pow idx z p.hp hz).symm

/-- Every node in a sibling subtree of the signed leaf's root path is settled by the signature
alone. -/
theorem exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_sibling {z s t : ℕ} (hzs : z ≤ s)
    (hs : s < p.hp) (ht : t / 2 ^ (s - z) = PerfectMerkleTree.sibling (idx / 2 ^ s)) :
    ∃ v, simulateQ c.toPartialImpl (xmssNodeM core sk pk adrs z t) = some v := by
  obtain ⟨hpath, -⟩ := (simulateQ_toPartialImpl_xmssSignM_eq_some_iff core c msg sk pk adrs
    idx).mp hsign
  rw [PerfectMerkleTree.simulateQ_intrinsicAuthPathM_eq_some_iff] at hpath
  exact PerfectMerkleTree.exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq _ _ _
    (hpath ⟨s, hs⟩) hzs ht

variable (hidx : idx < 2 ^ p.hp) {root : core.Y}
  (hrec : simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs) = some root)
include hidx hrec

/-- Every node of a signed-through tree is settled. -/
theorem exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_xmssSignM :
    ∀ z t, z ≤ p.hp → t < 2 ^ (p.hp - z) →
      ∃ v, simulateQ c.toPartialImpl (xmssNodeM core sk pk adrs z t) = some v := by
  intro z t hz ht
  rcases PerfectMerkleTree.eq_div_pow_or_exists_sibling hidx hz ht with rfl | ⟨s, hzs, hs, hsib⟩
  · exact (simulateQ_toPartialImpl_xmssNodeM_div_pow_eq_some_of_xmssSignM core c msg sk pk adrs
      idx hsign hrec).2 z hz
  · exact exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_sibling core c msg sk pk adrs idx
      hsign hzs hs hsib

/-- The honest root of a signed-through tree is settled, at the recovered root. -/
theorem simulateQ_toPartialImpl_xmssRootM_eq_some_of_xmssSignM :
    simulateQ c.toPartialImpl (xmssRootM core sk pk adrs) = some root := by
  have h := (simulateQ_toPartialImpl_xmssNodeM_div_pow_eq_some_of_xmssSignM core c msg sk pk adrs
    idx hsign hrec).1
  rwa [Nat.div_eq_of_lt hidx] at h

/-- At every internal node `(h, i)` of a signed-through tree the honest children are settled and
the honest `H` entry at the node's `TREE` address, on those children, is in the cache. -/
theorem exists_xmssNodeHash_entry_of_xmssSignM (h i : ℕ) (hpos : 0 < h) (hle : h ≤ p.hp)
    (hi : i < 2 ^ (p.hp - h)) :
    ∃ l r v, simulateQ c.toPartialImpl (xmssNodeM core sk pk adrs (h - 1) (2 * i)) = some l ∧
      simulateQ c.toPartialImpl (xmssNodeM core sk pk adrs (h - 1) (2 * i + 1)) = some r ∧
      c (.thash pk (core.adrsToKey (xmssNodeAdrs adrs h i)) [l, r]) = some v := by
  obtain ⟨w, hw⟩ := exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_xmssSignM core c msg sk
    pk adrs idx hsign hidx hrec h i hle hi
  obtain ⟨h', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [xmssNodeM_succ] at hw
  simp only [simulateQ_bind_eq_some_iff, xmssNodeHashM, xmssNodeHashWith,
    simulateQ_toPartialImpl_h] at hw
  obtain ⟨l, hl, r, hr, hq⟩ := hw
  exact ⟨l, r, w, hl, hr, hq⟩

end Xmss

/-! ## The top tree from key generation -/

section TopTree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) (c : PublicHash.Cache core)
  (sk : core.SkSeed) (pk : core.PkSeed) {pkRoot : core.Y}
  (h : simulateQ c.toPartialImpl (GeneralHypertree.rootM vp core sk pk) = some pkRoot)
include h

/-- Every node of the top tree is settled by key generation. -/
theorem exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_rootM :
    ∀ z t, z ≤ vp.params.hp → t < 2 ^ (vp.params.hp - z) →
      ∃ v, simulateQ c.toPartialImpl
        (xmssNodeM core sk pk (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) z t) = some v := by
  intro z t hz ht
  rw [xmssNodeM_eq_merkleRootM]
  exact PerfectMerkleTree.exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq _ _ _ h hz
    (Nat.div_eq_of_lt ht)

/-- Every WOTS+ chain of every leaf of the top tree is settled by key generation, at its full
length. -/
theorem exists_simulateQ_toPartialImpl_chainM_eq_some_of_rootM (t : ℕ)
    (ht : t < 2 ^ vp.params.hp)
    (i : Fin vp.params.len) :
    ∃ v, simulateQ c.toPartialImpl (chainM core pk
      (wotsChainAdrs (wotsLeafAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) t) i.val)
      (core.PRF pk sk
        (wotsSkAdrs (wotsLeafAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) t) i.val))
      0 (vp.params.w - 1)) = some v := by
  obtain ⟨leaf, hleaf⟩ := exists_simulateQ_toPartialImpl_xmssNodeM_eq_some_of_rootM core c sk pk
    h 0 t (Nat.zero_le _) (by simpa using ht)
  rw [xmssNodeM_zero, xmssLeafM, xmssLeafWith, wotsPkGenWith, simulateQ_bind_eq_some_iff] at hleaf
  obtain ⟨tops, htops, -⟩ := hleaf
  exact ⟨tops[i], (simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_iff core c sk pk _).mp htops i⟩

end TopTree

/-! ## FORS coverage -/

section Fors

variable {p : Params} (core : CorePrimitives p) (c : PublicHash.Cache core) (md : List Byte)
  (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs)

/-- A settled FORS signature whose recovered public key is settled settles the honest FORS public
key, at the recovered value: per tree, the recovery's `F` entry on the revealed secret is the
honest leaf, and the settled climb along the signed authentication path settles the honest
root. -/
theorem simulateQ_toPartialImpl_forsPkGenM_eq_some_of_forsSignM {sig : ForsSigCore p core}
    {fpk : core.Y}
    (hsign : simulateQ c.toPartialImpl (forsSignM core md sk pk adrs) = some sig)
    (hrec : simulateQ c.toPartialImpl (forsPkFromSigM core sig md pk adrs) = some fpk) :
    simulateQ c.toPartialImpl (forsPkGenM core sk pk adrs) = some fpk := by
  rw [simulateQ_toPartialImpl_forsSignM_eq_some_iff] at hsign
  rw [simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff] at hrec
  rw [simulateQ_toPartialImpl_forsPkGenM_eq_some_iff]
  obtain ⟨roots, hper, hTk⟩ := hrec
  refine ⟨roots, fun i => ?_, hTk⟩
  obtain ⟨path, hpath, hsig⟩ := hsign i
  obtain ⟨leaf, hF, hclimb⟩ := hper i
  rw [Fin.getElem_fin] at hsig
  rw [← hsig] at hF hclimb
  have hleaf : simulateQ c.toPartialImpl (forsLeafWith core (PublicHash.f core pk) sk pk adrs
      (i.val * 2 ^ p.a + forsIdx p md i.val)) = some leaf := by
    simpa only [forsLeafWith, simulateQ_toPartialImpl_f] using hF
  have h := PerfectMerkleTree.simulateQ_merkleRootM_div_pow_eq_some_of_climbM c.toPartialImpl _ _
    _ hleaf hpath hclimb
  rwa [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos p.a),
    Nat.div_eq_of_lt (forsIdx_lt p md i.val), Nat.zero_add] at h

end Fors

/-! ## Cache-size lower bounds -/

section CacheSize

variable {p : Params} (core : CorePrimitives p) (c : PublicHash.Cache core) (sk : core.SkSeed)
  (pk : core.PkSeed) (adrs : Adrs)

/-- The FORS `F` query of leaf `i`: the leaf role address on the leaf's own secret value.  A
query determined by the seeds, the base address and `i` alone. -/
@[expose] def forsLeafKey (i : ℕ) : (publicHashSpec core).Domain :=
  .thash pk (core.adrsToKey (forsNodeAdrs adrs 0 i)) [forsSkGenCore core sk pk adrs i]

/-- **A settled honest FORS subtree at height `z` forces `2 ^ z` cache entries.**  Each of the
`2 ^ z` leaves of the subtree forces its own `F` query; the hypothesis is that those `2 ^ z`
queries are distinct, and it is **necessary for an arbitrary core** rather than convenient, since
the unconditional form is false.  At a concrete bundle it is discharged from address-range facts
through `injOn_forsLeafKey_of_injOn_adrsToKey`. -/
theorem pow_le_enncard_of_forsNode? {z t : ℕ}
    (hinj : Set.InjOn (forsLeafKey core sk pk adrs) {i | i / 2 ^ z = t})
    {v : core.Y} (h : forsNode? core c sk pk adrs z t = some v) :
    ((2 ^ z : ℕ) : ENNReal) ≤ QueryCache.enncard c :=
  PerfectMerkleTree.pow_le_enncard_of_simulateQ_merkleRootM _ _ c _
    (fun i w hw => by
      rw [show forsLeafWith core (PublicHash.f core pk) sk pk adrs i
            = PublicHash.f core pk (forsNodeAdrs adrs 0 i)
                (forsSkGenCore core sk pk adrs i) from rfl,
        simulateQ_toPartialImpl_f] at hw
      exact hw ▸ rfl)
    hinj h

/-- The chain-step-zero `F` query of the first WOTS+ chain of XMSS leaf `i`: a query determined
by the seeds, the base address and `i` alone.  The leaf's own final compression query is not,
its input being the settled chain tops. -/
@[expose] def xmssLeafKey (i : ℕ) : (publicHashSpec core).Domain :=
  .thash pk (core.adrsToKey ((wotsChainAdrs (wotsLeafAdrs adrs i) 0).setHashAddress 0))
    [core.PRF pk sk (wotsSkAdrs (wotsLeafAdrs adrs i) 0)]

/-- **A settled honest XMSS subtree at height `z` forces `2 ^ z` cache entries.**  Each of the
`2 ^ z` leaves of the subtree forces its own chain-step-zero `F` query; the hypothesis is that
those `2 ^ z` queries are distinct, and it is **necessary for an arbitrary core** rather than
convenient, since the unconditional form is false.  At a concrete bundle it is discharged from
address-range facts through `injOn_xmssLeafKey_of_injOn_adrsToKey`. -/
theorem pow_le_enncard_of_xmssNode? (hlen : 0 < p.len) (hw : 1 < p.w) {z t : ℕ}
    (hinj : Set.InjOn (xmssLeafKey core sk pk adrs) {i | i / 2 ^ z = t})
    {v : core.Y} (h : xmssNode? core c sk pk adrs z t = some v) :
    ((2 ^ z : ℕ) : ENNReal) ≤ QueryCache.enncard c := by
  refine PerfectMerkleTree.pow_le_enncard_of_simulateQ_merkleRootM _ _ c _
    (fun i w hleaf => ?_) hinj (by rwa [xmssNode?, xmssNodeM_eq_merkleRootM] at h)
  simp only [xmssLeafM, xmssLeafWith, wotsPkGenWith, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_tl] at hleaf
  obtain ⟨tops, htops, -⟩ := hleaf
  obtain ⟨z', w', hz', hq⟩ := chain?_query_settled core c pk
    (wotsChainAdrs (wotsLeafAdrs adrs i) 0)
    (core.PRF pk sk (wotsSkAdrs (wotsLeafAdrs adrs i) 0)) 0 (t := 0) (by omega)
    ((simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_iff core c sk pk
      (wotsLeafAdrs adrs i)).mp htops ⟨0, hlen⟩)
  obtain rfl : z' = core.PRF pk sk (wotsSkAdrs (wotsLeafAdrs adrs i) 0) :=
    Option.some_inj.mp (hz'.symm.trans (chain?_zero core c pk
      (wotsChainAdrs (wotsLeafAdrs adrs i) 0)
      (core.PRF pk sk (wotsSkAdrs (wotsLeafAdrs adrs i) 0)) 0))
  exact hq ▸ rfl

/-- **The FORS leaf keys are distinct as soon as the address encoding is injective on a set of
addresses containing the leaf addresses.**  No property of the hash or of the secret values is
used: the leaf index is a field of the leaf address. -/
theorem injOn_forsLeafKey_of_injOn_adrsToKey {D : Set Adrs}
    (hinj : Set.InjOn core.adrsToKey D) {z t : ℕ}
    (hmem : ∀ i ∈ {i : ℕ | i / 2 ^ z = t}, forsNodeAdrs adrs 0 i ∈ D) :
    Set.InjOn (forsLeafKey core sk pk adrs) {i | i / 2 ^ z = t} := by
  intro i hi j hj hq
  simp only [forsLeafKey, PublicHashQuery.thash.injEq] at hq
  exact congrArg Adrs.word3 (hinj (hmem i hi) (hmem j hj) hq.2.1)

/-- **The XMSS leaf keys are distinct as soon as the address encoding is injective on a set of
addresses containing the chain-step-zero addresses.**  No property of the hash or of the secret
values is used: the leaf index is the key-pair field of that address. -/
theorem injOn_xmssLeafKey_of_injOn_adrsToKey {D : Set Adrs}
    (hinj : Set.InjOn core.adrsToKey D) {z t : ℕ}
    (hmem : ∀ i ∈ {i : ℕ | i / 2 ^ z = t},
      (wotsChainAdrs (wotsLeafAdrs adrs i) 0).setHashAddress 0 ∈ D) :
    Set.InjOn (xmssLeafKey core sk pk adrs) {i | i / 2 ^ z = t} := by
  intro i hi j hj hq
  simp only [xmssLeafKey, PublicHashQuery.thash.injEq] at hq
  exact congrArg Adrs.word1 (hinj (hmem i hi) (hmem j hj) hq.2.1)

end CacheSize

end SLHDSA.Security
