/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CacheDecomposition
public import HashSig.SLHDSA.Security.Target
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.OptionCoverage
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Sibling

/-!
# Honest SLH-DSA values under a public-hash cache, at a secret provider

The honest programs of `HashSig.SLHDSA.SecretProvider` draw every WOTS+ and FORS secret from a
provider `secret : Adrs → OracleComp (publicHashSpec core) core.Y`.  Read under the partial
oracle `QueryCache.toPartialImpl c`, such a program settles exactly when every secret it draws and
every hash query it issues is settled.  This module states that reading for every program that
draws a secret, at an arbitrary provider; the provider of interest is the oracle-backed
`oracleSecret core e pk sk` of `HashSig.SLHDSA.Security.Target`, whose every draw is one `F` query
of the secret seed at the draw's `PRF` address (`simulateQ_toPartialImpl_oracleSecret`).  At the
oracle-backed provider a settled reading therefore never supplies a secret the cache does not
record.  The programs of `HashSig.SLHDSA.Security.Target` run in a monad reaching a larger
oracle; every query-preserving monad morphism fixes an oracle-backed draw
(`oracleSecret_natural`), so key generation and signing there are the images of the programs
read here (`keygenInternalWithSecretM_oracleSecret_eq_ofSimulateQ`,
`signInternalWithSecretRandomizerM_oracleSecret_eq_ofSimulateQ`).

The readers `wotsPkGenTopsWithSecret?`, `xmssNodeWithSecret?`, `xmssRootWithSecret?`,
`forsNodeWithSecret?` and `forsPkGenWithSecret?` are the honest programs under the cache.  The
`*_eq_some_iff` lemmas decompose the WOTS+, XMSS, FORS, hypertree and Algorithm 19 programs into
their settled draws and queries, each secret draw a separate settled-secret conjunct.  The coverage
lemmas state that a signed-through XMSS tree is settled along the signed leaf's root path, up to
its honest root, and that a settled FORS signature whose recovered key is settled settles the
honest FORS public key.

## Scope

* The verifier's programs draw no secret; their decompositions are those of
  `HashSig.SLHDSA.Security.CacheDecomposition`.
* Key generation over a provider is the top-tree root program itself
  (`keygenInternalWithSecretM` is `GeneralHypertree.rootWithSecretM`), so the decomposition of
  Algorithm 18 into a root reading and the assembled key pair has no counterpart here.
* No property of any particular cache is proved here, and nothing here is probabilistic or quantum.

## Labels

*Readers*: `wotsPkGenTopsWithSecret?`, `xmssNodeWithSecret?`, `xmssRootWithSecret?`,
`forsNodeWithSecret?`, `forsPkGenWithSecret?`.

*The oracle-backed provider*: `simulateQ_toPartialImpl_oracleSecret`, `oracleSecret_natural`,
`keygenInternalWithSecretM_oracleSecret_eq_ofSimulateQ`,
`signInternalWithSecretRandomizerM_oracleSecret_eq_ofSimulateQ`.

*WOTS+ and XMSS*: `wotsPkGenTopsWithSecret?_eq_some_iff`,
`simulateQ_toPartialImpl_wotsSignWithSecret_eq_some_iff`,
`wotsPkGenTopsWithSecret?_eq_some_of_wotsSignWithSecret`,
`simulateQ_toPartialImpl_xmssSignWithSecret_eq_some_iff`.

*FORS*: `forsPkGenWithSecret?_eq_some_iff`,
`simulateQ_toPartialImpl_forsSignWithSecret_eq_some_iff`.

*Hypertree layers and Algorithm 19*:
`simulateQ_toPartialImpl_signFromPositionWithSecret_add_two_eq_some_iff`,
`simulateQ_toPartialImpl_signFromPositionWithSecret_one_false_eq_some_iff`,
`simulateQ_toPartialImpl_signInternalWithSecretRandomizerM_eq_some_iff`,
`components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM`.

*Signed-through XMSS tree*:
`simulateQ_toPartialImpl_xmssLeafWithSecret_eq_some_of_xmssSignWithSecret`,
`xmssNodeWithSecret?_div_pow_eq_some_of_xmssSignWithSecret`,
`xmssRootWithSecret?_eq_some_of_xmssSignWithSecret`.

*FORS coverage*: `forsPkGenWithSecret?_eq_some_of_forsSignWithSecret`.

Twenty-three declarations, none private.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

section Components

variable {p : Params} (core : CorePrimitives p) (c : PublicHash.Cache core)
  (secret : Adrs → OracleComp (publicHashSpec core) core.Y)

/-! ## Readers -/

/-- The honest WOTS+ chain tops at `adrs`, over the provider `secret`, read off a cache. -/
@[expose]
def wotsPkGenTopsWithSecret? (pk : core.PkSeed) (adrs : Adrs) : Option (Vector core.Y p.len) :=
  simulateQ c.toPartialImpl (wotsPkGenTopsWithSecret core (PublicHash.f core pk) secret adrs)

/-- The honest XMSS subtree root at height `z`, index `t`, over the provider `secret`, read off
a cache. -/
@[expose]
def xmssNodeWithSecret? (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) : Option core.Y :=
  simulateQ c.toPartialImpl (xmssNodeWithSecret core (PublicHash.f core pk)
    (PublicHash.tl core pk) (PublicHash.h core pk) secret adrs z t)

/-- The honest XMSS tree root, over the provider `secret`, read off a cache. -/
@[expose]
def xmssRootWithSecret? (pk : core.PkSeed) (adrs : Adrs) : Option core.Y :=
  simulateQ c.toPartialImpl (xmssRootWithSecret core (PublicHash.f core pk)
    (PublicHash.tl core pk) (PublicHash.h core pk) secret adrs)

/-- The honest FORS subtree root at height `z`, global leaf-numbered index `t`, over the provider
`secret`, read off a cache. -/
@[expose]
def forsNodeWithSecret? (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) : Option core.Y :=
  simulateQ c.toPartialImpl (PerfectMerkleTree.merkleRootM
    (forsLeafWithSecret core (PublicHash.f core pk) secret adrs)
    (forsNodeHashWith (PublicHash.h core pk) adrs) z t)

/-- The honest FORS public key, over the provider `secret`, read off a cache. -/
@[expose]
def forsPkGenWithSecret? (pk : core.PkSeed) (adrs : Adrs) : Option core.Y :=
  simulateQ c.toPartialImpl (forsPkGenWithSecret core (PublicHash.f core pk)
    (PublicHash.h core pk) (PublicHash.tl core pk) secret adrs)

/-! ## WOTS+ and XMSS -/

/-- The chain tops over a provider are settled exactly when, for every chain, the secret at its
`WOTS_PRF` address is settled and the full chain from that secret is settled, at the
corresponding top. -/
theorem wotsPkGenTopsWithSecret?_eq_some_iff (pk : core.PkSeed)
    (adrs : Adrs) {tops : Vector core.Y p.len} :
    wotsPkGenTopsWithSecret? core c secret pk adrs = some tops ↔
      ∀ i : Fin p.len, ∃ x, simulateQ c.toPartialImpl (secret (wotsSkAdrs adrs i.val)) = some x ∧
        simulateQ c.toPartialImpl (chainM core pk (wotsChainAdrs adrs i.val) x 0 (p.w - 1)) =
          some tops[i] := by
  simp only [wotsPkGenTopsWithSecret?, wotsPkGenTopsWithSecret, simulateQ_ofFnM_eq_some_iff,
    simulateQ_bind_eq_some_iff, chainM]

/-- A WOTS+ signature over a provider is settled exactly when, for every chain, the secret at its
`WOTS_PRF` address is settled and the message-selected chain prefix from it is settled, at the
corresponding signature entry. -/
theorem simulateQ_toPartialImpl_wotsSignWithSecret_eq_some_iff (msg : core.Y) (pk : core.PkSeed)
    (adrs : Adrs) {sig : WotsSig p core} :
    simulateQ c.toPartialImpl
        (wotsSignWithSecret core (PublicHash.f core pk) secret msg adrs) = some sig ↔
      ∀ i : Fin p.len, ∃ x, simulateQ c.toPartialImpl (secret (wotsSkAdrs adrs i.val)) = some x ∧
        simulateQ c.toPartialImpl (chainM core pk (wotsChainAdrs adrs i.val) x 0
          (chainStepsCore core msg i.val)) = some sig[i] := by
  simp only [wotsSignWithSecret, simulateQ_ofFnM_eq_some_iff, simulateQ_bind_eq_some_iff, chainM]

/-- A settled WOTS+ signature over a provider whose recovered chain tops are settled settles the
honest chain tops over that provider, at the recovered tops. -/
theorem wotsPkGenTopsWithSecret?_eq_some_of_wotsSignWithSecret
    (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) {sig : WotsSig p core}
    {tops : Vector core.Y p.len}
    (hsign : simulateQ c.toPartialImpl
      (wotsSignWithSecret core (PublicHash.f core pk) secret msg adrs) = some sig)
    (hrec : simulateQ c.toPartialImpl (wotsPkFromSigTopsM core sig msg pk adrs) = some tops) :
    wotsPkGenTopsWithSecret? core c secret pk adrs = some tops := by
  rw [simulateQ_toPartialImpl_wotsSignWithSecret_eq_some_iff] at hsign
  rw [simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff] at hrec
  rw [wotsPkGenTopsWithSecret?_eq_some_iff]
  intro i
  obtain ⟨x, hx, hpre⟩ := hsign i
  refine ⟨x, hx, ?_⟩
  rw [← Nat.add_sub_cancel' (chainStepsCore_le core msg i.val),
    simulateQ_toPartialImpl_chainM_add_eq_some_iff]
  exact ⟨sig[i], hpre, by rw [Nat.zero_add]; exact hrec i⟩

/-- An XMSS signature over a provider is settled exactly when the authentication path of its leaf
is settled, at the path it carries, and the WOTS+ signature at its leaf is settled, at the one it
carries. -/
theorem simulateQ_toPartialImpl_xmssSignWithSecret_eq_some_iff (msg : core.Y) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) {sig : XmssSig p core} :
    simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
        (PublicHash.tl core pk) (PublicHash.h core pk) secret msg adrs idx) = some sig ↔
      simulateQ c.toPartialImpl (PerfectMerkleTree.intrinsicAuthPathM
        (xmssLeafWithSecret core (PublicHash.f core pk) (PublicHash.tl core pk) secret adrs)
        (xmssNodeHashM core pk adrs) idx p.hp) = some sig.auth ∧
      simulateQ c.toPartialImpl (wotsSignWithSecret core (PublicHash.f core pk) secret msg
        (wotsLeafAdrs adrs idx)) = some sig.wots := by
  simp only [xmssSignWithSecret, simulateQ_bind_eq_some_iff, simulateQ_pure_eq_some_iff]
  exact ⟨fun ⟨_, hpath, _, hs, rfl⟩ => ⟨hpath, hs⟩, fun ⟨hpath, hs⟩ => ⟨_, hpath, _, hs, rfl⟩⟩

/-! ## FORS -/

/-- The honest FORS public key over a provider is settled exactly when every tree root is settled
and the `T_k` compression of the roots is cached. -/
theorem forsPkGenWithSecret?_eq_some_iff (pk : core.PkSeed) (adrs : Adrs)
    {fpk : core.Y} :
    forsPkGenWithSecret? core c secret pk adrs = some fpk ↔
      ∃ roots : Vector core.Y p.k,
        (∀ i : Fin p.k, forsNodeWithSecret? core c secret pk adrs p.a i.val = some roots[i]) ∧
        c (.thash pk (core.adrsToKey (forsPkAdrs adrs)) roots.toList) = some fpk := by
  simp only [forsPkGenWithSecret?, forsNodeWithSecret?, forsPkGenWithSecret, forsRootWithSecret,
    simulateQ_bind_eq_some_iff, simulateQ_ofFnM_eq_some_iff, simulateQ_toPartialImpl_tl]

/-- A FORS signature over a provider is settled exactly when, for every tree, the sibling-only
authentication path is settled and the secret at the selected leaf's `FORS_PRF` address is
settled, at the values the signature carries. -/
theorem simulateQ_toPartialImpl_forsSignWithSecret_eq_some_iff (md : List Byte) (pk : core.PkSeed)
    (adrs : Adrs) {sig : ForsSigCore p core} :
    simulateQ c.toPartialImpl (forsSignWithSecretM core secret md pk adrs) = some sig ↔
      ∀ i : Fin p.k, ∃ path : Vector core.Y p.a,
        simulateQ c.toPartialImpl (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret core (PublicHash.f core pk) secret adrs)
          (forsNodeHashWith (PublicHash.h core pk) adrs)
          (i.val * 2 ^ p.a + forsIdx p md i.val) p.a) = some path ∧
        ∃ x, simulateQ c.toPartialImpl
            (secret (forsSkAdrs adrs (i.val * 2 ^ p.a + forsIdx p md i.val))) = some x ∧
          (⟨x, path⟩ : ForsTreeSigCore p core) = sig[i] := by
  simp only [forsSignWithSecretM, forsSignWithSecret, simulateQ_ofFnM_eq_some_iff,
    simulateQ_bind_eq_some_iff, simulateQ_pure_eq_some_iff]

/-! ## A signed-through XMSS tree -/

section Xmss

variable (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) {sig : XmssSig p core}
  (hsign : simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
    (PublicHash.tl core pk) (PublicHash.h core pk) secret msg adrs idx) = some sig)
include hsign

/-- The honest leaf at the signed index of a tree signed through over a provider is settled, at
the leaf the signer's own recovery climbed from, and that climb is settled at the recovered
root. -/
theorem simulateQ_toPartialImpl_xmssLeafWithSecret_eq_some_of_xmssSignWithSecret {root : core.Y}
    (hrec : simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs) = some root) :
    ∃ leaf : core.Y, simulateQ c.toPartialImpl (xmssLeafWithSecret core (PublicHash.f core pk)
        (PublicHash.tl core pk) secret adrs idx) = some leaf ∧
      simulateQ c.toPartialImpl (PerfectMerkleTree.climbM
        (xmssNodeHashM core pk adrs) idx leaf sig.auth.toList) = some root := by
  obtain ⟨-, hwots⟩ := (simulateQ_toPartialImpl_xmssSignWithSecret_eq_some_iff core c secret msg
    pk adrs idx).mp hsign
  obtain ⟨leaf, ⟨tops, htops, hleaf⟩, hclimb⟩ :=
    (simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff core c idx sig msg pk adrs).mp hrec
  refine ⟨leaf, ?_, hclimb⟩
  simp only [xmssLeafWithSecret, wotsPkGenWithSecret, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_tl]
  exact ⟨tops, wotsPkGenTopsWithSecret?_eq_some_of_wotsSignWithSecret core
    c secret msg pk (wotsLeafAdrs adrs idx) hwots htops, hleaf⟩

/-- Every honest ancestor of the signed leaf of a tree signed through over a provider is settled,
the root at the recovered value. -/
theorem xmssNodeWithSecret?_div_pow_eq_some_of_xmssSignWithSecret {root : core.Y}
    (hrec : simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs) = some root) :
    xmssNodeWithSecret? core c secret pk adrs p.hp (idx / 2 ^ p.hp) = some root ∧
      ∀ z ≤ p.hp, ∃ v, xmssNodeWithSecret? core c secret pk adrs z (idx / 2 ^ z) = some v := by
  obtain ⟨hpath, -⟩ := (simulateQ_toPartialImpl_xmssSignWithSecret_eq_some_iff core c secret msg
    pk adrs idx).mp hsign
  obtain ⟨leaf, hleaf, hclimb⟩ :=
    simulateQ_toPartialImpl_xmssLeafWithSecret_eq_some_of_xmssSignWithSecret core c secret msg pk
      adrs idx hsign hrec
  have hroot := PerfectMerkleTree.simulateQ_merkleRootM_div_pow_eq_some_of_climbM
    c.toPartialImpl _ (xmssNodeHashM core pk adrs) idx hleaf hpath hclimb
  exact ⟨hroot, fun z hz => PerfectMerkleTree.exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq
    _ _ _ hroot hz (PerfectMerkleTree.div_pow_eq_div_pow_div_pow idx z p.hp hz).symm⟩

variable (hidx : idx < 2 ^ p.hp) {root : core.Y}
  (hrec : simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs) = some root)
include hidx hrec

/-- The honest root of a tree signed through over a provider is settled, at the recovered
root. -/
theorem xmssRootWithSecret?_eq_some_of_xmssSignWithSecret :
    xmssRootWithSecret? core c secret pk adrs = some root := by
  have h := (xmssNodeWithSecret?_div_pow_eq_some_of_xmssSignWithSecret core c secret msg pk adrs
    idx hsign hrec).1
  rwa [Nat.div_eq_of_lt hidx] at h

end Xmss

/-! ## FORS coverage -/

/-- A settled FORS signature over a provider whose recovered public key is settled settles the
honest FORS public key over that provider, at the recovered value. -/
theorem forsPkGenWithSecret?_eq_some_of_forsSignWithSecret (md : List Byte) (pk : core.PkSeed)
    (adrs : Adrs) {sig : ForsSigCore p core} {fpk : core.Y}
    (hsign : simulateQ c.toPartialImpl (forsSignWithSecretM core secret md pk adrs) = some sig)
    (hrec : simulateQ c.toPartialImpl (forsPkFromSigM core sig md pk adrs) = some fpk) :
    forsPkGenWithSecret? core c secret pk adrs = some fpk := by
  rw [simulateQ_toPartialImpl_forsSignWithSecret_eq_some_iff] at hsign
  rw [simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff] at hrec
  rw [forsPkGenWithSecret?_eq_some_iff]
  obtain ⟨roots, hper, hTk⟩ := hrec
  refine ⟨roots, fun i => ?_, hTk⟩
  obtain ⟨path, hpath, x, hx, hsig⟩ := hsign i
  obtain ⟨leaf, hF, hclimb⟩ := hper i
  rw [Fin.getElem_fin] at hsig
  rw [← hsig] at hF hclimb
  have hleaf : simulateQ c.toPartialImpl (forsLeafWithSecret core (PublicHash.f core pk) secret
      adrs (i.val * 2 ^ p.a + forsIdx p md i.val)) = some leaf := by
    simp only [forsLeafWithSecret, simulateQ_bind_eq_some_iff, simulateQ_toPartialImpl_f]
    exact ⟨x, hx, hF⟩
  have h := PerfectMerkleTree.simulateQ_merkleRootM_div_pow_eq_some_of_climbM c.toPartialImpl _ _
    _ hleaf hpath hclimb
  rwa [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos p.a),
    Nat.div_eq_of_lt (forsIdx_lt p md i.val), Nat.zero_add] at h

end Components

/-! ## Hypertree layers and Algorithm 19 -/

section Hypertree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) (c : PublicHash.Cache core)
  (secret : Adrs → OracleComp (publicHashSpec core) core.Y)

/-- Algorithm 12 over a provider with two or more layers left is settled exactly when the XMSS
signature at this position is settled, the root it recovers is settled, and the remaining layers
signed from that root are settled; the result is the remaining signatures with this one in
front. -/
theorem simulateQ_toPartialImpl_signFromPositionWithSecret_add_two_eq_some_iff
    (pk : core.PkSeed) (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (h : pos.layer.val + (layers + 2) = vp.params.d) (msg : core.Y)
    {sigs : Vector (XmssSig vp.params core) (layers + 2)} :
    simulateQ c.toPartialImpl (GeneralHypertree.signFromPositionWithSecret core
        (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) secret recoverFinal
        pos (layers + 2) h msg) = some sigs ↔
      ∃ (sig : XmssSig vp.params core) (root : core.Y)
        (rest : Vector (XmssSig vp.params core) (layers + 1)),
        simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
          (PublicHash.tl core pk) (PublicHash.h core pk) secret msg pos.toAdrs pos.leaf.val) =
            some sig ∧
        simulateQ c.toPartialImpl
          (xmssPkFromSigM core pos.leaf.val sig msg pk pos.toAdrs) = some root ∧
        simulateQ c.toPartialImpl (GeneralHypertree.signFromPositionWithSecret core
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) secret false
          (pos.next (by omega)) (layers + 1) (by simp [LayerPosition.next]; omega) root) =
            some rest ∧
        rest.insertIdx 0 sig = sigs := by
  simp only [GeneralHypertree.signFromPositionWithSecret,
    xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff, exists_and_left]

/-- Algorithm 12 over a provider at its last layer without final recovery is settled exactly when
the XMSS signature at that position is settled. -/
theorem simulateQ_toPartialImpl_signFromPositionWithSecret_one_false_eq_some_iff
    (pk : core.PkSeed) (pos : LayerPosition vp) (h : pos.layer.val + 1 = vp.params.d)
    (msg : core.Y) {sigs : Vector (XmssSig vp.params core) 1} :
    simulateQ c.toPartialImpl (GeneralHypertree.signFromPositionWithSecret core
        (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) secret false
        pos 1 h msg) = some sigs ↔
      ∃ sig : XmssSig vp.params core,
        simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
          (PublicHash.tl core pk) (PublicHash.h core pk) secret msg pos.toAdrs pos.leaf.val) =
            some sig ∧
        #v[sig] = sigs := by
  simp only [GeneralHypertree.signFromPositionWithSecret, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff, Bool.false_eq_true, ↓reduceIte]

/-- Algorithm 19 over a provider, with the randomizer `R` supplied, is settled exactly when its
`H_msg` query is cached at some digest, the FORS signature over the provider at that digest is
settled, the FORS public key recovered from it is settled, and the hypertree signature over the
provider on that key is settled; the result is assembled from these. -/
theorem simulateQ_toPartialImpl_signInternalWithSecretRandomizerM_eq_some_iff (msg : List Byte)
    (pkSeed : core.PkSeed) (pkRoot R : core.Y) {σ : GeneralScheme.SignatureCore vp core} :
    simulateQ c.toPartialImpl (GeneralScheme.signInternalWithSecretRandomizerM core secret msg
        pkSeed pkRoot R) = some σ ↔
      ∃ (digest : Bytes vp.params.m) (forsSig : ForsSigCore vp.params core) (forsPk : core.Y)
        (htSig : GeneralHypertree.Signature vp core),
        c (.hmsg R pkSeed pkRoot msg) = some digest ∧
        simulateQ c.toPartialImpl (forsSignWithSecretM core secret
          (splitDigest vp.params digest).md.toList pkSeed
          (splitDigest vp.params digest).forsAdrs) = some forsSig ∧
        simulateQ c.toPartialImpl (forsPkFromSigM core forsSig
          (splitDigest vp.params digest).md.toList pkSeed
          (splitDigest vp.params digest).forsAdrs) = some forsPk ∧
        simulateQ c.toPartialImpl (GeneralHypertree.signWithSecretM core secret forsPk pkSeed
          (splitDigest vp.params digest)) = some htSig ∧
        (⟨R, forsSig, htSig⟩ : GeneralScheme.SignatureCore vp core) = σ := by
  simp only [GeneralScheme.signInternalWithSecretRandomizerM, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff, simulateQ_toPartialImpl_hmsg, exists_and_left]

/-- A settled run of Algorithm 19 over a provider at a supplied randomizer carries that
randomizer, and its `H_msg` entry, FORS signature, recovered FORS public key and hypertree
signature are settled, in the shape a top-down reading of the signature uses. -/
theorem components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM
    (msg : List Byte) (pkSeed : core.PkSeed) (pkRoot R : core.Y)
    {σ : GeneralScheme.SignatureCore vp core}
    (h : simulateQ c.toPartialImpl (GeneralScheme.signInternalWithSecretRandomizerM core secret msg
      pkSeed pkRoot R) = some σ) :
    σ.randomness = R ∧
    ∃ (digest : Bytes vp.params.m) (forsPk : core.Y),
      c (.hmsg σ.randomness pkSeed pkRoot msg) = some digest ∧
      simulateQ c.toPartialImpl (forsSignWithSecretM core secret
        (splitDigest vp.params digest).md.toList pkSeed
        (splitDigest vp.params digest).forsAdrs) = some σ.fors ∧
      simulateQ c.toPartialImpl (forsPkFromSigM core σ.fors
        (splitDigest vp.params digest).md.toList pkSeed
        (splitDigest vp.params digest).forsAdrs) = some forsPk ∧
      simulateQ c.toPartialImpl (GeneralHypertree.signWithSecretM core secret forsPk pkSeed
        (splitDigest vp.params digest)) = some σ.hypertree := by
  obtain ⟨digest, forsSig, forsPk, htSig, hd, hfs, hfp, hht, rfl⟩ :=
    (simulateQ_toPartialImpl_signInternalWithSecretRandomizerM_eq_some_iff core c secret msg
      pkSeed pkRoot R).mp h
  exact ⟨rfl, digest, forsPk, hd, hfs, hfp, hht⟩

end Hypertree

/-! ## The oracle-backed provider -/

section Oracle

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) (c : PublicHash.Cache core)

/-- An oracle-backed secret under a cache is the cache entry of the `F` query of the secret seed,
read as a node, at the draw's `PRF` address. -/
@[simp]
theorem simulateQ_toPartialImpl_oracleSecret (e : core.SkSeed ≃ core.Y) (pk : core.PkSeed)
    (sk : core.SkSeed) (a : Adrs) :
    simulateQ c.toPartialImpl
        (oracleSecret core e (m := OracleComp (publicHashSpec core)) pk sk a) =
      c (.thash pk (core.adrsToKey a) [e sk]) := by
  rw [oracleSecret, simulateQ_toPartialImpl_f]

/-- A query-preserving monad morphism fixes every oracle-backed secret draw. -/
theorem oracleSecret_natural {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n) (e : core.SkSeed ≃ core.Y)
    (pk : core.PkSeed) (sk : core.SkSeed) (a : Adrs) :
    F.toMonadHom (oracleSecret core e (m := m) pk sk a) = oracleSecret core e (m := n) pk sk a :=
  PublicHash.f_natural core F pk a (e sk)

/-- Key generation at the oracle-backed provider, in any monad reaching the public hash, is the
image of the same program in `OracleComp (publicHashSpec core)` under the canonical interpretation
of its queries. -/
theorem keygenInternalWithSecretM_oracleSecret_eq_ofSimulateQ {m : Type → Type*} [Monad m]
    [LawfulMonad m] [HasQuery (publicHashSpec core) m] (e : core.SkSeed ≃ core.Y)
    (pk : core.PkSeed) (sk : core.SkSeed) :
    (GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pk sk) pk : m core.Y) =
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core) (m := m)).toMonadHom
        (GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pk sk) pk) :=
  (GeneralScheme.keygenInternalWithSecretM_natural core _ _ _
    (fun a _ => oracleSecret_natural core _ e pk sk a) pk).symm

/-- Signing at the oracle-backed provider and a supplied randomizer, in any monad reaching the
public hash, is the image of the same program in `OracleComp (publicHashSpec core)` under the
canonical interpretation of its queries. -/
theorem signInternalWithSecretRandomizerM_oracleSecret_eq_ofSimulateQ {m : Type → Type*}
    [Monad m] [LawfulMonad m] [HasQuery (publicHashSpec core) m] (e : core.SkSeed ≃ core.Y)
    (pk : core.PkSeed) (sk : core.SkSeed) (msg : List Byte) (pkRoot R : core.Y) :
    (GeneralScheme.signInternalWithSecretRandomizerM core (oracleSecret core e pk sk) msg pk
        pkRoot R : m (GeneralScheme.SignatureCore vp core)) =
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core) (m := m)).toMonadHom
        (GeneralScheme.signInternalWithSecretRandomizerM core (oracleSecret core e pk sk) msg pk
          pkRoot R) :=
  (GeneralScheme.signInternalWithSecretRandomizerM_natural core _ _ _
    (fun a _ => oracleSecret_natural core _ e pk sk a) msg pk pkRoot R).symm

end Oracle

end SLHDSA.Security
