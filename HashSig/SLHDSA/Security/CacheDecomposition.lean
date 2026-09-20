/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.GeneralScheme
public import HashSig.SLHDSA.Security.CacheReaders
public import VCVio.OracleComp.SimSemantics.SimulateQ.Option

/-!
# SLH-DSA programs under a public-hash cache, one query at a time

Under the partial oracle `QueryCache.toPartialImpl` a hash-only program reads to `some v`
exactly when every stage of it does, at the values it passes on
(`OracleComp.simulateQ_bind_eq_some_iff` and its siblings).  This module applies that
characterisation to the SLH-DSA programs, from FIPS 205 Algorithms 18--20 down to a single
WOTS+ chain step, so that a settled reading of key generation, signing or verification can be
followed down to the individual `T_l`, `F`, `H` and `H_msg` cache entries it rests on.

Each `simulateQ_toPartialImpl_*_eq_some_iff` lemma is an equivalence between a settled reading of
one program and settled readings of its immediate sub-programs.  The scheme layer decomposes
Algorithms 18--20; the hypertree layer peels one XMSS layer off Algorithms 12 and 13; the FORS
layer reduces Algorithms 14--16 to per-tree Merkle roots, authentication paths and climbs; the
WOTS+ layer reduces chain tops to chains and a chain to its `F` queries; the XMSS layer splits
Algorithms 10 and 11 into authentication path, WOTS+ signature and climb.  The `chain?` lemmas
compose and split chains (`chain?_add_eq_some_iff`), settle every prefix of a settled chain
(`exists_chain?_eq_some_of_le`) and locate every intermediate `F` entry
(`chain?_query_settled`); `simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_of_wotsSignM` is the
composition of a signer's chain prefixes with a verifier's chain suffixes.

## Scope

* No property of any particular cache is proved here; which entries a run of the counted
  random-oracle experiment settles belongs to `HashSig.SLHDSA.Security.RomTranscript`.
* The Merkle climbs and roots that the FORS and XMSS layers bottom out in are decomposed in
  `VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option`, not here.
* Nothing here is probabilistic, and nothing here is quantum: the cache is a classical table.

## Labels

Twenty-five declarations.

*Algorithms 18--20*: `simulateQ_toPartialImpl_keygenInternalM_eq_some_iff`,
`simulateQ_toPartialImpl_signInternalM_eq_some_iff`,
`components_of_simulateQ_toPartialImpl_signInternalM`,
`simulateQ_toPartialImpl_verifyInternalM_eq_some_true_iff`.

*Hypertree layers*: `simulateQ_toPartialImpl_recoverFromPositionM_add_two_eq_some_iff`,
`simulateQ_toPartialImpl_recoverFromPositionM_one_eq_some_iff`,
`simulateQ_toPartialImpl_pkFromSigM_eq`,
`simulateQ_toPartialImpl_signFromPositionM_add_two_eq_some_iff`,
`simulateQ_toPartialImpl_signFromPositionM_one_false_eq_some_iff`.

*FORS trees*: `simulateQ_toPartialImpl_forsPkGenM_eq_some_iff`,
`simulateQ_toPartialImpl_forsSignM_eq_some_iff`,
`simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff`.

*WOTS+ chains*: `simulateQ_toPartialImpl_chainM_succ_eq_some_iff`,
`simulateQ_toPartialImpl_chainM_add_eq_some_iff`,
`simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_iff`,
`simulateQ_toPartialImpl_wotsSignM_eq_some_iff`,
`simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff`,
`simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_of_wotsSignM`.

*XMSS trees*: `simulateQ_toPartialImpl_xmssSignM_eq_some_iff`,
`simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff`.

*Chain reader*: `chain?_zero`, `chain?_succ_eq_some_iff`, `chain?_add_eq_some_iff`,
`exists_chain?_eq_some_of_le`, `chain?_query_settled`.

## References

- NIST FIPS 205, §6--§9, Algorithms 5--20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

/-! ## WOTS+ chains -/

section Components

variable {p : Params} (core : CorePrimitives p) (c : PublicHash.Cache core)

/-- One more chain step is settled exactly when the chain so far is settled and the `F` query at
hash address `i + s` of its value is cached. -/
theorem simulateQ_toPartialImpl_chainM_succ_eq_some_iff (pk : core.PkSeed) (adrs : Adrs)
    (x : core.Y) (i s : ℕ) {y : core.Y} :
    simulateQ c.toPartialImpl (chainM core pk adrs x i (s + 1)) = some y ↔
      ∃ z, simulateQ c.toPartialImpl (chainM core pk adrs x i s) = some z ∧
        c (.thash pk (core.adrsToKey (adrs.setHashAddress (i + s))) [z]) = some y := by
  simp only [chainM, chainWith, simulateQ_bind_eq_some_iff, simulateQ_toPartialImpl_f]

/-- An `a + b`-step chain is settled exactly when its first `a` steps are settled and the
`b`-step chain from their value at hash address `i + a` is settled. -/
theorem simulateQ_toPartialImpl_chainM_add_eq_some_iff (pk : core.PkSeed) (adrs : Adrs)
    (x : core.Y) (i a b : ℕ) {y : core.Y} :
    simulateQ c.toPartialImpl (chainM core pk adrs x i (a + b)) = some y ↔
      ∃ z, simulateQ c.toPartialImpl (chainM core pk adrs x i a) = some z ∧
        simulateQ c.toPartialImpl (chainM core pk adrs z (i + a) b) = some y := by
  induction b generalizing y with
  | zero => simp [chainM, chainWith]
  | succ b ih =>
    rw [← Nat.add_assoc]
    simp only [simulateQ_toPartialImpl_chainM_succ_eq_some_iff, ih]
    rw [← Nat.add_assoc i a b]
    exact ⟨fun ⟨w, ⟨z, hz, hw⟩, hq⟩ => ⟨z, hz, w, hw, hq⟩,
      fun ⟨z, hz, w, hw, hq⟩ => ⟨w, ⟨z, hz, hw⟩, hq⟩⟩

/-- The honest chain tops are settled exactly when every full chain from its secret value is
settled, at the corresponding top. -/
theorem simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_iff (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) {tops : Vector core.Y p.len} :
    simulateQ c.toPartialImpl (wotsPkGenTopsM core sk pk adrs) = some tops ↔
      ∀ i : Fin p.len, simulateQ c.toPartialImpl (chainM core pk (wotsChainAdrs adrs i.val)
        (core.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1)) = some tops[i] := by
  simp only [wotsPkGenTopsM, wotsPkGenTopsWith, simulateQ_ofFnM_eq_some_iff, chainM]

/-- A WOTS+ signature is settled exactly when every message-selected chain prefix from its
secret value is settled, at the corresponding signature entry. -/
theorem simulateQ_toPartialImpl_wotsSignM_eq_some_iff (msg : core.Y) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) {sig : WotsSig p core} :
    simulateQ c.toPartialImpl (wotsSignM core msg sk pk adrs) = some sig ↔
      ∀ i : Fin p.len, simulateQ c.toPartialImpl (chainM core pk (wotsChainAdrs adrs i.val)
        (core.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainStepsCore core msg i.val)) =
          some sig[i] := by
  simp only [wotsSignM, wotsSignWith, simulateQ_ofFnM_eq_some_iff, chainM]

/-- The chain tops recovered from a WOTS+ signature are settled exactly when every chain suffix
from the signature entry is settled, at the corresponding top. -/
theorem simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff (sig : WotsSig p core)
    (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) {tops : Vector core.Y p.len} :
    simulateQ c.toPartialImpl (wotsPkFromSigTopsM core sig msg pk adrs) = some tops ↔
      ∀ i : Fin p.len, simulateQ c.toPartialImpl (chainM core pk (wotsChainAdrs adrs i.val)
        sig[i.val] (chainStepsCore core msg i.val) (p.w - 1 - chainStepsCore core msg i.val)) =
          some tops[i] := by
  simp only [wotsPkFromSigTopsM, wotsPkFromSigTopsWith, simulateQ_ofFnM_eq_some_iff, chainM]

/-- A settled WOTS+ signature whose recovered chain tops are settled settles the honest chain
tops, at the recovered tops: the signer's chain prefixes compose with the verifier's chain
suffixes. -/
theorem simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_of_wotsSignM (msg : core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) {sig : WotsSig p core}
    {tops : Vector core.Y p.len}
    (hsign : simulateQ c.toPartialImpl (wotsSignM core msg sk pk adrs) = some sig)
    (hrec : simulateQ c.toPartialImpl (wotsPkFromSigTopsM core sig msg pk adrs) = some tops) :
    simulateQ c.toPartialImpl (wotsPkGenTopsM core sk pk adrs) = some tops := by
  rw [simulateQ_toPartialImpl_wotsSignM_eq_some_iff] at hsign
  rw [simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff] at hrec
  rw [simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_iff]
  intro i
  rw [← Nat.add_sub_cancel' (chainStepsCore_le core msg i.val),
    simulateQ_toPartialImpl_chainM_add_eq_some_iff]
  exact ⟨sig[i], hsign i, by rw [Nat.zero_add]; exact hrec i⟩

/-! ## XMSS trees -/

/-- An XMSS signature is settled exactly when the authentication path of its leaf is settled, at
the path it carries, and the WOTS+ signature at its leaf is settled, at the one it carries. -/
theorem simulateQ_toPartialImpl_xmssSignM_eq_some_iff (msg : core.Y) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) {sig : XmssSig p core} :
    simulateQ c.toPartialImpl (xmssSignM core msg sk pk adrs idx) = some sig ↔
      simulateQ c.toPartialImpl (PerfectMerkleTree.intrinsicAuthPathM (xmssLeafM core sk pk adrs)
        (xmssNodeHashM core pk adrs) idx p.hp) = some sig.auth ∧
      simulateQ c.toPartialImpl (wotsSignM core msg sk pk (wotsLeafAdrs adrs idx)) =
        some sig.wots := by
  rw [xmssSignM_eq_bind]
  simp only [simulateQ_bind_eq_some_iff, simulateQ_pure_eq_some_iff]
  exact ⟨fun ⟨_, hpath, _, hs, rfl⟩ => ⟨hpath, hs⟩, fun ⟨hpath, hs⟩ => ⟨_, hpath, _, hs, rfl⟩⟩

/-- XMSS recovery is settled exactly when the recovered chain tops are settled, their `T_len`
compression is cached, and the climb from that leaf along the authentication path is
settled. -/
theorem simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff (idx : ℕ) (sig : XmssSig p core)
    (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) {root : core.Y} :
    simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs) = some root ↔
      ∃ leaf : core.Y,
        (∃ tops : Vector core.Y p.len,
          simulateQ c.toPartialImpl
            (wotsPkFromSigTopsM core sig.wots msg pk (wotsLeafAdrs adrs idx)) = some tops ∧
          c (.thash pk (core.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs idx))) tops.toList) =
            some leaf) ∧
        simulateQ c.toPartialImpl (PerfectMerkleTree.climbM
          (xmssNodeHashM core pk adrs) idx leaf sig.auth.toList) = some root := by
  rw [xmssPkFromSigM_eq_bind]
  simp only [wotsPkFromSigM, wotsPkFromSigWith, wotsPkFromSigTopsM, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_tl]

/-! ## Chain reader -/

/-- A zero-step chain reads to its input. -/
@[simp]
theorem chain?_zero (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) (i : ℕ) :
    chain? core c pk adrs x i 0 = some x := rfl

/-- One more chain step is settled exactly when the chain so far is settled and the `F` query at
hash address `i + s` of its value is cached. -/
theorem chain?_succ_eq_some_iff (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) (i s : ℕ)
    {y : core.Y} :
    chain? core c pk adrs x i (s + 1) = some y ↔
      ∃ z, chain? core c pk adrs x i s = some z ∧
        c (.thash pk (core.adrsToKey (adrs.setHashAddress (i + s))) [z]) = some y :=
  simulateQ_toPartialImpl_chainM_succ_eq_some_iff core c pk adrs x i s

/-- An `a + b`-step chain is settled exactly when its first `a` steps are settled and the
`b`-step chain from their value at hash address `i + a` is settled. -/
theorem chain?_add_eq_some_iff (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) (i a b : ℕ)
    {y : core.Y} :
    chain? core c pk adrs x i (a + b) = some y ↔
      ∃ z, chain? core c pk adrs x i a = some z ∧ chain? core c pk adrs z (i + a) b = some y :=
  simulateQ_toPartialImpl_chainM_add_eq_some_iff core c pk adrs x i a b

/-- A settled chain settles every shorter chain from the same input. -/
theorem exists_chain?_eq_some_of_le (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) (i : ℕ)
    {s t : ℕ} (hts : t ≤ s) {y : core.Y} (h : chain? core c pk adrs x i s = some y) :
    ∃ z, chain? core c pk adrs x i t = some z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hts
  exact ((chain?_add_eq_some_iff core c pk adrs x i t k).mp h).imp fun z hz => hz.1

/-- Every intermediate `F` query of a settled `s`-step chain is cached: for `t < s`, the
`t`-step chain is settled at some `z` and the `F` entry at hash address `i + t` of `z` is
cached. -/
theorem chain?_query_settled (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) (i : ℕ) {s t : ℕ}
    (hts : t < s) {y : core.Y} (h : chain? core c pk adrs x i s = some y) :
    ∃ z w, chain? core c pk adrs x i t = some z ∧
      c (.thash pk (core.adrsToKey (adrs.setHashAddress (i + t))) [z]) = some w := by
  obtain ⟨w, hw⟩ := exists_chain?_eq_some_of_le core c pk adrs x i hts h
  exact ((chain?_succ_eq_some_iff core c pk adrs x i t).mp hw).imp fun z hz => ⟨w, hz⟩

/-! ## FORS trees -/

/-- The honest FORS public key is settled exactly when every tree root is settled and the `T_k`
compression of the roots is cached. -/
theorem simulateQ_toPartialImpl_forsPkGenM_eq_some_iff (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) {fpk : core.Y} :
    simulateQ c.toPartialImpl (forsPkGenM core sk pk adrs) = some fpk ↔
      ∃ roots : Vector core.Y p.k,
        (∀ i : Fin p.k, simulateQ c.toPartialImpl (PerfectMerkleTree.merkleRootM
          (forsLeafWith core (PublicHash.f core pk) sk pk adrs)
          (forsNodeHashWith (PublicHash.h core pk) adrs) p.a i.val) = some roots[i]) ∧
        c (.thash pk (core.adrsToKey (forsPkAdrs adrs)) roots.toList) = some fpk := by
  simp only [forsPkGenM, forsPkGenWith, forsRootWith, simulateQ_bind_eq_some_iff,
    simulateQ_ofFnM_eq_some_iff, simulateQ_toPartialImpl_tl]

/-- A FORS signature is settled exactly when every tree's sibling-only authentication path is
settled, at the path the signature carries beside the selected secret value. -/
theorem simulateQ_toPartialImpl_forsSignM_eq_some_iff (md : List Byte) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) {sig : ForsSigCore p core} :
    simulateQ c.toPartialImpl (forsSignM core md sk pk adrs) = some sig ↔
      ∀ i : Fin p.k, ∃ path : Vector core.Y p.a,
        simulateQ c.toPartialImpl (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWith core (PublicHash.f core pk) sk pk adrs)
          (forsNodeHashWith (PublicHash.h core pk) adrs)
          (i.val * 2 ^ p.a + forsIdx p md i.val) p.a) = some path ∧
        (⟨forsSkGenCore core sk pk adrs (i.val * 2 ^ p.a + forsIdx p md i.val), path⟩ :
          ForsTreeSigCore p core) = sig[i] := by
  simp only [forsSignM, forsSignWith, simulateQ_ofFnM_eq_some_iff, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff]

/-- FORS recovery is settled exactly when, for every tree, the `F` query of the revealed secret
is cached and the climb from it is settled at the recovered root, and the `T_k` compression of
the recovered roots is cached. -/
theorem simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff (sig : ForsSigCore p core)
    (md : List Byte) (pk : core.PkSeed) (adrs : Adrs) {fpk : core.Y} :
    simulateQ c.toPartialImpl (forsPkFromSigM core sig md pk adrs) = some fpk ↔
      ∃ roots : Vector core.Y p.k,
        (∀ i : Fin p.k, ∃ leaf : core.Y,
          c (.thash pk (core.adrsToKey (forsNodeAdrs adrs 0
            (i.val * 2 ^ p.a + forsIdx p md i.val))) [(sig[i.val]).sk]) = some leaf ∧
          simulateQ c.toPartialImpl (PerfectMerkleTree.climbM
            (forsNodeHashWith (PublicHash.h core pk) adrs) (i.val * 2 ^ p.a + forsIdx p md i.val)
            leaf (sig[i.val]).auth.toList) = some roots[i]) ∧
        c (.thash pk (core.adrsToKey (forsPkAdrs adrs)) roots.toList) = some fpk := by
  simp only [forsPkFromSigM, forsPkFromSigWith, simulateQ_bind_eq_some_iff,
    simulateQ_ofFnM_eq_some_iff, simulateQ_toPartialImpl_f, simulateQ_toPartialImpl_tl]

end Components

/-! ## Hypertree layers -/

section Hypertree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) (c : PublicHash.Cache core)

/-- Algorithm 13 with two or more layers left is settled exactly when the head XMSS signature
recovers a settled root and the remaining layers, recovering from that root at the next position,
are settled. -/
theorem simulateQ_toPartialImpl_recoverFromPositionM_add_two_eq_some_iff (pk : core.PkSeed)
    (pos : LayerPosition vp) (layers : ℕ) (h : pos.layer.val + (layers + 2) = vp.params.d)
    (msg : core.Y) (sigs : Vector (XmssSig vp.params core) (layers + 2)) {root : core.Y} :
    simulateQ c.toPartialImpl
        (GeneralHypertree.recoverFromPositionM vp core pk pos (layers + 2) h msg sigs) =
          some root ↔
      ∃ r, simulateQ c.toPartialImpl
          (xmssPkFromSigM core pos.leaf.val sigs.head msg pk pos.toAdrs) = some r ∧
        simulateQ c.toPartialImpl (GeneralHypertree.recoverFromPositionM vp core pk
          (pos.next (by omega)) (layers + 1) (by simp [LayerPosition.next]; omega) r sigs.tail) =
            some root :=
  simulateQ_bind_eq_some_iff _ _ _

/-- Algorithm 13 at its last layer is the XMSS recovery at that position. -/
theorem simulateQ_toPartialImpl_recoverFromPositionM_one_eq_some_iff (pk : core.PkSeed)
    (pos : LayerPosition vp) (h : pos.layer.val + 1 = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) 1) {root : core.Y} :
    simulateQ c.toPartialImpl
        (GeneralHypertree.recoverFromPositionM vp core pk pos 1 h msg sigs) = some root ↔
      simulateQ c.toPartialImpl
        (xmssPkFromSigM core pos.leaf.val sigs.head msg pk pos.toAdrs) = some root :=
  Iff.rfl

/-- Hypertree recovery is Algorithm 13's loop from the digest's layer-zero position over all
`d` layers. -/
theorem simulateQ_toPartialImpl_pkFromSigM_eq (msg : core.Y)
    (sig : GeneralHypertree.Signature vp core) (pk : core.PkSeed) (parts : DigestParts vp.params) :
    simulateQ c.toPartialImpl (GeneralHypertree.pkFromSigM vp core msg sig pk parts) =
      simulateQ c.toPartialImpl (GeneralHypertree.recoverFromPositionM vp core pk
        (LayerPosition.initial vp parts) vp.params.d (by simp [LayerPosition.initial]) msg sig) :=
  rfl

/-- Algorithm 12 with two or more layers left is settled exactly when the XMSS signature at this
position is settled, the root it recovers is settled, and the remaining layers signed from that
root are settled; the result is the remaining signatures with this one in front. -/
theorem simulateQ_toPartialImpl_signFromPositionM_add_two_eq_some_iff (sk : core.SkSeed)
    (pk : core.PkSeed) (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (h : pos.layer.val + (layers + 2) = vp.params.d) (msg : core.Y)
    {sigs : Vector (XmssSig vp.params core) (layers + 2)} :
    simulateQ c.toPartialImpl
        (GeneralHypertree.signFromPositionM vp core sk pk recoverFinal pos (layers + 2) h msg) =
          some sigs ↔
      ∃ (sig : XmssSig vp.params core) (root : core.Y)
        (rest : Vector (XmssSig vp.params core) (layers + 1)),
        simulateQ c.toPartialImpl (xmssSignM core msg sk pk pos.toAdrs pos.leaf.val) = some sig ∧
        simulateQ c.toPartialImpl
          (xmssPkFromSigM core pos.leaf.val sig msg pk pos.toAdrs) = some root ∧
        simulateQ c.toPartialImpl (GeneralHypertree.signFromPositionM vp core sk pk false
          (pos.next (by omega)) (layers + 1) (by simp [LayerPosition.next]; omega) root) =
            some rest ∧
        rest.insertIdx 0 sig = sigs := by
  simp only [GeneralHypertree.signFromPositionM, GeneralHypertree.signFromPositionWith,
    xmssSignWith_publicHash_eq_xmssSignM, xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM,
    simulateQ_bind_eq_some_iff, simulateQ_pure_eq_some_iff, exists_and_left]

/-- Algorithm 12 at its last layer without final recovery is settled exactly when the XMSS
signature at that position is settled. -/
theorem simulateQ_toPartialImpl_signFromPositionM_one_false_eq_some_iff (sk : core.SkSeed)
    (pk : core.PkSeed) (pos : LayerPosition vp) (h : pos.layer.val + 1 = vp.params.d)
    (msg : core.Y) {sigs : Vector (XmssSig vp.params core) 1} :
    simulateQ c.toPartialImpl
        (GeneralHypertree.signFromPositionM vp core sk pk false pos 1 h msg) = some sigs ↔
      ∃ sig : XmssSig vp.params core,
        simulateQ c.toPartialImpl (xmssSignM core msg sk pk pos.toAdrs pos.leaf.val) = some sig ∧
        #v[sig] = sigs := by
  simp only [GeneralHypertree.signFromPositionM, GeneralHypertree.signFromPositionWith,
    xmssSignWith_publicHash_eq_xmssSignM, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff, Bool.false_eq_true, ↓reduceIte]

/-! ## Algorithms 18--20 -/

/-- Algorithm 18 is settled exactly when the top tree root is settled, and the key pair is built
from it. -/
theorem simulateQ_toPartialImpl_keygenInternalM_eq_some_iff (skSeed : core.SkSeed)
    (skPrf : core.SkPrf) (pkSeed : core.PkSeed) {pk : PublicKeyCore core}
    {sk : SecretKeyCore core} :
    simulateQ c.toPartialImpl
        (GeneralScheme.keygenInternalM (m := OracleComp (publicHashSpec core)) vp core skSeed
          skPrf pkSeed) = some (pk, sk) ↔
      ∃ pkRoot : core.Y,
        simulateQ c.toPartialImpl (GeneralHypertree.rootM vp core skSeed pkSeed) = some pkRoot ∧
        (⟨pkSeed, pkRoot⟩ : PublicKeyCore core) = pk ∧
        (⟨skSeed, skPrf, pkSeed, pkRoot⟩ : SecretKeyCore core) = sk := by
  simp only [GeneralScheme.keygenInternalM, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff, Prod.mk.injEq]

/-- Algorithm 19 is settled exactly when its `H_msg` query is cached at some digest, the FORS
signature at that digest is settled, the FORS public key recovered from it is settled, and the
hypertree signature over that key is settled; the result is assembled from these. -/
theorem simulateQ_toPartialImpl_signInternalM_eq_some_iff (msg : List Byte)
    (sk : SecretKeyCore core) (addrnd : core.Y) {σ : GeneralScheme.SignatureCore vp core} :
    simulateQ c.toPartialImpl
        (GeneralScheme.signInternalM (m := OracleComp (publicHashSpec core)) vp core msg sk
          addrnd) = some σ ↔
      ∃ (digest : Bytes vp.params.m) (forsSig : ForsSigCore vp.params core) (forsPk : core.Y)
        (htSig : GeneralHypertree.Signature vp core),
        c (.hmsg (core.PRFmsg sk.skPrf addrnd msg) sk.pkSeed sk.pkRoot msg) = some digest ∧
        simulateQ c.toPartialImpl (forsSignM core (splitDigest vp.params digest).md.toList
          sk.skSeed sk.pkSeed (splitDigest vp.params digest).forsAdrs) = some forsSig ∧
        simulateQ c.toPartialImpl (forsPkFromSigM core forsSig
          (splitDigest vp.params digest).md.toList sk.pkSeed
          (splitDigest vp.params digest).forsAdrs) = some forsPk ∧
        simulateQ c.toPartialImpl (GeneralHypertree.signM vp core forsPk sk.skSeed sk.pkSeed
          (splitDigest vp.params digest)) = some htSig ∧
        (⟨core.PRFmsg sk.skPrf addrnd msg, forsSig, htSig⟩ :
          GeneralScheme.SignatureCore vp core) = σ := by
  simp only [GeneralScheme.signInternalM, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff, simulateQ_toPartialImpl_hmsg, exists_and_left]

/-- A settled Algorithm 19 run carries the derived randomizer, and its `H_msg` entry, FORS
signature, recovered FORS public key and hypertree signature are settled, in the shape a
top-down reading of the signature uses. -/
theorem components_of_simulateQ_toPartialImpl_signInternalM (msg : List Byte)
    (sk : SecretKeyCore core) (addrnd : core.Y) {σ : GeneralScheme.SignatureCore vp core}
    (h : simulateQ c.toPartialImpl
      (GeneralScheme.signInternalM (m := OracleComp (publicHashSpec core)) vp core msg sk
        addrnd) = some σ) :
    σ.randomness = core.PRFmsg sk.skPrf addrnd msg ∧
    ∃ (digest : Bytes vp.params.m) (forsPk : core.Y),
      c (.hmsg σ.randomness sk.pkSeed sk.pkRoot msg) = some digest ∧
      simulateQ c.toPartialImpl (forsSignM core (splitDigest vp.params digest).md.toList
        sk.skSeed sk.pkSeed (splitDigest vp.params digest).forsAdrs) = some σ.fors ∧
      simulateQ c.toPartialImpl (forsPkFromSigM core σ.fors
        (splitDigest vp.params digest).md.toList sk.pkSeed
        (splitDigest vp.params digest).forsAdrs) = some forsPk ∧
      simulateQ c.toPartialImpl (GeneralHypertree.signM vp core forsPk sk.skSeed sk.pkSeed
        (splitDigest vp.params digest)) = some σ.hypertree := by
  obtain ⟨digest, forsSig, forsPk, htSig, hd, hfs, hfp, hht, rfl⟩ :=
    (simulateQ_toPartialImpl_signInternalM_eq_some_iff core c msg sk addrnd).mp h
  exact ⟨rfl, digest, forsPk, hd, hfs, hfp, hht⟩

/-- Algorithm 20 is settled at `true` exactly when its `H_msg` query is cached at some digest,
the FORS public key recovered from the signature at that digest is settled, and the hypertree
recovery from that key is settled at the public root. -/
theorem simulateQ_toPartialImpl_verifyInternalM_eq_some_true_iff [DecidableEq core.Y]
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    simulateQ c.toPartialImpl
        (GeneralScheme.verifyInternalM (m := OracleComp (publicHashSpec core)) vp core msg sig
          pk) = some true ↔
      ∃ (digest : Bytes vp.params.m) (forsPk : core.Y),
        c (.hmsg sig.randomness pk.pkSeed pk.pkRoot msg) = some digest ∧
        simulateQ c.toPartialImpl (forsPkFromSigM core sig.fors
          (splitDigest vp.params digest).md.toList pk.pkSeed
          (splitDigest vp.params digest).forsAdrs) = some forsPk ∧
        simulateQ c.toPartialImpl (GeneralHypertree.pkFromSigM vp core forsPk sig.hypertree
          pk.pkSeed (splitDigest vp.params digest)) = some pk.pkRoot := by
  simp only [GeneralScheme.verifyInternalM, GeneralHypertree.verifyM, simulateQ_bind_eq_some_iff,
    simulateQ_pure_eq_some_iff, simulateQ_toPartialImpl_hmsg, decide_eq_true_eq,
    exists_eq_right, exists_and_left]

end Hypertree

end SLHDSA.Security
