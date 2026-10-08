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
characterisation to the SLH-DSA programs, from FIPS 205's verification (Algorithm 20) down to a
single WOTS+ chain step, so that a settled reading can be followed down to the individual `T_l`,
`F`, `H` and `H_msg` cache entries it rests on.

Each `simulateQ_toPartialImpl_*_eq_some_iff` lemma is an equivalence between a settled reading of
one program and settled readings of its immediate sub-programs.  The scheme layer decomposes
Algorithm 20; the hypertree layer peels one XMSS layer off Algorithm 13; the FORS layer reduces
the FORS public key and its recovery to per-tree Merkle roots and climbs; the WOTS+ layer reduces
chain tops to chains and a chain to its `F` queries; the XMSS layer splits the recovery of
Algorithm 11 into WOTS+ recovery and climb.  The `chain?` lemmas compose and split chains
(`chain?_add_eq_some_iff`) and, for two settled chains of equal length that end at the same value,
find the first step at which they split into two cached `F` entries with one answer
(`chain?_diverge`).

## Scope

* No property of any particular cache is proved here.
* The programs that draw a secret are decomposed over a secret provider in
  `HashSig.SLHDSA.Security.CacheSecret`.
* The Merkle climbs and roots that the FORS and XMSS layers bottom out in are decomposed in
  `VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option`, not here.
* Nothing here is probabilistic, and nothing here is quantum: the cache is a classical table.

## Labels

Sixteen declarations.

*Algorithm 20*: `simulateQ_toPartialImpl_verifyInternalM_eq_some_true_iff`,
`exists_of_simulateQ_toPartialImpl_verifyInternalM_eq_some`.

*Hypertree layers*: `simulateQ_toPartialImpl_recoverFromPositionM_add_two_eq_some_iff`,
`simulateQ_toPartialImpl_recoverFromPositionM_one_eq_some_iff`,
`simulateQ_toPartialImpl_pkFromSigM_eq`.

*FORS trees*: `simulateQ_toPartialImpl_forsPkGenM_eq_some_iff`,
`simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff`.

*WOTS+ chains*: `simulateQ_toPartialImpl_chainM_succ_eq_some_iff`,
`simulateQ_toPartialImpl_chainM_add_eq_some_iff`,
`simulateQ_toPartialImpl_wotsPkGenTopsM_eq_some_iff`,
`simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff`.

*XMSS trees*: `simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff`.

*Chain reader*: `chain?_zero`, `chain?_succ_eq_some_iff`, `chain?_add_eq_some_iff`,
`chain?_diverge`.

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

/-- The chain tops recovered from a WOTS+ signature are settled exactly when every chain suffix
from the signature entry is settled, at the corresponding top. -/
theorem simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff (sig : WotsSig p core)
    (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) {tops : Vector core.Y p.len} :
    simulateQ c.toPartialImpl (wotsPkFromSigTopsM core sig msg pk adrs) = some tops ↔
      ∀ i : Fin p.len, simulateQ c.toPartialImpl (chainM core pk (wotsChainAdrs adrs i.val)
        sig[i.val] (chainStepsCore core msg i.val) (p.w - 1 - chainStepsCore core msg i.val)) =
          some tops[i] := by
  simp only [wotsPkFromSigTopsM, wotsPkFromSigTopsWith, simulateQ_ofFnM_eq_some_iff, chainM]

/-! ## XMSS trees -/

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

/-- Two settled `n`-step chains from `u` and from `v` at hash address `i` that end at the same
value either start at the same value, or first split at a step `j < n`: their `j`-step values
differ while the two `F` entries at hash address `i + j` are both cached with the same
answer. -/
theorem chain?_diverge (pk : core.PkSeed) (adrs : Adrs) (u v : core.Y) (i n : ℕ) {y : core.Y}
    (hu : chain? core c pk adrs u i n = some y) (hv : chain? core c pk adrs v i n = some y) :
    u = v ∨ ∃ j, j < n ∧ ∃ u' v' w, u' ≠ v' ∧
      chain? core c pk adrs u i j = some u' ∧ chain? core c pk adrs v i j = some v' ∧
      c (.thash pk (core.adrsToKey (adrs.setHashAddress (i + j))) [u']) = some w ∧
      c (.thash pk (core.adrsToKey (adrs.setHashAddress (i + j))) [v']) = some w := by
  induction n generalizing y with
  | zero =>
    rw [chain?_zero] at hu hv
    exact Or.inl ((Option.some.inj hu).trans (Option.some.inj hv).symm)
  | succ n ih =>
    obtain ⟨u₁, hu₁, hqu⟩ := (chain?_succ_eq_some_iff core c pk adrs u i n).mp hu
    obtain ⟨v₁, hv₁, hqv⟩ := (chain?_succ_eq_some_iff core c pk adrs v i n).mp hv
    by_cases h : u₁ = v₁
    · subst h
      exact (ih hu₁ hv₁).imp id fun ⟨j, hj, rest⟩ => ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    · exact Or.inr ⟨n, Nat.lt_succ_self n, u₁, v₁, y, h, hu₁, hv₁, hqu, hqv⟩

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

/-! ## Algorithms 18--20 -/

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

variable {core c} in
/-- Algorithm 20 settled at any verdict has its `H_msg` digest, its FORS public key and its
hypertree recovery settled. -/
theorem exists_of_simulateQ_toPartialImpl_verifyInternalM_eq_some [DecidableEq core.Y]
    {msg : List Byte} {sig : GeneralScheme.SignatureCore vp core} {pk : PublicKeyCore core}
    {b : Bool} (h : simulateQ c.toPartialImpl
      (GeneralScheme.verifyInternalM (m := OracleComp (publicHashSpec core)) vp core msg sig pk) =
        some b) :
    ∃ digest forsPk root, c (.hmsg sig.randomness pk.pkSeed pk.pkRoot msg) = some digest ∧
      forsPkFromSig? core c sig.fors (splitDigest vp.params digest).md.toList pk.pkSeed
        (splitDigest vp.params digest).forsAdrs = some forsPk ∧
      simulateQ c.toPartialImpl (GeneralHypertree.pkFromSigM vp core forsPk sig.hypertree
        pk.pkSeed (splitDigest vp.params digest)) = some root := by
  simp only [GeneralScheme.verifyInternalM, GeneralHypertree.verifyM, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_hmsg] at h
  obtain ⟨digest, hd, forsPk, hf, root, hr, -⟩ := h
  exact ⟨digest, forsPk, root, hd, hf, hr⟩

end Hypertree

end SLHDSA.Security
