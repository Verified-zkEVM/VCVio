/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.XmssWitnesses
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Reading honest SLH-DSA values off a public-hash cache

A public-hash cache `PublicHash.Cache core` is a partial table of the tweakable-hash and `H_msg`
answers a lazy random oracle has handed out.  Read as the partial query implementation
`QueryCache.toPartialImpl`, it evaluates a hash-only program to `some v` exactly when every query
the program makes is in the table, and then `v` is the value the program computes under *every*
total answer function agreeing with the cache (`QueryCache.evalWithAnswerFn_eq_of_agreesWithFn`).
This module names that reading for the honest SLH-DSA component programs.

The four one-query lemmas `simulateQ_toPartialImpl_hmsg`, `_tl`, `_f`, `_h` reduce a
single `H_msg`, `T_l`, `F` or `H` query to a cache lookup.  The readers `xmssRoot?`, `xmssNode?`,
`forsPkGen?`, `forsNode?`, `wotsPkGenTops?`, `chain?`, `xmssPkFromSig?` and `forsPkFromSig?` are
the honest and the verifier's programs under the cache, and the `*_withPublicHash_eq_of_*_eq_some`
lemmas transport a successful reading to the pure API at `PublicHash.withPublicHash core f` for
every agreeing `f`.  `xmss_stop_case` applies
them: an XMSS signature whose recovered root is settled at the honest root of the same
tree yields, under every agreeing `f`, either the honest WOTS+ public key or an `H`-collision on
the leaf's root path.

## Scope

* No property of any particular cache is proved here.  Which entries a run of the counted
  random-oracle experiment settles belongs to `HashSig.SLHDSA.Security.RomTranscript`.
* Nothing here is probabilistic.
* The readers are definitions over `simulateQ c.toPartialImpl`; the decompositions of the
  underlying programs into their individual hash queries belong to
  `HashSig.SLHDSA.Security.CacheDecomposition`.
* Nothing here is quantum: the cache is a classical table.

## Labels

Eighteen declarations.

*One-query readings*: `simulateQ_toPartialImpl_hmsg`, `simulateQ_toPartialImpl_tl`,
`simulateQ_toPartialImpl_f`, `simulateQ_toPartialImpl_h`.

*Readers*: `xmssRoot?`, `xmssNode?`, `forsPkGen?`, `forsNode?`, `wotsPkGenTops?`, `chain?`,
`xmssPkFromSig?`, `forsPkFromSig?`.

*Transport to the pure API*: `xmssRoot_withPublicHash_eq_of_xmssRoot?_eq_some`,
`xmssPkFromSig_withPublicHash_eq_of_xmssPkFromSig?_eq_some`,
`chain_withPublicHash_eq_of_chain?_eq_some`,
`wotsPkGenTops_withPublicHash_eq_of_wotsPkGenTops?_eq_some`.

*Existence of an agreeing total answer function*: the `(publicHashSpec core).Inhabited`
instance, through which `QueryCache.exists_agreesWithFn` applies to every public-hash cache.

*First descent stop case*: `xmss_stop_case`.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

variable {p : Params} (core : CorePrimitives p)

/-! ## One-query readings -/

/-- One `H_msg` query under the cache is the cache entry at that query. -/
theorem simulateQ_toPartialImpl_hmsg (c : PublicHash.Cache core) (R : core.Y)
    (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    simulateQ c.toPartialImpl
        (PublicHash.hmsg core R pkSeed pkRoot msg : OracleComp (publicHashSpec core) (Bytes p.m)) =
      c (.hmsg R pkSeed pkRoot msg) := by
  simp only [PublicHash.hmsg, simulateQ_HasQuery_query, QueryCache.toPartialImpl_apply]

/-- One `T_l` query under the cache is the cache entry at that query. -/
theorem simulateQ_toPartialImpl_tl (c : PublicHash.Cache core) (pkSeed : core.PkSeed)
    (adrs : Adrs) (xs : List core.Y) :
    simulateQ c.toPartialImpl
        (PublicHash.tl core pkSeed adrs xs : OracleComp (publicHashSpec core) core.Y) =
      c (.thash pkSeed (core.adrsToKey adrs) xs) := by
  simp only [PublicHash.tl, simulateQ_HasQuery_query, QueryCache.toPartialImpl_apply]

/-- One `F` query under the cache is the cache entry at that query. -/
theorem simulateQ_toPartialImpl_f (c : PublicHash.Cache core) (pkSeed : core.PkSeed)
    (adrs : Adrs) (x : core.Y) :
    simulateQ c.toPartialImpl
        (PublicHash.f core pkSeed adrs x : OracleComp (publicHashSpec core) core.Y) =
      c (.thash pkSeed (core.adrsToKey adrs) [x]) := by
  simp only [PublicHash.f, simulateQ_HasQuery_query, QueryCache.toPartialImpl_apply]

/-- One `H` query under the cache is the cache entry at that query. -/
theorem simulateQ_toPartialImpl_h (c : PublicHash.Cache core) (pkSeed : core.PkSeed)
    (adrs : Adrs) (l r : core.Y) :
    simulateQ c.toPartialImpl
        (PublicHash.h core pkSeed adrs l r : OracleComp (publicHashSpec core) core.Y) =
      c (.thash pkSeed (core.adrsToKey adrs) [l, r]) := by
  simp only [PublicHash.h, simulateQ_HasQuery_query, QueryCache.toPartialImpl_apply]

/-! ## Readers -/

/-- The honest XMSS tree root read off a cache. -/
@[expose]
def xmssRoot? (c : PublicHash.Cache core) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    Option core.Y :=
  simulateQ c.toPartialImpl (xmssRootM core sk pk adrs)

/-- The honest XMSS subtree root at height `z`, index `t`, read off a cache. -/
@[expose]
def xmssNode? (c : PublicHash.Cache core) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs)
    (z t : ℕ) : Option core.Y :=
  simulateQ c.toPartialImpl (xmssNodeM core sk pk adrs z t)

/-- The honest FORS public key read off a cache. -/
@[expose]
def forsPkGen? (c : PublicHash.Cache core) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    Option core.Y :=
  simulateQ c.toPartialImpl (forsPkGenM core sk pk adrs)

/-- The honest FORS subtree root at height `z`, global leaf-numbered index `t`, read off a
cache. -/
@[expose]
def forsNode? (c : PublicHash.Cache core) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs)
    (z t : ℕ) : Option core.Y :=
  simulateQ c.toPartialImpl (PerfectMerkleTree.merkleRootM
    (forsLeafWith core (PublicHash.f core pk) sk pk adrs)
    (forsNodeHashWith (PublicHash.h core pk) adrs) z t)

/-- The honest WOTS+ chain tops read off a cache. -/
@[expose]
def wotsPkGenTops? (c : PublicHash.Cache core) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) : Option (Vector core.Y p.len) :=
  simulateQ c.toPartialImpl (wotsPkGenTopsM core sk pk adrs)

/-- One WOTS+ chain value, `s` steps from `x` starting at hash address `i`, read off a cache. -/
@[expose]
def chain? (c : PublicHash.Cache core) (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) (i s : ℕ) :
    Option core.Y :=
  simulateQ c.toPartialImpl (chainM core pk adrs x i s)

/-- The root an XMSS signature recovers, read off a cache. -/
@[expose]
def xmssPkFromSig? (c : PublicHash.Cache core) (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) : Option core.Y :=
  simulateQ c.toPartialImpl (xmssPkFromSigM core idx sig msg pk adrs)

/-- The FORS public key a signature recovers on message digest `md`, read off a cache. -/
@[expose]
def forsPkFromSig? (c : PublicHash.Cache core) (sig : ForsSigCore p core) (md : List Byte)
    (pk : core.PkSeed) (adrs : Adrs) : Option core.Y :=
  simulateQ c.toPartialImpl (forsPkFromSigM core sig md pk adrs)

/-! ## Transport to the pure API -/

variable {core} {c : PublicHash.Cache core} {f : QueryImpl (publicHashSpec core) Id}
  (hf : c.AgreesWithFn f)
include hf

/-- A settled honest XMSS root is the pure root under every agreeing total answer function. -/
theorem xmssRoot_withPublicHash_eq_of_xmssRoot?_eq_some {sk : core.SkSeed} {pk : core.PkSeed}
    {adrs : Adrs} {r : core.Y} (h : xmssRoot? core c sk pk adrs = some r) :
    xmssRoot (PublicHash.withPublicHash core f) sk pk adrs = r := by
  rw [← simulateQ_xmssRootM_withPublicHash]
  exact QueryCache.evalWithAnswerFn_eq_of_agreesWithFn hf _ h

/-- A settled recovered XMSS root is the pure recovered root under every agreeing total answer
function. -/
theorem xmssPkFromSig_withPublicHash_eq_of_xmssPkFromSig?_eq_some {idx : ℕ}
    {sig : XmssSig p core} {msg : core.Y} {pk : core.PkSeed} {adrs : Adrs} {r : core.Y}
    (h : xmssPkFromSig? core c idx sig msg pk adrs = some r) :
    xmssPkFromSig (PublicHash.withPublicHash core f) idx sig msg pk adrs = r := by
  rw [← simulateQ_xmssPkFromSigM_withPublicHash]
  exact QueryCache.evalWithAnswerFn_eq_of_agreesWithFn hf _ h

/-- A settled chain value is the pure chain value under every agreeing total answer
function. -/
theorem chain_withPublicHash_eq_of_chain?_eq_some {pk : core.PkSeed} {adrs : Adrs} {x : core.Y}
    {i s : ℕ} {y : core.Y} (h : chain? core c pk adrs x i s = some y) :
    chain (PublicHash.withPublicHash core f) pk adrs x i s = y := by
  rw [← simulateQ_chainM_withPublicHash]
  exact QueryCache.evalWithAnswerFn_eq_of_agreesWithFn hf _ h

/-- Settled honest chain tops are the pure chain tops under every agreeing total answer
function. -/
theorem wotsPkGenTops_withPublicHash_eq_of_wotsPkGenTops?_eq_some {sk : core.SkSeed}
    {pk : core.PkSeed} {adrs : Adrs} {tops : Vector core.Y p.len}
    (h : wotsPkGenTops? core c sk pk adrs = some tops) :
    wotsPkGenTops (PublicHash.withPublicHash core f) sk pk adrs = tops := by
  rw [← simulateQ_wotsPkGenTopsM_withPublicHash]
  exact QueryCache.evalWithAnswerFn_eq_of_agreesWithFn hf _ h

/-! ## First descent stop case -/

/-- An XMSS signature at leaf `idx` whose recovered root is settled at the honest root of the
same tree yields, under every total answer function agreeing with the cache, either the honest
WOTS+ public key at that leaf or an `H`-collision at an internal node on the leaf's root path
whose first endpoint is the honest child pair. -/
theorem xmss_stop_case (idx : ℕ) (hidx : idx < 2 ^ p.hp) (sig : XmssSig p core) (msg : core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) {r : core.Y}
    (hforge : xmssPkFromSig? core c idx sig msg pk adrs = some r)
    (hhonest : xmssRoot? core c sk pk adrs = some r) :
    let prims := PublicHash.withPublicHash core f
    wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx) =
        wotsPkGen prims sk pk (wotsLeafAdrs adrs idx) ∨
      ∃ (z : ℕ) (cc : core.Y × core.Y), 0 < z ∧ z ≤ p.hp ∧
        xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z) ≠ cc ∧
        prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z))
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).1
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).2 =
          prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z)) cc.1 cc.2 :=
  xmssPkFromSig_cases (PublicHash.withPublicHash core f) idx hidx sig msg sk pk adrs
    ((xmssPkFromSig_withPublicHash_eq_of_xmssPkFromSig?_eq_some hf hforge).trans
      (xmssRoot_withPublicHash_eq_of_xmssRoot?_eq_some hf hhonest).symm)

omit hf

/-! ## Existence of an agreeing total answer function -/

/-- Every public-hash query has an inhabited answer type once the node type is inhabited, so
`QueryCache.exists_agreesWithFn` extends every public-hash cache to a total answer function. -/
instance instInhabitedPublicHashSpec [Inhabited core.Y] : (publicHashSpec core).Inhabited where
  inhabitedB q := by cases q <;> infer_instance

end SLHDSA.Security
