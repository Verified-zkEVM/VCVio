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
single `H_msg`, `T_l`, `F` or `H` query to a cache lookup.  The readers `chain?`, `xmssPkFromSig?`
and `forsPkFromSig?` are the verifier's programs under the cache; they draw no secret.  The
readers of the programs that do draw a secret take the secret provider as an argument and are in
`HashSig.SLHDSA.Security.CacheSecret`.

## Scope

* No property of any particular cache is proved here.
* Nothing here is probabilistic.
* The readers are definitions over `simulateQ c.toPartialImpl`; the decompositions of the
  underlying programs into their individual hash queries belong to
  `HashSig.SLHDSA.Security.CacheDecomposition`.
* Nothing here is quantum: the cache is a classical table.

## Labels

Seven declarations.

*One-query readings*: `simulateQ_toPartialImpl_hmsg`, `simulateQ_toPartialImpl_tl`,
`simulateQ_toPartialImpl_f`, `simulateQ_toPartialImpl_h`.

*Readers*: `chain?`, `xmssPkFromSig?`, `forsPkFromSig?`.
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

end SLHDSA.Security
