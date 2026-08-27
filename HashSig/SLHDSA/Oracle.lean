/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Primitives
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Explicit public-hash oracle for SLH-DSA

This module gives the four public SLH-DSA hash operations an explicit oracle syntax.  The query
identity retains the function family, public seed, complete address, ordered input, and (for
`T_l`) the full input list.  Consequently a lazy random-oracle handler cannot accidentally
identify nodes at different addresses or calls to different hash families.

`PublicHash.impl` interprets the syntax with the deterministic functions in `Primitives`.
`PublicHash.randomOracle` instead samples each previously unseen tagged query once and caches the
answer.  Both handlers interpret the same canonical `OracleComp` programs.

The keyed operations `PRF` and `PRF_msg` are intentionally not part of this public interface:
security games may expose this oracle to an adversary without exposing secret-key operations.

The ideal-oracle domain stores the complete structural `Adrs`.  The concrete SHA-2 instantiation
compresses addresses to `ADRSc`; relating that encoding to this ideal model requires a separate
reachability/injectivity argument and is not claimed here.

## References

- NIST FIPS 205, Section 4.1 (`F`, `H`, `T_l`, and `H_msg`)
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}

/-- A tagged query to one of the public SLH-DSA hash functions.  The carrier types are explicit
parameters so the generated decidable-equality instance uses the caller's concrete instances. -/
inductive PublicHashQuery (PkSeed Y : Type) where
  /-- `F(PK.seed, ADRS, x)`. -/
  | f (pkSeed : PkSeed) (adrs : Adrs) (x : Y)
  /-- `H(PK.seed, ADRS, left, right)`.  The child order is part of the query. -/
  | h (pkSeed : PkSeed) (adrs : Adrs) (left right : Y)
  /-- `T_l(PK.seed, ADRS, xs)`.  Length and order are part of the query. -/
  | tl (pkSeed : PkSeed) (adrs : Adrs) (xs : List Y)
  /-- `H_msg(R, PK.seed, PK.root, M)`. -/
  | hmsg (r : Y) (pkSeed : PkSeed) (pkRoot : Y) (msg : List Byte)
deriving DecidableEq

/-- The dependent public-hash specification.  Reducibility is intentional: consumers must be able
to see that the first three constructors return nodes while `H_msg` returns a digest. -/
@[reducible] def publicHashSpec (prims : Primitives p) :
    OracleSpec (PublicHashQuery prims.PkSeed prims.Y)
  | .f _ _ _ => prims.Y
  | .h _ _ _ _ => prims.Y
  | .tl _ _ _ => prims.Y
  | .hmsg _ _ _ _ => Bytes p.m

namespace PublicHash

/-- Issue an explicit `F` query. -/
def f (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) : m prims.Y :=
  query (spec := publicHashSpec prims) (PublicHashQuery.f pkSeed adrs x)

/-- Issue an explicit ordered binary-node `H` query. -/
def h (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (left right : prims.Y) : m prims.Y :=
  query (spec := publicHashSpec prims) (PublicHashQuery.h pkSeed adrs left right)

/-- Issue an explicit variable-arity `T_l` query. -/
def tl (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (xs : List prims.Y) : m prims.Y :=
  query (spec := publicHashSpec prims) (PublicHashQuery.tl pkSeed adrs xs)

/-- Issue an explicit `H_msg` query. -/
def hmsg (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (r : prims.Y) (pkSeed : prims.PkSeed) (pkRoot : prims.Y) (msg : List Byte) :
    m (Bytes p.m) :=
  query (spec := publicHashSpec prims) (PublicHashQuery.hmsg r pkSeed pkRoot msg)

/-- Deterministically interpret the public-hash syntax using the functions in `Primitives`. -/
def impl (prims : Primitives p) : QueryImpl (publicHashSpec prims) Id
  | .f pkSeed adrs x => prims.F pkSeed adrs x
  | .h pkSeed adrs left right => prims.H pkSeed adrs left right
  | .tl pkSeed adrs xs => prims.Tl pkSeed adrs xs
  | .hmsg r pkSeed pkRoot msg => prims.Hmsg r pkSeed pkRoot msg

/-- Reinterpret the four public hash fields of `prims` through an arbitrary deterministic answer
function, while leaving the secret PRFs and node encoding unchanged.  This is the functional
bridge used to prove random-oracle correctness: every total answer function defines another
perfectly valid pure SLH-DSA primitive bundle. -/
@[reducible] def withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) :
    Primitives p where
  PkSeed := prims.PkSeed
  SkSeed := prims.SkSeed
  SkPrf := prims.SkPrf
  Y := prims.Y
  F pkSeed adrs x := answer (.f pkSeed adrs x)
  H pkSeed adrs left right := answer (.h pkSeed adrs left right)
  Tl pkSeed adrs xs := answer (.tl pkSeed adrs xs)
  PRF := prims.PRF
  PRFmsg := prims.PRFmsg
  Hmsg r pkSeed pkRoot msg := answer (.hmsg r pkSeed pkRoot msg)
  yToBytes := prims.yToBytes

@[simp] theorem withPublicHash_f (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) :
    (withPublicHash prims answer).F pkSeed adrs x = answer (.f pkSeed adrs x) := rfl

@[simp] theorem withPublicHash_h (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (left right : prims.Y) :
    (withPublicHash prims answer).H pkSeed adrs left right =
      answer (.h pkSeed adrs left right) := rfl

@[simp] theorem withPublicHash_tl (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (xs : List prims.Y) :
    (withPublicHash prims answer).Tl pkSeed adrs xs = answer (.tl pkSeed adrs xs) := rfl

@[simp] theorem withPublicHash_hmsg (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (r : prims.Y) (pkSeed : prims.PkSeed)
    (pkRoot : prims.Y) (msg : List Byte) :
    (withPublicHash prims answer).Hmsg r pkSeed pkRoot msg =
      answer (.hmsg r pkSeed pkRoot msg) := rfl

@[simp] theorem simulateQ_f (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.f prims pkSeed adrs x : OracleComp (publicHashSpec prims) prims.Y) =
      prims.F pkSeed adrs x := by
  simp only [f, simulateQ_HasQuery_query, impl]

@[simp] theorem simulateQ_h (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (left right : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.h prims pkSeed adrs left right : OracleComp (publicHashSpec prims) prims.Y) =
      prims.H pkSeed adrs left right := by
  simp only [h, simulateQ_HasQuery_query, impl]

@[simp] theorem simulateQ_tl (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (xs : List prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.tl prims pkSeed adrs xs : OracleComp (publicHashSpec prims) prims.Y) =
      prims.Tl pkSeed adrs xs := by
  simp only [tl, simulateQ_HasQuery_query, impl]

@[simp] theorem simulateQ_hmsg (prims : Primitives p) (r : prims.Y)
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y) (msg : List Byte) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.hmsg prims r pkSeed pkRoot msg :
          OracleComp (publicHashSpec prims) (Bytes p.m)) =
      prims.Hmsg r pkSeed pkRoot msg := by
  simp only [hmsg, simulateQ_HasQuery_query, impl]

/-- The cache used by the lazy public random oracle. -/
abbrev Cache (prims : Primitives p) := (publicHashSpec prims).QueryCache

/-- Lazy random-oracle interpretation of the tagged public hash syntax. -/
@[reducible] def randomOracle (prims : Primitives p)
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    [SampleableType prims.Y] [SampleableType (Bytes p.m)] :
    QueryImpl (publicHashSpec prims) (StateT (PublicHash.Cache prims) ProbComp) := by
  letI : ∀ t : PublicHashQuery prims.PkSeed prims.Y,
      SampleableType ((publicHashSpec prims).Range t) := fun t => by
    cases t <;> exact inferInstance
  exact (publicHashSpec prims).randomOracle

/-- Install the lazy random oracle as the query capability of a state transformer.  This is a
named value rather than a global instance: a security experiment must opt into this semantics
once, and then thread the resulting cache through key generation, the adversary, signing, and
verification. -/
@[instance_reducible]
def randomOracleHasQuery (prims : Primitives p) [DecidableEq prims.PkSeed]
    [DecidableEq prims.Y] [SampleableType prims.Y] [SampleableType (Bytes p.m)] :
    HasQuery (publicHashSpec prims) (StateT (PublicHash.Cache prims) ProbComp) where
  query := PublicHash.randomOracle prims

end PublicHash

end SLHDSA
