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

This module gives the public SLH-DSA hash operations an explicit oracle syntax.  `F`, `H = T₂`,
and `T_l` are arity-specific wrappers around one tweakable-hash collection query.  Its identity
retains the public seed, the instantiation's canonical encoded address, and the full ordered input
list.  Thus the ideal model has exactly the aliases of the concrete address serialization.

`PublicHash.impl` interprets the syntax with the deterministic functions in `Primitives`.
`PublicHash.randomOracle` instead samples each previously unseen tagged query once and caches the
answer.  Both handlers interpret the same canonical `OracleComp` programs.

The keyed operations `PRF` and `PRF_msg` are intentionally not part of this public interface:
security games may expose this oracle to an adversary without exposing secret-key operations.
This is a modular tweakable-hash/PRF model, not a claim that every named operation is an
independent domain of one raw SHA/XOF random oracle.  A proof connecting the model to a concrete
hash instantiation must discharge the corresponding PRF and public-collection assumptions.

## References

- NIST FIPS 205, Section 4.1 (`F`, `H`, `T_l`, and `H_msg`)
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}

/-- A query to the public SLH-DSA hash collection.  The carrier types are explicit
parameters so the generated decidable-equality instance uses the caller's concrete instances. -/
inductive PublicHashQuery (PkSeed AdrsKey Y : Type) where
  /-- `T_l(PK.seed, encodedADRS, xs)`.  `F` and `H` use lists of length one and two. -/
  | thash (pkSeed : PkSeed) (adrsKey : AdrsKey) (xs : List Y)
  /-- `H_msg(R, PK.seed, PK.root, M)`. -/
  | hmsg (r : Y) (pkSeed : PkSeed) (pkRoot : Y) (msg : List Byte)
deriving DecidableEq

/-- The dependent public-hash specification.  Reducibility is intentional: consumers must see
that `thash` returns a node while `H_msg` returns a digest. -/
@[reducible] def publicHashSpec (prims : Primitives p) :
    OracleSpec (PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)
  | .thash _ _ _ => prims.Y
  | .hmsg _ _ _ _ => Bytes p.m

namespace PublicHash

/-- Issue an explicit `F` query. -/
def f (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) : m prims.Y :=
  query (spec := publicHashSpec prims)
    (PublicHashQuery.thash pkSeed (prims.adrsToKey adrs) [x])

/-- Issue an explicit ordered binary-node `H` query. -/
def h (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (left right : prims.Y) : m prims.Y :=
  query (spec := publicHashSpec prims)
    (PublicHashQuery.thash pkSeed (prims.adrsToKey adrs) [left, right])

/-- Issue an explicit variable-arity `T_l` query. -/
def tl (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (xs : List prims.Y) : m prims.Y :=
  query (spec := publicHashSpec prims)
    (PublicHashQuery.thash pkSeed (prims.adrsToKey adrs) xs)

/-- Issue an explicit `H_msg` query. -/
def hmsg (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (r : prims.Y) (pkSeed : prims.PkSeed) (pkRoot : prims.Y) (msg : List Byte) :
    m (Bytes p.m) :=
  query (spec := publicHashSpec prims) (PublicHashQuery.hmsg r pkSeed pkRoot msg)

/-- Deterministically interpret the public-hash syntax using the functions in `Primitives`. -/
def impl (prims : Primitives p) : QueryImpl (publicHashSpec prims) Id
  | .thash pkSeed encodedAdrs xs => prims.Thash pkSeed encodedAdrs xs
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
  AdrsKey := prims.AdrsKey
  adrsToKey := prims.adrsToKey
  Thash pkSeed encodedAdrs xs := answer (.thash pkSeed encodedAdrs xs)
  PRF := prims.PRF
  PRFmsg := prims.PRFmsg
  Hmsg r pkSeed pkRoot msg := answer (.hmsg r pkSeed pkRoot msg)
  yToBytes := prims.yToBytes

@[simp] theorem withPublicHash_f (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) :
    (withPublicHash prims answer).F pkSeed adrs x =
      answer (.thash pkSeed (prims.adrsToKey adrs) [x]) := rfl

@[simp] theorem withPublicHash_h (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (left right : prims.Y) :
    (withPublicHash prims answer).H pkSeed adrs left right =
      answer (.thash pkSeed (prims.adrsToKey adrs) [left, right]) := rfl

@[simp] theorem withPublicHash_tl (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (xs : List prims.Y) :
    (withPublicHash prims answer).Tl pkSeed adrs xs =
      answer (.thash pkSeed (prims.adrsToKey adrs) xs) := rfl

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
    [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    [SampleableType prims.Y] [SampleableType (Bytes p.m)] :
    QueryImpl (publicHashSpec prims) (StateT (PublicHash.Cache prims) ProbComp) := by
  letI : ∀ t : PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y,
      SampleableType ((publicHashSpec prims).Range t) := fun t => by
    cases t <;> exact inferInstance
  exact (publicHashSpec prims).randomOracle

/-- Install the lazy random oracle as the query capability of a state transformer.  This is a
named value rather than a global instance: a security experiment must opt into this semantics
once, and then thread the resulting cache through key generation, the adversary, signing, and
verification. -/
@[instance_reducible]
def randomOracleHasQuery (prims : Primitives p) [DecidableEq prims.PkSeed]
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    [SampleableType prims.Y] [SampleableType (Bytes p.m)] :
    HasQuery (publicHashSpec prims) (StateT (PublicHash.Cache prims) ProbComp) where
  query := PublicHash.randomOracle prims

end PublicHash

end SLHDSA
