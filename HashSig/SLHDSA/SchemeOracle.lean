/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.ForsOracle
public import HashSig.SLHDSA.Scheme

/-!
# Explicit-oracle SLH-DSA vertical slice

This module assembles the currently supported single-layer (`d = 1`) SLH-DSA scheme from the
oracle-parametric WOTS+, XMSS, and FORS components.  All public `F`, `H`, `T_l`, and `H_msg`
evaluations are explicit queries.  `PRF` and `PRF_msg` remain keyed operations on `Primitives` and
are not exposed through the public oracle.

The algorithms are monad-parametric and never allocate or reset an oracle cache.  A random-oracle
security experiment must interpret the complete keygen/sign/adversary/verify computation once with
`PublicHash.randomOracle`; evaluating those phases separately would create different random
functions.  This file deliberately makes no generic completeness claim for arbitrary `HasQuery`
handlers.

The general `d > 1` hypertree remains a separate required migration before this interface can
replace the generic FIPS 205 scheme surface.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA

open PerfectMerkleTree

variable {p : Params}

/-- Evidence that a parameter record really denotes the single-XMSS-layer profile implemented by
this module.  `Params` stores `d` and `h'` independently, so checking only `d = 1` would still
permit an inconsistent record with `h' ≠ h`. -/
class Params.IsSingleLayer (p : Params) : Prop where
  d_eq_one : p.d = 1
  hp_eq_h : p.hp = p.h

instance : Params.IsSingleLayer slhdsaSha2_128_24 where
  d_eq_one := rfl
  hp_eq_h := rfl

namespace OracleScheme

/-- A single-layer SLH-DSA signature with typed FORS and XMSS authentication paths. -/
abbrev Signature (p : Params) (prims : Primitives p) :=
  prims.Y × ForsOracle.Signature p prims × XmssOracle.Signature p prims

/-- Internal key generation.  The public root is computed by the streaming XMSS engine. -/
def keygenInternalM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) : m (PublicKey prims × SecretKey prims) := do
  let pkRoot ← XmssOracle.rootM prims skSeed pkSeed (htAdrs Adrs.zero 0)
  pure (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- Internal signing for the supported `d = 1` parameter set. -/
def signInternalM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    (msg : List Byte) (sk : SecretKey prims)
    (addrnd : prims.Y) : m (Signature p prims) := do
  let r := prims.PRFmsg sk.skPrf addrnd msg
  let digest ← PublicHash.hmsg prims r sk.pkSeed sk.pkRoot msg
  let md := (splitDigest p digest).1
  let index : LeafIndex p.hp := ⟨(splitDigest p digest).2, splitDigest_snd_lt p digest⟩
  let forsAddress := forsAdrsOf index.val
  let forsSig ← ForsOracle.signM prims md sk.skSeed sk.pkSeed forsAddress
  let forsPk ← ForsOracle.pkFromSigM prims forsSig md sk.pkSeed forsAddress
  let xmssSig ←
    XmssOracle.signM prims forsPk sk.skSeed sk.pkSeed (htAdrs Adrs.zero 0) index
  pure (r, forsSig, xmssSig)

/-- Internal verification.  Its result is monadic because all public hashes are oracle queries. -/
def verifyInternalM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    [DecidableEq prims.Y] (msg : List Byte)
    (sig : Signature p prims) (pk : PublicKey prims) : m Bool := do
  let digest ← PublicHash.hmsg prims sig.1 pk.pkSeed pk.pkRoot msg
  let md := (splitDigest p digest).1
  let index : LeafIndex p.hp := ⟨(splitDigest p digest).2, splitDigest_snd_lt p digest⟩
  let forsAddress := forsAdrsOf index.val
  let forsPk ← ForsOracle.pkFromSigM prims sig.2.1 md pk.pkSeed forsAddress
  let root ← XmssOracle.pkFromSigM prims index sig.2.2 forsPk pk.pkSeed (htAdrs Adrs.zero 0)
  pure (decide (root = pk.pkRoot))

/-- External key generation with lifted public randomness and explicit public-hash queries. -/
def keygenM (prims : Primitives p) {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    [SampleableType prims.SkSeed]
    [SampleableType prims.SkPrf] [SampleableType prims.PkSeed] :
    m (PublicKey prims × SecretKey prims) := do
  let skSeed ← liftM ($ᵗ prims.SkSeed)
  let skPrf ← liftM ($ᵗ prims.SkPrf)
  let pkSeed ← liftM ($ᵗ prims.PkSeed)
  keygenInternalM prims skSeed skPrf pkSeed

/-- External hedged signing with lifted public randomness. -/
def signM (prims : Primitives p) {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    [SampleableType prims.Y] (sk : SecretKey prims)
    (msg : List Byte) : m (Signature p prims) := do
  let addrnd ← liftM ($ᵗ prims.Y)
  signInternalM prims msg sk addrnd

/-- The explicit-oracle, single-layer SLH-DSA signature algorithm. -/
def alg (prims : Primitives p) {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    [SampleableType prims.SkSeed]
    [SampleableType prims.SkPrf] [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.Y] :
    SignatureAlg m (List Byte) (PublicKey prims) (SecretKey prims) (Signature p prims) where
  keygen := keygenM prims
  sign _ sk msg := signM prims sk msg
  verify pk msg sig := verifyInternalM prims msg sig pk

/-- The single-layer algorithm with the lazy random oracle installed as its explicit query
capability.  The resulting state transformer still exposes the cache: the surrounding security
experiment, not any scheme phase, chooses the initial cache and runs the entire game once. -/
def randomOracleAlg (prims : Primitives p) [Params.IsSingleLayer p]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [SampleableType (Bytes p.m)] :
    SignatureAlg (StateT (PublicHash.Cache prims) ProbComp) (List Byte)
      (PublicKey prims) (SecretKey prims) (Signature p prims) := by
  letI := PublicHash.randomOracleHasQuery prims
  exact alg prims

end OracleScheme

end SLHDSA
