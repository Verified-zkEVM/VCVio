/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.ForsOracle
public import HashSig.SLHDSA.Scheme
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

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

/-- Internal signing for the supported `d = 1` parameter set.

The general hypertree algorithm recovers each intermediate XMSS root to feed the next layer.  At
`d = 1` there is no next layer, so this slice omits that output-dead recovery query.  Consequently
it is output-equivalent to the FIPS algorithm but intentionally does not claim literal query-trace
equality with a mechanically specialized `d = 1` pseudocode transcription. -/
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

/-- Honest key generation, signing, and verification are functionally complete after fixing any
deterministic public-hash answer function.  The same answer function interprets the whole program,
so repeated queries—in particular the signing and verification `H_msg` calls—receive the same
answer.  This is deliberately stronger than canonical-function parity but does not identify the
trace of an arbitrary effectful handler. -/
theorem simulateQ_honest_roundTrip_withPublicHash (prims : Primitives p)
    [Params.IsSingleLayer p] [DecidableEq prims.Y]
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : List Byte)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) :
    simulateQ answer (do
      let (pk, sk) ← (keygenInternalM prims skSeed skPrf pkSeed :
        OracleComp (publicHashSpec prims) (PublicKey prims × SecretKey prims))
      let sig ← signInternalM prims msg sk addrnd
      verifyInternalM prims msg sig pk) = true := by
  let functionalPrims := PublicHash.withPublicHash prims answer
  let root := XmssOracle.root functionalPrims skSeed pkSeed (htAdrs Adrs.zero 0)
  let r := prims.PRFmsg skPrf addrnd msg
  let digest := answer (.hmsg r pkSeed root msg)
  let md := (splitDigest p digest).1
  let index : LeafIndex p.hp :=
    ⟨(splitDigest p digest).2, splitDigest_snd_lt p digest⟩
  let forsAddress := forsAdrsOf index.val
  simp only [keygenInternalM, signInternalM, verifyInternalM,
    simulateQ_bind, simulateQ_pure,
    XmssOracle.simulateQ_rootM_withPublicHash,
    ForsOracle.simulateQ_signM_withPublicHash,
    ForsOracle.simulateQ_pkFromSigM_withPublicHash,
    XmssOracle.simulateQ_signM_withPublicHash,
    XmssOracle.simulateQ_pkFromSigM_withPublicHash,
    PublicHash.hmsg, simulateQ_HasQuery_query]
  change decide (
    XmssOracle.pkFromSig functionalPrims index
      (XmssOracle.sign functionalPrims
        (ForsOracle.pkFromSig functionalPrims
          (ForsOracle.sign functionalPrims md skSeed pkSeed forsAddress)
          md pkSeed forsAddress)
        skSeed pkSeed (htAdrs Adrs.zero 0) index)
      (ForsOracle.pkFromSig functionalPrims
        (ForsOracle.sign functionalPrims md skSeed pkSeed forsAddress)
        md pkSeed forsAddress)
      pkSeed (htAdrs Adrs.zero 0) = root) = true
  rw [ForsOracle.pkFromSig_sign, XmssOracle.pkFromSig_sign]
  apply decide_eq_true
  exact (XmssOracle.root_eq_xmssRoot functionalPrims skSeed pkSeed
    (htAdrs Adrs.zero 0)).symm

/-- Canonical deterministic-handler corollary of honest scheme execution. -/
theorem simulateQ_honest_roundTrip (prims : Primitives p)
    [Params.IsSingleLayer p] [DecidableEq prims.Y] (msg : List Byte)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) :
    simulateQ (PublicHash.impl prims) (do
      let (pk, sk) ← (keygenInternalM prims skSeed skPrf pkSeed :
        OracleComp (publicHashSpec prims) (PublicKey prims × SecretKey prims))
      let sig ← signInternalM prims msg sk addrnd
      verifyInternalM prims msg sig pk) = true :=
  simulateQ_honest_roundTrip_withPublicHash prims (PublicHash.impl prims) msg
    skSeed skPrf pkSeed addrnd

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

/-- External empty-context hedged signing with lifted public randomness.  The raw caller message
is encoded as FIPS 205's `M' = 0x00 || 0x00 || M` before entering Algorithm 19. -/
def signM (prims : Primitives p) {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    [SampleableType prims.Y] (sk : SecretKey prims)
    (msg : List Byte) : m (Signature p prims) := do
  let addrnd ← liftM ($ᵗ prims.Y)
  signInternalM prims (emptyContextMessage msg) sk addrnd

/-- External empty-context verification.  It applies the same FIPS 205 message-domain encoding as
`signM` before entering the internal verification algorithm. -/
def verifyM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    [DecidableEq prims.Y] (pk : PublicKey prims) (msg : List Byte)
    (sig : Signature p prims) : m Bool :=
  verifyInternalM prims (emptyContextMessage msg) sig pk

/-- The explicit-oracle, single-layer SLH-DSA signature algorithm. -/
def alg (prims : Primitives p) {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m]
    [Params.IsSingleLayer p] [HasQuery (publicHashSpec prims) m]
    [SampleableType prims.SkSeed]
    [SampleableType prims.SkPrf] [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.Y] :
    SignatureAlg m (List Byte) (PublicKey prims) (SecretKey prims) (Signature p prims) where
  keygen := keygenM prims
  sign _ sk msg := signM prims sk msg
  verify pk msg sig := verifyM prims pk msg sig

/-- The scheme in free public-randomness-plus-public-hash syntax.  This is the surface expected by
the generic `SignatureAlg` security games: the adversary sees the same public-hash queries, while a
runtime decides whether to interpret them as a lazy random oracle, a programmed oracle, or a
deterministic function. -/
def oracleAlg (prims : Primitives p) [Params.IsSingleLayer p]
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    SignatureAlg (OracleComp (unifSpec + publicHashSpec prims)) (List Byte)
      (PublicKey prims) (SecretKey prims) (Signature p prims) :=
  alg prims

/-- Runtime for the free scheme under a lazy random oracle with a caller-supplied initial cache.
Keeping the cache parameter explicit is the hook used by programmed-oracle reductions. -/
noncomputable def runtimeWithCache (prims : Primitives p) [DecidableEq prims.PkSeed]
    [DecidableEq prims.Y] [SampleableType prims.Y] [SampleableType (Bytes p.m)]
    (cache : PublicHash.Cache prims) :
    ProbCompRuntime (OracleComp (unifSpec + publicHashSpec prims)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle (PublicHash.randomOracle prims) cache
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Standard lazy-random-oracle runtime, initialized once with an empty cache around the complete
security experiment. -/
noncomputable def runtime (prims : Primitives p) [DecidableEq prims.PkSeed]
    [DecidableEq prims.Y] [SampleableType prims.Y] [SampleableType (Bytes p.m)] :
    ProbCompRuntime (OracleComp (unifSpec + publicHashSpec prims)) :=
  runtimeWithCache prims ∅

@[simp] theorem runtime_eq_runtimeWithCache_empty (prims : Primitives p)
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    [SampleableType prims.Y] [SampleableType (Bytes p.m)] :
    runtime prims = runtimeWithCache prims ∅ := rfl

/-- The cache-parametric random-oracle runtime commutes with mapping visible outputs. -/
theorem runtimeWithCache_evalDist_map (prims : Primitives p)
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    [SampleableType prims.Y] [SampleableType (Bytes p.m)]
    (cache : PublicHash.Cache prims) {α β : Type} (f : α → β)
    (mx : OracleComp (unifSpec + publicHashSpec prims) α) :
    (runtimeWithCache prims cache).evalDist (f <$> mx) =
      f <$> (runtimeWithCache prims cache).evalDist mx :=
  SPMFSemantics.withStateOracle_evalDist_map ..

/-- Bind-to-pure form used by the generic EUF-CMA freshness-drop game hop. -/
theorem runtimeWithCache_evalDist_bind_pure (prims : Primitives p)
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    [SampleableType prims.Y] [SampleableType (Bytes p.m)]
    (cache : PublicHash.Cache prims) {α β : Type}
    (mx : OracleComp (unifSpec + publicHashSpec prims) α) (f : α → β) :
    (runtimeWithCache prims cache).evalDist (mx >>= fun x => pure (f x)) =
      f <$> (runtimeWithCache prims cache).evalDist mx := by
  rw [show (mx >>= fun x => pure (f x)) = f <$> mx from (map_eq_bind_pure_comp _ f mx).symm,
    runtimeWithCache_evalDist_map]

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
