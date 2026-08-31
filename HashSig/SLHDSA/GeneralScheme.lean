/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.HypertreeGeneral
public import HashSig.SLHDSA.Scheme

/-!
# General internal SLH-DSA scheme (FIPS 205 Algorithms 18--20)

This module is the arbitrary-`d` construction boundary.  It retains every output of `H_msg`, uses
the digest-derived FORS address, and invokes the general hypertree from the typed layer-zero
position.  Key generation computes the root of the top-layer XMSS tree.

The older `SLHDSA.Scheme` API remains available as an explicit one-layer compatibility surface
while its downstream security consumers migrate to this construction.

## References

- NIST FIPS 205, Section 9, Algorithms 18--20
-/

@[expose] public section

namespace SLHDSA.GeneralScheme

open OracleComp

/-- Structured internal signature with an intrinsically `d`-layer hypertree component. -/
structure SignatureCore (vp : ValidatedParams) (core : CorePrimitives vp.params) where
  randomness : core.Y
  fors : ForsSigCore vp.params core
  hypertree : GeneralHypertree.Signature vp core

/-- FIPS Algorithm 18: derive the public root from layer `d - 1`, tree zero. -/
def keygenInternalM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    m (PublicKeyCore core × SecretKeyCore core) := do
  let pkRoot ← GeneralHypertree.rootM vp core skSeed pkSeed
  return (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- FIPS Algorithm 19: randomized internal signing for every validated parameter set. -/
def signInternalM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    m (SignatureCore vp core) := do
  let R := core.PRFmsg sk.skPrf addrnd msg
  let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
  let parts := splitDigest vp.params digest
  let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
  let forsPk ← forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
  let htSig ← GeneralHypertree.signM vp core forsPk sk.skSeed sk.pkSeed parts
  return ⟨R, forsSig, htSig⟩

/-- FIPS Algorithm 20: recover the FORS and hypertree roots along the same typed position
trajectory used by signing. -/
def verifyInternalM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore vp core) (pk : PublicKeyCore core) : m Bool := do
  let digest ← PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg
  let parts := splitDigest vp.params digest
  let forsPk ← forsPkFromSigM core sig.fors parts.md.toList pk.pkSeed parts.forsAdrs
  GeneralHypertree.verifyM vp core forsPk sig.hypertree pk.pkSeed parts pk.pkRoot

/-! ## Naturality -/

private theorem queryHom_hmsg {p : Params} (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    F.toMonadHom (PublicHash.hmsg core r pkSeed pkRoot msg) =
      PublicHash.hmsg core r pkSeed pkRoot msg := by
  change F.toMonadHom
      (query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)) =
    query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)
  exact HasQuery.map_query F _

/-- Query-preserving monad morphisms commute with general internal key generation. -/
theorem keygenInternalM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    F.toMonadHom (keygenInternalM vp core skSeed skPrf pkSeed) =
      keygenInternalM vp core skSeed skPrf pkSeed := by
  simp [keygenInternalM, GeneralHypertree.rootM_natural vp core F]

/-- Query-preserving monad morphisms commute with general internal signing. -/
theorem signInternalM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    F.toMonadHom (signInternalM vp core msg sk addrnd) =
      signInternalM vp core msg sk addrnd := by
  simp [signInternalM, queryHom_hmsg core F, forsSignM_natural core F,
    forsPkFromSigM_natural core F, GeneralHypertree.signM_natural vp core F]

/-- Query-preserving monad morphisms commute with general internal verification. -/
theorem verifyInternalM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sig : SignatureCore vp core) (pk : PublicKeyCore core) :
    F.toMonadHom (verifyInternalM vp core msg sig pk) =
      verifyInternalM vp core msg sig pk := by
  simp [verifyInternalM, queryHom_hmsg core F, forsPkFromSigM_natural core F,
    GeneralHypertree.verifyM_natural vp core F]

/-! ## Pure deterministic interpretations -/

def keygenInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    PublicKeyCore prims.core × SecretKeyCore prims.core :=
  simulateQ (PublicHash.impl prims)
    (keygenInternalM vp prims.core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec prims.core)
        (PublicKeyCore prims.core × SecretKeyCore prims.core))

def signInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    SignatureCore vp prims.core :=
  simulateQ (PublicHash.impl prims)
    (signInternalM vp prims.core msg sk addrnd :
      OracleComp (publicHashSpec prims.core) (SignatureCore vp prims.core))

def verifyInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y]
    (msg : List Byte) (sig : SignatureCore vp prims.core) (pk : PublicKeyCore prims.core) : Bool :=
  simulateQ (PublicHash.impl prims)
    (verifyInternalM vp prims.core msg sig pk : OracleComp (publicHashSpec prims.core) Bool)

end SLHDSA.GeneralScheme
