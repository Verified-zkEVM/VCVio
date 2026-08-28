/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Scheme

/-!
# Oracle-parametric SLH-DSA scheme canaries

These examples pin the internal FIPS 205 Algorithms 18–20 to their canonical explicit-query
programs. In particular, signing performs `H_msg`, FORS signing, FORS recovery from that exact
signature, and hypertree signing in order; it never regenerates the FORS public key.
-/

public section

namespace SLHDSA.SchemeTest

open OracleComp

variable {p : Params} (core : CorePrimitives p)

/-- FIPS 205 Algorithm 19 recovers the FORS public key from the generated signature before
hypertree signing. Replacing that recovery with `forsPkGenM` makes this canary fail. -/
example (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    (slhSignInternalM core msg sk addrnd :
      OracleComp (publicHashSpec core) (SignatureCore p core)) = (do
        let R := core.PRFmsg sk.skPrf addrnd msg
        let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
        let idxLeaf := (splitDigest p digest).2
        let md := (splitDigest p digest).1
        let fAdrs := forsAdrsOf idxLeaf
        let forsSig ← forsSignM core md sk.skSeed sk.pkSeed fAdrs
        let forsPk ← forsPkFromSigM core forsSig md sk.pkSeed fAdrs
        let htSig ← htSignM core forsPk sk.skSeed sk.pkSeed Adrs.zero 0 idxLeaf
        return (R, forsSig, htSig)) := by
  rfl

/-- Verification performs `H_msg`, FORS recovery, and hypertree recovery/comparison in order. -/
example [DecidableEq core.Y] (msg : List Byte) (sig : SignatureCore p core)
    (pk : PublicKeyCore core) :
    (slhVerifyInternalM core msg sig pk : OracleComp (publicHashSpec core) Bool) = (do
      let digest ← PublicHash.hmsg core sig.1 pk.pkSeed pk.pkRoot msg
      let idxLeaf := (splitDigest p digest).2
      let md := (splitDigest p digest).1
      let fAdrs := forsAdrsOf idxLeaf
      let forsPk ← forsPkFromSigM core sig.2.1 md pk.pkSeed fAdrs
      htVerifyM core forsPk sig.2.2 pk.pkSeed Adrs.zero 0 idxLeaf pk.pkRoot) := by
  rfl

/-- The established pure signer is literally the concrete public-hash interpretation of the
canonical program. -/
example (prims : Primitives p) (msg : List Byte) (sk : SecretKey prims)
    (addrnd : prims.Y) :
    slhSignInternal prims msg sk addrnd =
      simulateQ (PublicHash.impl prims)
        (slhSignInternalM prims.core msg sk addrnd :
          OracleComp (publicHashSpec prims.core) (Signature prims)) := by
  rfl

/-- An arbitrary total answer function interprets the canonical signer as the induced pure
API; no concrete hash implementation or cache is baked into the program. -/
example (answer : QueryImpl (publicHashSpec core) Id)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    simulateQ answer
        (slhSignInternalM core msg sk addrnd :
          OracleComp (publicHashSpec core) (SignatureCore p core)) =
      slhSignInternal (PublicHash.withPublicHash core answer) msg sk addrnd :=
  simulateQ_slhSignInternalM_withPublicHash core answer msg sk addrnd

/-- Query-preserving handlers commute with the whole internal signer. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core) (m := m)).toMonadHom
        (slhSignInternalM core msg sk addrnd :
          OracleComp (publicHashSpec core) (SignatureCore p core)) =
      (slhSignInternalM core msg sk addrnd : m (SignatureCore p core)) := by
  exact slhSignInternalM_natural core _ msg sk addrnd

/-- Key generation reuses the canonical hypertree root budget. -/
example (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    IsTotalQueryBound
      (slhKeygenInternalM core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core))
      (slhKeygenInternalQueryBound p) :=
  slhKeygenInternalM_isTotalQueryBound core skSeed skPrf pkSeed

/-- Verification accounts for `H_msg`, the supplied FORS paths, and the supplied hypertree path;
the bound is about structural queries rather than cache misses. -/
example [DecidableEq core.Y] (msg : List Byte) (sig : SignatureCore p core)
    (pk : PublicKeyCore core) :
    IsTotalQueryBound
      (slhVerifyInternalM core msg sig pk : OracleComp (publicHashSpec core) Bool)
      (slhVerifyInternalQueryBound p core sig) :=
  slhVerifyInternalM_isTotalQueryBound core msg sig pk

/-- The external hedged API retains its empty-context encoding and samples only `addrnd`; the
canonical explicit-query program remains behind the established pure internal wrapper. -/
example (prims : Primitives p) [SampleableType prims.Y]
    (sk : SecretKey prims) (msg : List Byte) :
    slhSign prims sk msg = (do
      let addrnd ← $ᵗ prims.Y
      return slhSignInternal prims (emptyContextMessage msg) sk addrnd) := by
  rfl

/-- One fixed total public-hash table gives end-to-end internal correctness through the canonical
key-generation, signing, and verification programs. -/
example (answer : QueryImpl (publicHashSpec core) Id) [DecidableEq core.Y]
    (msg : List Byte) (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) (addrnd : core.Y) :
    simulateQ answer (do
      let (pk, sk) ← slhKeygenInternalM core skSeed skPrf pkSeed
      let sig ← slhSignInternalM core msg sk addrnd
      slhVerifyInternalM core msg sig pk) = true :=
  simulateQ_slhVerifyInternalM_slhSignInternalM_withPublicHash
    core answer msg skSeed skPrf pkSeed addrnd

end SLHDSA.SchemeTest
