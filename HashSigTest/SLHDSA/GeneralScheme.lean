/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.GeneralScheme

/-!
# General internal-scheme canaries

These equations pin the general Algorithms 18--20 composition boundary: top-layer key generation,
digest-derived FORS addressing, and the arbitrary-`d` hypertree call.
-/

public section

namespace SLHDSA.GeneralSchemeTest

open OracleComp

variable (vp : ValidatedParams) (core : CorePrimitives vp.params)

/-- The structured scheme signature carries exactly `d` XMSS signatures. -/
example (sig : GeneralScheme.SignatureCore vp core) :
    sig.hypertree.toArray.size = vp.params.d := sig.hypertree.size_toArray

/-- Algorithm 18 delegates root generation to the top-layer general hypertree. -/
example (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) = (do
        let pkRoot ← GeneralHypertree.rootM vp core skSeed pkSeed
        return (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)) := by
  rfl

/-- Algorithm 19 retains every digest output and passes the typed parts to the general
hypertree, rather than resetting the tree address to zero. -/
example (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    (GeneralScheme.signInternalM vp core msg sk addrnd :
      OracleComp (publicHashSpec core) (GeneralScheme.SignatureCore vp core)) = (do
        let R := core.PRFmsg sk.skPrf addrnd msg
        let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
        let parts := splitDigest vp.params digest
        let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
        let forsPk ←
          forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
        let htSig ← GeneralHypertree.signM vp core forsPk sk.skSeed sk.pkSeed parts
        return ⟨R, forsSig, htSig⟩) := by
  rfl

/-- Algorithm 20 follows the same digest-derived FORS and hypertree schedule. -/
example [DecidableEq core.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    (GeneralScheme.verifyInternalM vp core msg sig pk :
      OracleComp (publicHashSpec core) Bool) = (do
        let digest ← PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg
        let parts := splitDigest vp.params digest
        let forsPk ← forsPkFromSigM core sig.fors parts.md.toList pk.pkSeed parts.forsAdrs
        GeneralHypertree.verifyM vp core forsPk sig.hypertree pk.pkSeed parts pk.pkRoot) := by
  rfl

end SLHDSA.GeneralSchemeTest
