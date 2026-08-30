/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Scheme

/-!
# Oracle-parametric SLH-DSA scheme canaries

These examples cover the two observable internal FIPS 205 schedules. Signing performs `H_msg`,
FORS signing, recovery from that exact signature, and hypertree signing in order; it never
regenerates the FORS public key.
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

/-- Verification first rejects malformed authentication-path lengths, then performs `H_msg`,
FORS recovery, and hypertree recovery/comparison in order. -/
example [DecidableEq core.Y] (msg : List Byte) (sig : SignatureCore p core)
    (pk : PublicKeyCore core) :
    (slhVerifyInternalM core msg sig pk : OracleComp (publicHashSpec core) Bool) =
      if sig.IsWellFormed then do
        let digest ← PublicHash.hmsg core sig.1 pk.pkSeed pk.pkRoot msg
        let idxLeaf := (splitDigest p digest).2
        let md := (splitDigest p digest).1
        let fAdrs := forsAdrsOf idxLeaf
        let forsPk ← forsPkFromSigM core sig.2.1 md pk.pkSeed fAdrs
        htVerifyM core forsPk sig.2.2 pk.pkSeed Adrs.zero 0 idxLeaf pk.pkRoot
      else
        pure false := by
  rfl

/-- Replace the `d = 1` XMSS authentication path by the empty list. -/
def withEmptyXmssAuthPath (sig : SignatureCore p core) : SignatureCore p core :=
  (sig.1, sig.2.1, (sig.2.2.1, []))

/-- Emptying a positive-height XMSS path violates the fixed signature format. -/
theorem withEmptyXmssAuthPath_not_isWellFormed (sig : SignatureCore p core)
    (hhp : p.hp ≠ 0) : ¬ (withEmptyXmssAuthPath core sig).IsWellFormed := by
  intro hformat
  apply hhp
  simpa [withEmptyXmssAuthPath] using hformat.2.symm

/-- Replace one FORS authentication path by the empty list. -/
def withEmptyForsAuthPath (sig : SignatureCore p core) (target : Fin p.k) :
    SignatureCore p core :=
  let forsSig := Vector.ofFn fun i : Fin p.k =>
    if i = target then ((sig.2.1[i.val]).1, []) else sig.2.1[i.val]
  (sig.1, forsSig, sig.2.2)

/-- Emptying one positive-height FORS path violates the fixed signature format. -/
theorem withEmptyForsAuthPath_not_isWellFormed (sig : SignatureCore p core)
    (target : Fin p.k) (ha : p.a ≠ 0) :
    ¬ (withEmptyForsAuthPath core sig target).IsWellFormed := by
  intro hformat
  apply ha
  have htarget := hformat.1 target
  simpa [withEmptyForsAuthPath] using htarget.symm

/-- The format guard rejects a malformed XMSS path without reaching `H_msg`. -/
example [DecidableEq core.Y] (msg : List Byte) (sig : SignatureCore p core)
    (pk : PublicKeyCore core) (hhp : p.hp ≠ 0) :
    slhVerifyInternalM core msg (withEmptyXmssAuthPath core sig) pk =
      (pure false : OracleComp (publicHashSpec core) Bool) := by
  exact slhVerifyInternalM_of_not_isWellFormed core msg _ pk
    (withEmptyXmssAuthPath_not_isWellFormed core sig hhp)

/-- The same format guard rejects a malformed FORS path before reaching `H_msg`. -/
example [DecidableEq core.Y] (msg : List Byte) (sig : SignatureCore p core)
    (pk : PublicKeyCore core) (target : Fin p.k) (ha : p.a ≠ 0) :
    slhVerifyInternalM core msg (withEmptyForsAuthPath core sig target) pk =
      (pure false : OracleComp (publicHashSpec core) Bool) := by
  exact slhVerifyInternalM_of_not_isWellFormed core msg _ pk
    (withEmptyForsAuthPath_not_isWellFormed core sig target ha)

/-- Honest signing always produces the fixed authentication-path lengths. -/
example (prims : Primitives p) (msg : List Byte) (sk : SecretKeyCore prims.core)
    (addrnd : prims.Y) :
    (slhSignInternal prims msg sk addrnd).IsWellFormed :=
  slhSignInternal_isWellFormed prims msg sk addrnd

end SLHDSA.SchemeTest
