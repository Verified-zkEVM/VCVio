/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Concrete.Instance
public import HashSig.SLHDSA.SchemeOracle

/-!
# Concrete producer canary for oracle-parametric SLH-DSA

This file checks that the free public-hash syntax and its lazy-random-oracle runtime specialize to
the repository's real SHA2-128-24 carrier bundle.  It is an elaboration canary, not a claim that
the random oracle is the concrete SHA-2 implementation.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA.Concrete.OracleTest

instance : DecidableEq shaPrimitives.PkSeed :=
  inferInstanceAs (DecidableEq (Bytes 16))

noncomputable example :
    SignatureAlg (OracleComp (unifSpec + publicHashSpec shaPrimitives)) (List Byte)
      (PublicKey shaPrimitives) (SecretKey shaPrimitives)
      (OracleScheme.Signature slhdsaSha2_128_24 shaPrimitives) :=
  OracleScheme.oracleAlg shaPrimitives

noncomputable example :
    ProbCompRuntime (OracleComp (unifSpec + publicHashSpec shaPrimitives)) :=
  OracleScheme.runtime shaPrimitives

end SLHDSA.Concrete.OracleTest
