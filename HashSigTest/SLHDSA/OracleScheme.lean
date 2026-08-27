/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.SchemeOracle

/-!
# End-to-end canary for the explicit-oracle SLH-DSA slice

This small parameter set elaborates key generation, FORS, WOTS+, XMSS signing, and verification
through the explicit public-hash syntax.  The example is a regression canary rather than a
security claim, an executable acceptance proof, or a FIPS-approved parameter set.
-/

@[expose] public section

open OracleComp

namespace SLHDSA.OracleSchemeTest

/-- A tiny single-layer parameter set whose complete trees are practical to reduce in a test. -/
def toyParams : Params where
  n := 1
  h := 1
  d := 1
  hp := 1
  a := 1
  k := 1
  lgw := 1

def boolByte (b : Bool) : Byte :=
  if b then 1 else 0

/-- A deliberately simple deterministic primitive bundle for exercising control flow and address
plumbing.  It is not intended to satisfy any cryptographic property. -/
def toyPrimitives : Primitives toyParams where
  PkSeed := Bool
  SkSeed := Bool
  SkPrf := Bool
  Y := Bool
  F := fun pk _ x => xor pk x
  H := fun pk _ left right => xor pk (xor left (!right))
  Tl := fun pk _ xs => xs.foldl xor pk
  PRF := fun pk sk _ => xor pk sk
  PRFmsg := fun skPrf addrnd _ => xor skPrf addrnd
  Hmsg := fun _ _ _ _ => #v[0, 0]
  yToBytes := fun y => #v[boolByte y]

instance : DecidableEq toyPrimitives.Y := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq toyPrimitives.PkSeed := inferInstanceAs (DecidableEq Bool)
noncomputable instance : SampleableType toyPrimitives.Y :=
  SampleableType.ofFintype Bool

instance : Params.IsSingleLayer toyParams where
  d_eq_one := rfl
  hp_eq_h := rfl

/-- The complete explicit-oracle keygen/sign/verify program. -/
def roundTrip : OracleComp (publicHashSpec toyPrimitives) Bool := do
  let (pk, sk) ← OracleScheme.keygenInternalM toyPrimitives false false false
  let sig ← OracleScheme.signInternalM toyPrimitives [0] sk false
  OracleScheme.verifyInternalM toyPrimitives [0] sig pk

/-- Kernel-visible type canary for the complete explicit-oracle program. -/
example : OracleComp (publicHashSpec toyPrimitives) Bool := roundTrip

/-- The same vertical slice under the concrete lazy-random-oracle capability.  Its type exposes
the one cache that the enclosing experiment must initialize and thread through the whole run. -/
noncomputable def roundTripRandomOracle :
    StateT (PublicHash.Cache toyPrimitives) ProbComp Bool := by
  letI := PublicHash.randomOracleHasQuery toyPrimitives
  exact do
    let (pk, sk) ← OracleScheme.keygenInternalM toyPrimitives false false false
    let sig ← OracleScheme.signInternalM toyPrimitives [0] sk false
    OracleScheme.verifyInternalM toyPrimitives [0] sig pk

/-- The enclosing experiment initializes the cache once, around the complete program. -/
noncomputable def runRoundTripRandomOracle :
    ProbComp (Bool × PublicHash.Cache toyPrimitives) :=
  roundTripRandomOracle.run ∅

end SLHDSA.OracleSchemeTest
