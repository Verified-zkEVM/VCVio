/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.JointRom

/-!
# SLH-DSA joint-run budget guard

`HashSig.SLHDSA.Security.JointRom` relates the two SLH-DSA query budgets by the implication
`hasSignQueryBound_of_hasHashQueryBound`: a hash-query budget is also a signing-query budget.
`not_forall_signBound_le_hashBound` guards the reading of that relation as an inequality between
the two budget parameters, by refuting it: for any adversary with a hash budget at all,
`∀ qs qh, HasSignQueryBound adv qs → HasHashQueryBound adv qh → qs ≤ qh` is false.  Both
predicates are upper bounds, so a signing budget can be raised freely while the hash budget stays
put, and a side obligation written as `qs ≤ qh` on the parameters would be unprovable.  The
inequality that does hold is `sInf_signBound_le_sInf_hashBound`, between the least witnesses.

## Nothing here is runnable

The joint run interprets into `ProbComp` through a lazily sampled cache and is `noncomputable`,
as is everything built on it, so the refutation is checked by elaboration only.  The file has no
`main` and is built by the `HashSigTest` library glob alone.

## What the check cannot catch

* **Whether the implication is the right side obligation.**  The refutation rules out one wrong
  statement; that `hasSignQueryBound_of_hasHashQueryBound` is what a separated bound needs is a
  property of the bound, which nothing here reads.
* **Anything about a probability.**  No mass of any event of the joint run is evaluated.
-/

public section

namespace SLHDSA.JointRomTest

open Security OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

/-- The oracle family the whole experiment runs in: private sampling together with the public
hash. -/
local notation "romSpec" => unifSpec + publicHashSpec core

/-- **No inequality between the two budget parameters holds.**  Both `HasSignQueryBound` and
`HasHashQueryBound` are upper bounds, so `hasSignQueryBound_mono` raises any signing budget above
any given hash budget.  The content of the relation is the implication
`hasSignQueryBound_of_hasHashQueryBound`, and the inequality that does hold is between the least
witnesses, `sInf_signBound_le_sInf_hashBound`. -/
theorem not_forall_signBound_le_hashBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q : ℕ)
    (hq : HasHashQueryBound core adv q) :
    ¬ ∀ qs qh : ℕ, HasSignQueryBound core adv qs → HasHashQueryBound core adv qh → qs ≤ qh := by
  intro h
  have : q + 1 ≤ q :=
    h (q + 1) q (hasSignQueryBound_mono core adv (Nat.le_succ q)
      (hasSignQueryBound_of_hasHashQueryBound core adv q hq)) hq
  omega

end SLHDSA.JointRomTest
