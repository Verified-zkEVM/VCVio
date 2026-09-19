/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CountedRom

/-!
# SLH-DSA counted random-oracle canaries

Elaboration pins for the cost function of `HashSig.SLHDSA.Security.CountedRom`'s
`countedRomImpl`: a private-sampling query is charged `0` and forwarded to `unifFwdImpl`, and a
public-hash query is charged `1` and forwarded to `PublicHash.randomOracle`.  Each is a program
equality naming the charge and the handler, restated here from `countedRomImpl_inl` and
`countedRomImpl_inr` so that a change to either charge fails a pin outside the library module.

## Nothing here is runnable

`countedRomImpl` interprets into `ProbComp` through a lazily sampled cache and is `noncomputable`,
as is everything built on it, so the two equalities are pinned by elaboration only.  The file has
no `main` and is built by the `HashSigTest` library glob alone.

## What the checks cannot catch

* **Whether the count is the right budget.**  The pins fix the charge per query; that key
  generation, signing and verification are charged alongside the forger is a property of
  `romGameCore` and `HasHashQueryBound`, which nothing here reads.
* **Anything about a probability.**  `romForgeAdvantage` and the success bit of
  `countedRomExperiment` are `ℝ≥0∞`- and `ProbComp`-valued; no fixture can run them.
-/

public section

namespace SLHDSA.CountedRomTest

open Security OracleComp OracleSpec

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

open scoped Classical in
/-- A private-sampling query is charged `0` and forwarded to `unifFwdImpl`. -/
example (i : unifSpec.Domain) :
    countedRomImpl core (Sum.inl i) = (do
      AddWriterT.addTell (M := StateT (PublicHash.Cache core) ProbComp) (0 : ℕ)
      liftM (unifFwdImpl (publicHashSpec core) i)) :=
  countedRomImpl_inl core i

open scoped Classical in
/-- A public-hash query is charged `1` and forwarded to the shared lazy random oracle. -/
example (q : (publicHashSpec core).Domain) :
    countedRomImpl core (Sum.inr q) = (do
      AddWriterT.addTell (M := StateT (PublicHash.Cache core) ProbComp) (1 : ℕ)
      liftM (PublicHash.randomOracle core q)) :=
  countedRomImpl_inr core q

end SLHDSA.CountedRomTest
