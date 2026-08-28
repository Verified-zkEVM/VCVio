/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import HashSig.SLHDSA.RandomOracle

/-!
# Shared-ROM SLH-DSA canaries

These examples pin the final architecture: one canonical external scheme, the old concrete
scheme as its deterministic public-hash interpretation, and one cache around the full ROM
experiment.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.RandomOracleTest

variable {p : Params} (core : CorePrimitives p)

/-- The external scheme is definitionally assembled from the canonical monadic components. -/
example {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m]
    [HasQuery (publicHashSpec core) m]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y] [DecidableEq core.Y] :
    (slhdsaAlgM (m := m) core).keygen = slhKeygenM core := rfl

/-- The former concrete API is a proved specialization, not a parallel implementation. -/
example (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    SignatureAlg.map (simulateQ' (concretePublicHashImpl prims))
      (slhdsaAlgM (m := OracleComp (unifSpec + publicHashSpec prims.core)) prims.core) =
        slhdsaAlg prims :=
  map_slhdsaAlgM_concrete prims

/-- The standard ROM runtime is exactly the cache-parametric runtime started empty. -/
example [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)] :
    PublicHash.runtime core = PublicHash.runtimeWithCache core ∅ := rfl

/-- End-to-end completeness uses the single shared-cache runtime. -/
example [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y]
    [SampleableType (Bytes p.m)] :
    (slhdsaAlgM (m := OracleComp (unifSpec + publicHashSpec core)) core).PerfectlyComplete
      (PublicHash.runtime core) :=
  slhdsaAlgM_perfectlyComplete core

/-- The shared-cache observation law is directly usable by the generic adaptive EUF-CMA API for
an arbitrary adversary. In particular, the game wraps adversarial public-hash queries, adaptive
signing-oracle calls, and final verification in the same runtime invocation. -/
example [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y]
    [SampleableType (Bytes p.m)]
    (adv : SignatureAlg.unforgeableAdv
      (slhdsaAlgM (m := OracleComp (unifSpec + publicHashSpec core)) core)) :
    adv.advantage (PublicHash.runtime core) ≤
      Pr[= true | SignatureAlg.unforgeableExpNoFresh (PublicHash.runtime core) adv] :=
  adv.advantage_le_unforgeableExpNoFresh (PublicHash.runtime core)
    (fun f mx => PublicHash.runtime_evalSPMF_bind_pure core mx f)

end SLHDSA.RandomOracleTest
