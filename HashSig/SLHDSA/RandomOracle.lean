/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Scheme
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

/-!
# SLH-DSA in the public-hash random-oracle model

This file lifts the canonical internal SLH-DSA programs into one external signature algorithm.
Fresh seeds and the signing randomizer are lifted from `ProbComp`; `H_msg` and every tweakable
hash remain explicit `HasQuery (publicHashSpec core)` calls. The canonical random-oracle
specialization uses one lazy cache for the complete experiment. Consequently key generation,
the adversary, every signing-oracle call, and final verification all see the same public-hash
table.

The model intentionally excludes the secret operations `PRF` and `PRF_msg`, which remain pure
fields of `CorePrimitives`. Thus this is a public-hash ROM formalization, not a claim that every
named SLH-DSA operation is an independent raw-hash oracle.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}

/-! ### Canonical external algorithms -/

/-- External key generation: sample the three FIPS 205 seeds, then run the canonical internal
explicit-query program. -/
def slhKeygenM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] : m (PublicKeyCore core × SecretKeyCore core) := do
  let skSeed ← (monadLift ($ᵗ core.SkSeed) : m core.SkSeed)
  let skPrf ← (monadLift ($ᵗ core.SkPrf) : m core.SkPrf)
  let pkSeed ← (monadLift ($ᵗ core.PkSeed) : m core.PkSeed)
  slhKeygenInternalM core skSeed skPrf pkSeed

/-- External hedged signing for the empty-context API: sample `addrnd`, encode the external
message, then run the canonical internal explicit-query signer. -/
def slhSignM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
    [SampleableType core.Y] (sk : SecretKeyCore core) (msg : List Byte) :
    m (SignatureCore p core) := do
  let addrnd ← (monadLift ($ᵗ core.Y) : m core.Y)
  slhSignInternalM core (emptyContextMessage msg) sk addrnd

/-- External empty-context verification via the canonical internal explicit-query verifier. -/
def slhVerifyM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (pk : PublicKeyCore core) (msg : List Byte) (sig : SignatureCore p core) : m Bool :=
  slhVerifyInternalM core (emptyContextMessage msg) sig pk

/-- The single canonical oracle-parametric SLH-DSA signature scheme. Its algorithms are generic
over the public-randomness lift and the public-hash query capability. -/
def slhdsaAlgM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y] [DecidableEq core.Y] :
    SignatureAlg m (List Byte) (PublicKeyCore core) (SecretKeyCore core)
      (SignatureCore p core) where
  keygen := slhKeygenM core
  sign _pk sk msg := slhSignM core sk msg
  verify pk msg sig := slhVerifyM core pk msg sig

/-- The external scheme is natural under morphisms that preserve both the public-hash query
capability and the designated lift of fresh public randomness. -/
theorem map_slhdsaAlgM (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y] [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (hLift : HasQuery.PreservesProbCompLift (m := m) (n := n) F.toMonadHom) :
    SignatureAlg.map F.toMonadHom (slhdsaAlgM (m := m) core) =
      slhdsaAlgM (m := n) core := by
  apply SignatureAlg.ext
  · simp [slhdsaAlgM, slhKeygenM, hLift ($ᵗ core.SkSeed), hLift ($ᵗ core.SkPrf),
      hLift ($ᵗ core.PkSeed), slhKeygenInternalM_natural core F]
  · funext pk sk msg
    simp [slhdsaAlgM, slhSignM, hLift ($ᵗ core.Y), slhSignInternalM_natural core F]
  · funext pk msg sig
    exact slhVerifyInternalM_natural core F (emptyContextMessage msg) sig pk

/-! ### Deterministic compatibility specialization -/

/-- Interpret the combined uniform/public-hash syntax by keeping uniform samples probabilistic
and answering public hashes with the concrete functions in `prims`. -/
def concretePublicHashImpl (prims : Primitives p) :
    QueryImpl (unifSpec + publicHashSpec prims.core) ProbComp :=
  unifFwdAnswerImpl (PublicHash.impl prims)

/-- The established concrete `ProbComp` scheme is the deterministic-public-hash interpretation
of the single canonical oracle-parametric scheme. -/
theorem map_slhdsaAlgM_concrete (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    SignatureAlg.map (simulateQ' (concretePublicHashImpl prims))
      (slhdsaAlgM (m := OracleComp (unifSpec + publicHashSpec prims.core)) prims.core) =
        slhdsaAlg prims := by
  let _ : HasQuery (publicHashSpec prims.core) ProbComp :=
    ⟨fun q => liftM (PublicHash.impl prims q)⟩
  let F : HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (unifSpec + publicHashSpec prims.core)) ProbComp :=
    { toMonadHom := simulateQ' (concretePublicHashImpl prims)
      map_query' := fun q => by
        simpa [concretePublicHashImpl, unifFwdAnswerImpl] using
          (QueryImpl.simulateQ_add_liftM_query_right
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp))
            ((PublicHash.impl prims).liftTarget ProbComp) q) }
  have hLift : HasQuery.PreservesProbCompLift F.toMonadHom := by
    intro α oa
    change simulateQ (concretePublicHashImpl prims)
      (liftM oa : OracleComp (unifSpec + publicHashSpec prims.core) α) = oa
    rw [concretePublicHashImpl, unifFwdAnswerImpl,
      QueryImpl.simulateQ_add_liftM_left, HasQuery.toQueryImpl_eq_id', simulateQ_id']
  rw [map_slhdsaAlgM prims.core F hLift]
  have hImpl :
      (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp)) =
        (PublicHash.impl prims).liftTarget ProbComp := by
    funext q
    rfl
  have hKeygen : ∀ skSeed skPrf pkSeed,
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp))
          (slhKeygenInternalM prims.core skSeed skPrf pkSeed :
            OracleComp (publicHashSpec prims.core) _) =
        pure (slhKeygenInternal prims skSeed skPrf pkSeed) := by
    intro skSeed skPrf pkSeed
    rw [hImpl, simulateQ_liftTarget]
    rfl
  have hSign : ∀ msg sk addrnd,
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp))
          (slhSignInternalM prims.core msg sk addrnd :
            OracleComp (publicHashSpec prims.core) _) =
        pure (slhSignInternal prims msg sk addrnd) := by
    intro msg sk addrnd
    rw [hImpl, simulateQ_liftTarget]
    rfl
  have hVerify : ∀ msg sig pk,
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp))
          (slhVerifyInternalM prims.core msg sig pk :
            OracleComp (publicHashSpec prims.core) _) =
        pure (slhVerifyInternal prims msg sig pk) := by
    intro msg sig pk
    rw [hImpl, simulateQ_liftTarget]
    rfl
  apply SignatureAlg.ext
  · simp [slhdsaAlgM, slhdsaAlg, slhKeygenM, slhKeygen, hKeygen,
      ← slhKeygenInternalM_natural prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))]
  · funext pk sk msg
    simp [slhdsaAlgM, slhdsaAlg, slhSignM, slhSign, hSign,
      ← slhSignInternalM_natural prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))]
  · funext pk msg sig
    simp [slhdsaAlgM, slhdsaAlg, slhVerifyM, slhVerify, hVerify,
      ← slhVerifyInternalM_natural prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))]

/-! ### One shared lazy-random-oracle runtime -/

namespace PublicHash

open scoped Classical in
/-- Runtime for the combined fresh-uniform/public-hash world, starting from a supplied public-hash
cache. This is the programming hook for reductions. The cache is installed once around the whole
experiment; it is not reset between scheme components or signing-oracle calls. -/
noncomputable def runtimeWithCache (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)]
    (cache : PublicHash.Cache core) :
    ProbCompRuntime (OracleComp (unifSpec + publicHashSpec core)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := PublicHash.randomOracle core) cache
  toProbCompLift := ProbCompLift.ofMonadLift _

open scoped Classical in
/-- Standard SLH-DSA public-hash ROM runtime, starting from the empty cache. -/
noncomputable def runtime (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)] :
    ProbCompRuntime (OracleComp (unifSpec + publicHashSpec core)) :=
  runtimeWithCache core ∅

@[simp] theorem runtime_eq_runtimeWithCache_empty (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)] :
    PublicHash.runtime core = PublicHash.runtimeWithCache core ∅ := rfl

/-- The shared-cache runtime commutes with mapping a pure function over a surface computation. -/
theorem runtimeWithCache_evalSPMF_map (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)]
    (cache : PublicHash.Cache core) {α β : Type} (f : α → β)
    (mx : OracleComp (unifSpec + publicHashSpec core) α) :
    (PublicHash.runtimeWithCache core cache).evalSPMF (f <$> mx) =
      f <$> (PublicHash.runtimeWithCache core cache).evalSPMF mx :=
  SPMFSemantics.withStateOracle_evalSPMF_map ..

/-- The shared-cache runtime pulls a final pure-returning bind through observation. This is the
runtime law used by generic `SignatureAlg` EUF-CMA game hops. -/
theorem runtimeWithCache_evalSPMF_bind_pure (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)]
    (cache : PublicHash.Cache core) {α β : Type}
    (mx : OracleComp (unifSpec + publicHashSpec core) α) (f : α → β) :
    (PublicHash.runtimeWithCache core cache).evalSPMF (mx >>= fun x => pure (f x)) =
      f <$> (PublicHash.runtimeWithCache core cache).evalSPMF mx := by
  rw [show (mx >>= fun x => pure (f x)) = f <$> mx from
    (map_eq_bind_pure_comp _ f mx).symm, runtimeWithCache_evalSPMF_map]

/-- Empty-cache instance of `runtimeWithCache_evalSPMF_bind_pure`. -/
theorem runtime_evalSPMF_bind_pure (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)]
    {α β : Type} (mx : OracleComp (unifSpec + publicHashSpec core) α) (f : α → β) :
    (PublicHash.runtime core).evalSPMF (mx >>= fun x => pure (f x)) =
      f <$> (PublicHash.runtime core).evalSPMF mx :=
  runtimeWithCache_evalSPMF_bind_pure core ∅ mx f

end PublicHash

/-! ### End-to-end shared-ROM completeness -/

open scoped Classical in
/-- The canonical oracle-parametric SLH-DSA scheme is perfectly complete under the runtime that
threads one lazy public-hash random-oracle cache through the entire experiment.

The proof uses the generic mixed-uniform/random-oracle probability-one bridge. It reduces the
lazy oracle to every fixed total hash table and then applies deterministic correctness. -/
theorem slhdsaAlgM_perfectlyComplete (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y]
    [SampleableType (Bytes p.m)] :
    (slhdsaAlgM (m := OracleComp (unifSpec + publicHashSpec core)) core).PerfectlyComplete
      (PublicHash.runtime core) := by
  let _ : ∀ q : (publicHashSpec core).Domain,
      SampleableType ((publicHashSpec core).Range q) := fun q => by
    cases q <;> infer_instance
  intro msg
  let alg := slhdsaAlgM (m := OracleComp (unifSpec + publicHashSpec core)) core
  let oa : OracleComp (unifSpec + publicHashSpec core) Bool := do
    let (pk, sk) ← alg.keygen
    let sig ← alg.sign pk sk msg
    alg.verify pk msg sig
  change Pr[= true | (PublicHash.runtime core).evalSPMF oa] = 1
  unfold PublicHash.runtime PublicHash.runtimeWithCache ProbCompRuntime.evalSPMF
    SPMFSemantics.evalSPMF SemanticsVia.denote SPMFSemantics.withStateOracle
  rw [probOutput_evalSPMF]
  change Pr[= true |
    (simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core) oa).run' ∅] = 1
  rw [← probEvent_eq_eq_probOutput, StateT.run', probEvent_map]
  apply (OracleComp.probEvent_eq_one_simulateQ_unifFwdImpl_add_randomOracle_run_iff
    (oa := oa) (preexisting_cache := (∅ : PublicHash.Cache core))
    (fun b => b = true)).2
  intro f _hf
  let prims := PublicHash.withPublicHash core f
  have hAlg := map_slhdsaAlgM_concrete prims
  have hAlg' : SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg =
      slhdsaAlg prims := by
    simpa [alg, prims, concretePublicHashImpl] using hAlg
  rw [probEvent_eq_eq_probOutput]
  simp only [oa, simulateQ_bind]
  change Pr[= true | do
    let (pk, sk) ←
      (SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg).keygen
    let sig ←
      (SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg).sign pk sk msg
    (SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg).verify pk msg sig] = 1
  rw [hAlg']
  exact slhdsaAlg_perfectlyComplete prims msg

end SLHDSA
