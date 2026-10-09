/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

/-!
# Basic Constructions of Simulation Oracles

This file defines a number of basic simulation oracles, as well as operations to combine them.

## `preInsert` and `postInsert`

The two main building blocks for instrumented `QueryImpl` values are `preInsert` and
`postInsert`. Both take a base `QueryImpl spec m` and a per-query side effect, and produce
a new `QueryImpl spec n` that wraps the base with that side effect:

* `preInsert  so nx` runs `nx t` *before* the handler `so t`. The side effect happens
  unconditionally, including when the handler later fails.
* `postInsert so nx` runs `nx t u` *after* the handler returns response `u`, so the side
  effect can depend on the response and is skipped when the handler fails.

Both come with a complete generic theory, parametric in a projection
`proj : ∀ {γ}, n γ → m γ` that strips the instrumentation: `proj_simulateQ_preInsert`,
`probFailure_proj_simulateQ_preInsert`, `NeverFail_proj_simulateQ_preInsert_iff`,
`evalSPMF_proj_simulateQ_preInsert`, `probOutput_proj_simulateQ_preInsert`,
`support_proj_simulateQ_preInsert`, `finSupport_proj_simulateQ_preInsert`, and the
induction principle `simulateQ_preInsert.induct` (with `postInsert` analogues). Query-bound
transfer through these wrappers lives in `QueryTracking/QueryBound.lean`.

Most of the wrappers in `QueryTracking/` (`withTraceBefore`, `withTrace`,
`withTraceAppendBefore`, `withTraceAppend`, `withCost`, `withCounting`, `withAddCost`,
`withUnitCost`, `withLogging`, `appendInputLog`) bottom out at these combinators. New
instrumentation should follow the same pattern when its shape is "for each query, run a
side effect and delegate" — wrappers whose control flow is conditional on external state
or the would-be response (cache-on-hit, seed fallback, budget gating) genuinely need a
custom `QueryImpl` and stay outside this hierarchy.
-/

@[expose] public section

open OracleSpec OracleComp Prod Sum

universe u v w

namespace QueryImpl

section insertPre

variable {m : Type u → Type v} {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    {ι : Type*} {spec : OracleSpec ι} {α β : Type u}

/-- A `preInsert` instrumentation preserves failure probability for any base monad with
`[MonadLiftT m SPMF]`, given the projection bundle and its compatibility with failure
probabilities. -/
lemma probFailure_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    Pr[⊥ | proj (simulateQ (so.preInsert nx) oa)] = Pr[⊥ | simulateQ so oa] := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-- `NeverFail` biconditional companion of `probFailure_proj_simulateQ_preInsert`. -/
lemma neverFail_proj_simulateQ_preInsert_iff [Monad m]
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    NeverFail (proj (simulateQ (so.preInsert nx) oa)) ↔ NeverFail (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-! #### `evalSPMF` / `probOutput` / `support` bridges for `preInsert` -/

lemma evalSPMF_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    𝒮[proj (simulateQ (so.preInsert nx) oa)] = 𝒮[simulateQ so oa] := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma probOutput_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) (x : β) :
    Pr[= x | proj (simulateQ (so.preInsert nx) oa)] = Pr[= x | simulateQ so oa] := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

end insertPre

section insertPost

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] [MonadLiftT m n]
    {ι : Type*} {spec : OracleSpec ι} {α β : Type u}

/-- A `postInsert` instrumentation preserves failure probability for any base monad with
`[MonadLiftT m SPMF]`, given the projection bundle and its compatibility with failure
probabilities. -/
lemma probFailure_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    Pr[⊥ | proj (simulateQ (so.postInsert nx) oa)] = Pr[⊥ | simulateQ so oa] := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-- `NeverFail` biconditional companion of `probFailure_proj_simulateQ_postInsert`. -/
lemma neverFail_proj_simulateQ_postInsert_iff
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    NeverFail (proj (simulateQ (so.postInsert nx) oa)) ↔ NeverFail (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-! #### `evalSPMF` / `probOutput` / `support` bridges for `postInsert` -/

lemma evalSPMF_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    𝒮[proj (simulateQ (so.postInsert nx) oa)] = 𝒮[simulateQ so oa] := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma probOutput_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) (x : β) :
    Pr[= x | proj (simulateQ (so.postInsert nx) oa)] = Pr[= x | simulateQ so oa] := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

end insertPost

end QueryImpl
