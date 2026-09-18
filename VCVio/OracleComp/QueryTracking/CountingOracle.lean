/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.CountingOracle.Core
public import VCVio.OracleComp.QueryTracking.Tracing
public import VCVio.OracleComp.EvalDist

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle` for counting the number of queries made
while running the computation. The count is represented by a function from oracle indices to
counts, allowing each oracle to be tracked individually.

Tracking individually is not necessary, but gives tighter security bounds in some cases.
It also allows for generating things like seed values for a computation more tightly.

`QueryImpl.withCost` and `QueryImpl.withCounting` are response-independent traces, defined as
specialisations of `QueryImpl.withTraceBefore` (see `Tracing.lean`): the cost is accumulated
*before* the underlying handler runs, so failed queries still incur their cost. The counting
case picks `QueryCount.single` as the trace function.
-/

@[expose] public section

open OracleSpec OracleComp

universe u v w

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

section withCost

variable {ω : Type u} [Monoid ω]

/-- Cost-tracking preserves failure probability: for any base monad `m` with `MonadLiftT m SPMF`,
wrapping an oracle implementation with `withCost` does not change the probability of failure. -/
lemma probFailure_run_simulateQ_withCost [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withCost costFn) mx).run] = Pr[⊥ | simulateQ so mx] :=
  probFailure_run_simulateQ_withTraceBefore so costFn mx

lemma NeverFail_run_simulateQ_withCost_iff [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withCost costFn) mx).run ↔ NeverFail (simulateQ so mx) :=
  neverFail_run_simulateQ_withTraceBefore_iff so costFn mx

/-! ### EvalDist Bridge for `withCost`

These lemmas connect the result-marginal distribution of a `withCost`-instrumented
computation to the distribution of the uninstrumented computation, enabling direct
probability-level reasoning about traced computations. -/

lemma evalSPMF_fst_run_withCost [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    𝒮[Prod.fst <$> (simulateQ (so.withCost costFn) mx).run] =
      𝒮[simulateQ so mx] :=
  evalSPMF_fst_run_withTraceBefore so costFn mx

lemma probOutput_fst_run_withCost [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withCost costFn) mx).run] =
      Pr[= x | simulateQ so mx] :=
  probOutput_fst_run_withTraceBefore so costFn mx x
end withCost

end QueryImpl

namespace costOracle

variable {ω : Type u} [Monoid ω]
lemma evalSPMF_fst_run_simulateQ [IsUniformSpec spec]
    (costFn : spec.Domain → ω) (oa : OracleComp spec α) :
    𝒮[Prod.fst <$> (simulateQ (costOracle costFn) oa).run] = 𝒮[oa] := by
  rw [fst_map_run_simulateQ]

lemma probOutput_fst_run_simulateQ [IsUniformSpec spec]
    (costFn : spec.Domain → ω) (oa : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (costOracle costFn) oa).run] = Pr[= x | oa] := by
  rw [fst_map_run_simulateQ]
end costOracle

namespace countingOracle

variable [DecidableEq ι]
/-- Specialization of `QueryImpl.probFailure_run_simulateQ_withCost` to `countingOracle`. -/
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    [DecidableEq ι₀] [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) :
    Pr[⊥ | (simulateQ (spec₀.countingOracle) oa).run] = Pr[⊥ | oa] := by
  simp only [countingOracle, QueryImpl.withCounting_eq_withCost,
    QueryImpl.probFailure_run_simulateQ_withCost, simulateQ_ofLift_eq_self]

/-- Specialization of `QueryImpl.NeverFail_run_simulateQ_withCost_iff` to `countingOracle`. -/
@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    [DecidableEq ι₀] [IsUniformSpec spec₀] {α : Type}
    (oa : OracleComp spec₀ α) :
    NeverFail (simulateQ (spec₀.countingOracle) oa).run ↔ NeverFail oa := by
  simp only [countingOracle, QueryImpl.withCounting_eq_withCost,
    QueryImpl.NeverFail_run_simulateQ_withCost_iff, simulateQ_ofLift_eq_self]

@[simp]
lemma probEvent_fst_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    [DecidableEq ι₀] [IsUniformSpec spec₀] {α : Type}
    (oa : OracleComp spec₀ α) (p : α → Prop) :
    Pr[ fun z => p z.1 | (simulateQ (spec₀.countingOracle) oa).run] = Pr[ p | oa] := by
  rw [show (fun z : α × QueryCount ι₀ => p z.1) = p ∘ Prod.fst from rfl,
    ← probEvent_map, fst_map_run_simulateQ]

lemma probOutput_fst_map_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    [DecidableEq ι₀] [IsUniformSpec spec₀] {α : Type}
    (oa : OracleComp spec₀ α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (spec₀.countingOracle) oa).run] =
      Pr[= x | oa] := by
  rw [fst_map_run_simulateQ]

lemma evalSPMF_fst_map_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) :
    𝒮[Prod.fst <$> (simulateQ (spec₀.countingOracle) oa).run] = 𝒮[oa] := by
  rw [fst_map_run_simulateQ]
section support

section snd_map
end snd_map
end support

end countingOracle
