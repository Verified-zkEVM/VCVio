/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.Tracing

/-!
# Discrete probability equations for logged execution

Logged query execution preserves the output distribution after discarding its trace.
The scalar output, event, and failure probabilities express this projection equation.
-/

@[expose] public section

universe u v w

open OracleSpec OracleComp

variable {ι} {spec : OracleSpec ι} {α : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Logging preserves failure probability: for any base monad `m` with `MonadLiftT m SPMF`,
wrapping an oracle implementation with `withLogging` does not change the probability of failure.
When `m = OracleComp spec`, both sides are `0` (trivially true). When `m` can genuinely fail
(e.g. `OptionT (OracleComp spec)`), this is a non-trivial faithfulness property. -/
lemma probFailure_run_simulateQ_withLogging [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withLogging) mx).run] = Pr[⊥ | simulateQ so mx] :=
  so.probFailure_run_simulateQ_withTraceAppend
    (fun (t : spec.Domain) u => ([⟨t, u⟩] : QueryLog spec)) mx



lemma NeverFail_run_simulateQ_withLogging_iff [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withLogging) mx).run ↔ NeverFail (simulateQ so mx) :=
  so.neverFail_run_simulateQ_withTraceAppend_iff
    (fun (t : spec.Domain) u => ([⟨t, u⟩] : QueryLog spec)) mx


end QueryImpl

namespace loggingOracle

/-- Specialization of `QueryImpl.probFailure_run_simulateQ_withLogging` to `loggingOracle`. -/
lemma probFailure_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    [IsUniformSpec spec]
    (oa : OracleComp spec α) :
    Pr[⊥ | (WriterT.run
        (simulateQ spec.loggingOracle oa) :
          OracleComp spec (α × spec.QueryLog))] = Pr[⊥ | oa] := by
  rw [loggingOracle, QueryImpl.probFailure_run_simulateQ_withLogging, simulateQ_ofLift_eq_self]

/-- Specialization of `QueryImpl.NeverFail_run_simulateQ_withLogging_iff` to `loggingOracle`. -/
@[simp]
lemma NeverFail_run_simulateQ_iff {spec : OracleSpec.{0, 0} ι} {α : Type}
    [IsUniformSpec spec]
    (oa : OracleComp spec α) :
    NeverFail (simulateQ spec.loggingOracle oa).run ↔ NeverFail oa := by
  rw [loggingOracle, QueryImpl.NeverFail_run_simulateQ_withLogging_iff, simulateQ_ofLift_eq_self]



@[simp]
lemma probEvent_fst_run_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    [IsUniformSpec spec]
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[ fun z => p z.1 | (simulateQ spec.loggingOracle oa).run] = Pr[ p | oa] := by
  rw [show (fun z : α × spec.QueryLog => p z.1) = p ∘ Prod.fst from rfl,
    ← probEvent_map, fst_map_run_simulateQ]



lemma probOutput_fst_map_run_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    [IsUniformSpec spec]
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ spec.loggingOracle oa).run] =
      Pr[= x | oa] := by
  rw [fst_map_run_simulateQ]



lemma evalSPMF_fst_map_run_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    [IsUniformSpec spec] (oa : OracleComp spec α) :
    𝒮[Prod.fst <$> (simulateQ spec.loggingOracle oa).run] = 𝒮[oa] := by
  rw [fst_map_run_simulateQ]

end loggingOracle

namespace OracleComp

/-- For any computation `oa` and predicate `p`, the probability of `p` holding on the output
equals the probability of `p ∘ Prod.fst` holding on the output of `oa.withQueryLog`. -/
@[simp, grind =]
lemma probEvent_withQueryLog {ι : Type} {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {α : Type}
    (oa : OracleComp oSpec α) (p : α → Prop) :
    Pr[p ∘ Prod.fst | oa.withQueryLog] = Pr[p | oa] :=
  loggingOracle.probEvent_fst_run_simulateQ oa p


end OracleComp
