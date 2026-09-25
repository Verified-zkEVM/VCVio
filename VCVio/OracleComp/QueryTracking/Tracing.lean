/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.Tracing.Core
public import VCVio.OracleComp.EvalDist

/-!
# Discrete probability equations for trace instrumentation

The successful-output projection of an instrumented query implementation preserves
its discrete distribution and scalar output and failure probabilities.
-/

@[expose] public section

open OracleSpec OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-! ### `withTraceBefore`: response-independent trace, recorded before handler -/

section withTraceBefore

variable {ω : Type u} [Monoid ω]

/-- A "before"-style trace preserves failure probability for any base monad with
`MonadLiftT m SPMF`: instrumenting with `withTraceBefore` does not change the
probability of failure. -/
lemma probFailure_run_simulateQ_withTraceBefore [LawfulMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceBefore traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTraceBefore so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTraceBefore_iff [LawfulMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceBefore traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceBefore]

/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTraceBefore` -/

lemma evalSPMF_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    𝒮[Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run] =
      𝒮[simulateQ so mx] :=
  congrArg evalSPMF (fst_map_run_withTraceBefore so traceFn mx)

lemma probOutput_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceBefore]
end withTraceBefore

/-! ### `withTrace`: response-dependent trace, recorded after handler -/

section withTrace

variable {ω : Type u} [Monoid ω]

/-- An "after"-style trace preserves failure probability for any base monad with
`MonadLiftT m SPMF`: instrumenting with `withTrace` does not change the probability
of failure. When `m = OracleComp spec`, both sides are `0` (trivially true);
when `m` can genuinely fail (e.g. `OptionT (OracleComp spec)`), this is a
non-trivial faithfulness property. -/
lemma probFailure_run_simulateQ_withTrace [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTrace traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTrace so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTrace_iff [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTrace traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTrace]

/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTrace` -/

lemma evalSPMF_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    𝒮[Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run] =
      𝒮[simulateQ so mx] :=
  congrArg evalSPMF (fst_map_run_withTrace so traceFn mx)

lemma probOutput_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTrace]
end withTrace

/-! ### `withTraceAppendBefore`: response-independent trace, recorded before
handler, accumulating via `∅` / `++` -/

section withTraceAppendBefore

variable {ω : Type u} [EmptyCollection ω] [Append ω]

lemma probFailure_run_simulateQ_withTraceAppendBefore [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTraceAppendBefore so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTraceAppendBefore_iff [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppendBefore traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceAppendBefore]

/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTraceAppendBefore` -/

lemma evalSPMF_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    𝒮[Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      𝒮[simulateQ so mx] :=
  congrArg evalSPMF (fst_map_run_withTraceAppendBefore so traceFn mx)

lemma probOutput_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceAppendBefore]
end withTraceAppendBefore

/-! ### `withTraceAppend`: response-dependent trace, recorded after handler,
accumulating via `∅` / `++` -/

section withTraceAppend

variable {ω : Type u} [EmptyCollection ω] [Append ω]

lemma probFailure_run_simulateQ_withTraceAppend [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceAppend traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTraceAppend so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTraceAppend_iff [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppend traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceAppend]

/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTraceAppend` -/

lemma evalSPMF_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    𝒮[Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run] =
      𝒮[simulateQ so mx] :=
  congrArg evalSPMF (fst_map_run_withTraceAppend so traceFn mx)

lemma probOutput_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceAppend]
end withTraceAppend

end QueryImpl
