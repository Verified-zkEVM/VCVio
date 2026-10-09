/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.WriterT.Core
public import VCVio.OracleComp.EvalDist

/-!
# Probability compatibility for writer-instrumented handlers

Scalar failure and losslessness identities for writer-instrumented oracle simulations.
-/

@[expose] public section

open OracleSpec

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u} {ω : Type u} [Monoid ω]

/-- Running a writer-instrumented simulation preserves the failure probability of the
underlying computation. -/
lemma probFailure_writerT_run_simulateQ [IsUniformSpec spec]
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (oa : OracleComp spec α) : Pr[⊥ | (simulateQ so oa).run] = Pr[⊥ | oa] := by
  induction oa using OracleComp.inductionOn <;> simp

/-- A writer-instrumented simulation never fails iff the underlying computation never fails. -/
lemma NeverFail_writerT_run_simulateQ_iff [IsUniformSpec spec]
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (oa : OracleComp spec α) :
    NeverFail ((simulateQ so oa).run : OracleComp spec _) ↔
      NeverFail (oa : OracleComp spec α) := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    probFailure_writerT_run_simulateQ oa]

end OracleComp
