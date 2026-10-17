/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ResumptionMeasure
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-!
# Measures of bounded and resumable machine executions

Executable machine unrolling and coinductive truncation have identical measures. Retaining
the residual state permits exact continuation across chunk boundaries. Projecting it away
gives the explicit cutoff observation; discarding cutoff mass gives the increasing
returned-output approximations.
-/

public section

open MeasureTheory

namespace PFunctor.DynSystem.DynComputation

variable {P : PFunctor} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α β : Type*}

/-- Bounded machine execution and bounded coinductive semantics agree. -/
theorem denote_unroll [MeasurableSpace β] (machine : DynComputation P α β)
    (fuel : ℕ) (state : machine.State) :
    FreeM.denote (machine.unroll fuel state) =
      Resumption.truncateMeasure fuel (machine.toDynSystem.behavior state) := by
  rw [unroll_eq_truncate, Resumption.truncateMeasure]

/-- Forgetting the residual state of a chunk gives exactly the cutoff law. -/
theorem map_denote_unrollChunk [MeasurableSpace β]
    [∀ a, DiscreteMeasurableSpace (P.B a)] (machine : DynComputation P α β)
    [MeasurableSpace (Chunk machine.State β)] (hresult : Measurable (@Chunk.result machine.State β))
    (fuel : ℕ) (state : machine.State) :
    (FreeM.denote (machine.unrollChunk fuel state)).map Chunk.result =
      Resumption.truncateMeasure fuel (machine.toDynSystem.behavior state) := by
  rw [← FreeM.denote_map_of_measurable _ _ hresult, unrollChunk_result, denote_unroll]

/-- The successful-output measure of a bounded execution is the canonical approximation. -/
theorem dropNone_denote_unroll [MeasurableSpace β] (machine : DynComputation P α β)
    (fuel : ℕ) (state : machine.State) :
    (FreeM.denote (machine.unroll fuel state)).dropNone =
      Resumption.outputMeasure fuel (machine.toDynSystem.behavior state) := by
  rw [denote_unroll, Resumption.outputMeasure]

/-- A resumed chunk has the law of one execution with the combined budget. -/
theorem denote_unrollChunk_add (machine : DynComputation P α β)
    [MeasurableSpace (Chunk machine.State β)] (first second : ℕ) (state : machine.State) :
    FreeM.denote (machine.unrollChunk first state >>= machine.resumeChunk second) =
      FreeM.denote (machine.unrollChunk (first + second) state) := by
  rw [unrollChunk_add]

end PFunctor.DynSystem.DynComputation
