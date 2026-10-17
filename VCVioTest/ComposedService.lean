/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.MeasurableServices.ReactiveThreshold
public import Examples.MeasurableServices.ContinuousSyntax
public import VCVio.EvalDist.ResumptionKernel
meta import Examples.MeasurableServices.UniformTernary
meta import VCVio.OracleComp.Coinductive.UniformThreshold.Approximation
meta import PolyFun.PFunctor.Dynamical.DynComputation.Resumable
meta import PolyFun.ITree.Machine

/-! # Executable composed-service regressions and ordinary-import semantic canaries -/

public section

open PFunctor UniformThreshold

namespace VCVioTest.ComposedService

attribute [local instance] UniformTernary.ContinuousSyntax.answerSpace

private def tape : Handler (StateT (List Bool) Option) coinSpec.toPFunctor := fun _ bits =>
  match bits with
  | [] => none
  | b :: rest => some (b, rest)

/-- Run the complete ternary client, retaining the exact unconsumed tape suffix. -/
def inspect (fuel : Nat) (bits : List Bool) : Option (Option (Fin 3) × List Bool) := do
  let (chunk, rest) ← UniformTernary.compiled.startChunk
    (ITree.withSilentSteps tape) fuel ((), Prefix.empty) bits
  pure (chunk.result.map Prod.fst, rest)

/-- Permanently cap each service call before running the optional client. -/
def capped (fuel : Nat) (bits : List Bool) : Option (Option (Fin 3) × List Bool) := do
  let (value, rest) ←
    (cappedClient (fun _ _ => fuel) UniformTernary.client Prefix.empty).run.liftM tape bits
  pure (value.map Prod.fst, rest)

run_cmd do
  unless inspect 20 [false, false, true] == some (some 0, [true]) do
    throwError "compiled lower third lost output or consumed extra bits"
  unless inspect 20 [true, false, false, true] == some (some 1, [true]) do
    throwError "compiled middle third did not preserve the first call's prefix"
  unless inspect 20 [true, true, false] == some (some 2, [false]) do
    throwError "compiled upper third did not return at the first decisive bit"
  unless capped 1 [false, false, true] == some (none, [false, true]) do
    throwError "a capped call retried after timeout"
  unless capped 1 [true, true, false] == some (some 2, [false]) do
    throwError "per-call caps were confused with the whole client's bit budget"

example : ITree.returnedMeasure (ITree.diverge : ITree coinSpec.toPFunctor Bool) = 0 :=
  ITree.returnedMeasure_diverge

example : PFunctor.FreeM.KernelAdmissible UniformTernary.ContinuousSyntax.answer
    (UniformTernary.ContinuousSyntax.program.map (fun x => decide (x = 0))) :=
  UniformTernary.ContinuousSyntax.admissible.map _ Measurable.of_discrete

end VCVioTest.ComposedService
