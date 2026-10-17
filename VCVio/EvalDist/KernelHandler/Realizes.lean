/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorKernel
public import VCVio.EvalDist.Defs.Measure.Core
public import PolyFun.PFunctor.Handler.Stateful

/-!
# Kernel correctness of stateful monadic handlers

A realization proves a local answer-and-state law for each service operation.
The same law then holds for every adaptive finite client. The implementation
monad is abstract, allowing finite random programs, resumptions, and interaction
trees to share the contract whenever their evaluation respects measurable bind.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.KernelHandler

universe uA u v

variable {P : PFunctor.{uA, u}} {S α : Type u} {m : Type u → Type v}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
  [Monad m] [EvalDistSemantics m]

/-- Every operation realizes its joint answer-and-successor-state kernel. -/
@[expose] def Realizes (K : KernelHandler P S) (h : Handler.Stateful m S P) : Prop :=
  ∀ a s, 𝒟[(h a).run s] = K a s

/-- Local correctness extends to every adaptive client, retaining the final service state. -/
theorem Realizes.run [LawfulEvalDistSemantics m]
    [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
    [MeasurableSpace α] {K : KernelHandler P S} {h : Handler.Stateful m S P}
    (hh : K.Realizes h) (program : FreeM P α) (state : S) :
    𝒟[h.run program state] = program.runKernel K state := by
  induction program generalizing state with
  | pure value => rw [Handler.Stateful.run_pure, evalDist_pure, FreeM.runKernel_pure]
  | lift_bind a next ih =>
      change 𝒟[h.run (.liftBind a next) state] = FreeM.runKernel K (.liftBind a next) state
      have hmeas : Measurable fun result : P.B a × S => 𝒟[h.run (next result.1) result.2] := by
        simp_rw [ih]
        exact FreeM.measurable_runKernel_continuation K next
      rw [Handler.Stateful.run_liftBind, evalDist_bind _ _ hmeas,
        FreeM.runKernel_liftBind, hh a state]
      exact congrArg (Measure.bind (K a state)) (funext fun result => ih result.1 result.2)

end PFunctor.KernelHandler
