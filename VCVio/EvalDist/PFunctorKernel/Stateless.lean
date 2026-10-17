/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorKernel
public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# Compatibility of certified kernels with stateless probability

A stateless answer measure is a kernel with trivial private state. A local
`KernelAdmissible` certificate makes the existing guarded `FreeM.denote`
interpretation agree with the certified kernel, including continuous answers.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor

universe uA uB uR

variable (P : PFunctor.{uA, uB}) [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]

/-- The chosen answer measures, with an unchanged trivial private state. -/
noncomputable def AnswerMeasure.statelessKernel : KernelHandler P Unit := fun a =>
  Kernel.const Unit ((AnswerMeasure.toMeasure a).map (fun b => (b, ())))

@[simp] theorem AnswerMeasure.statelessKernel_apply (a : P.A) (state : Unit) :
    statelessKernel P a state = (toMeasure a).map (fun b => (b, ())) := by rfl

namespace FreeM

variable {P} {α : Type uR} [MeasurableSpace α]

/-- A certified stateless program has the same law as the guarded measure fold. -/
theorem denote_eq_map_runKernelOfAdmissible (program : FreeM P α)
    (hp : KernelAdmissible (AnswerMeasure.statelessKernel P) program) :
    denote program =
      (runKernelOfAdmissible (AnswerMeasure.statelessKernel P) program hp ()).map Prod.fst := by
  rw [runKernelOfAdmissible_apply]
  induction program with
  | pure x =>
      change Measure.dirac x = (Measure.dirac (x, ())).map Prod.fst
      rw [Measure.map_dirac' measurable_fst]
  | lift_bind a next ih =>
      change KernelAdmissible (AnswerMeasure.statelessKernel P) (.liftBind a next) at hp
      have hnext (b : P.B a) := ih b (hp.1 b)
      have hpair : Measurable (fun b : P.B a => (b, ())) :=
        measurable_id.prodMk measurable_const
      have hstate : Measurable (fun b : P.B a =>
          runStateMeasure (AnswerMeasure.statelessKernel P) (next b) ()) := hp.2.comp hpair
      have hm : Measurable (fun b => denote (next b)) := by
        simp_rw [hnext]
        exact (Measure.measurable_map Prod.fst measurable_fst).comp
          (hp.2.comp hpair)
      change denote (.liftBind a next) =
        ((AnswerMeasure.statelessKernel P a ()).bind fun result =>
          runStateMeasure (AnswerMeasure.statelessKernel P) (next result.1) result.2).map Prod.fst
      rw [denote_liftBind a next hm.aemeasurable, AnswerMeasure.statelessKernel_apply,
        Measure.bind_map hpair.aemeasurable hp.2.aemeasurable,
        Measure.map_bind hstate.aemeasurable
          measurable_fst.aemeasurable]
      exact congrArg (Measure.bind (AnswerMeasure.toMeasure a)) (funext hnext)

end FreeM
end PFunctor
