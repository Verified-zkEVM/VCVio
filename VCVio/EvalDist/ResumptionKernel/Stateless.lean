/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ResumptionKernel
public import VCVio.EvalDist.ResumptionMeasure.Domain
public import VCVio.EvalDist.PFunctorKernel.Stateless

/-!
# Stateless probability as a coinductive kernel interpretation

Forgetting the trivial state of the chosen answer kernels gives the ordinary
returned measure. The proof uses continuous-algebra fusion, so it applies to
infinite or diverging clients without a termination premise.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder

universe uA u

namespace PFunctor.Resumption

variable {P : PFunctor.{uA, u}} {α : Type u}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] [P.AnswerMeasure] [MeasurableSpace α]

/-- Forgetting the trivial state of the kernel interpretation recovers the returned measure,
including divergence and clients without a uniform finite depth bound. -/
theorem map_runKernel_stateless (tree : Resumption P α) :
    (runKernel (AnswerMeasure.statelessKernel P) tree ()).map Prod.fst =
      returnedMeasure tree := by
  let F : Kernel Unit (α × Unit) →𝒄 Measure α :=
    (Measure.bindContinuousLeft (Measure.measurable_dirac.comp measurable_fst)).comp
      (Kernel.evalContinuous ())
  have hf := denote_fusion (P := P)
    (fun x : α => Kernel.deterministic (fun s : Unit => (x, s))
      (measurable_const.prodMk measurable_id))
    (AnswerMeasure.statelessKernel P).continuousAlgebra (AnswerMeasure.continuousAlgebra P α)
    F (by
      simp only [F, ContinuousHom.comp_apply, Measure.bindContinuousLeft_apply,
        Kernel.evalContinuous_apply]
      change (0 : Measure (α × Unit)).bind (fun out => Measure.dirac out.1) = 0
      simp) (by
      intro a next
      simp only [F, ContinuousHom.comp_apply, Measure.bindContinuousLeft_apply,
        Kernel.evalContinuous_apply, KernelHandler.continuousAlgebra_apply,
        AnswerMeasure.statelessKernel_apply, AnswerMeasure.continuousAlgebra_apply]
      rw [Measure.bind_map (f := fun b : P.B a => (b, ()))
        (measurable_id.prodMk measurable_const).aemeasurable
        Measurable.of_discrete.aemeasurable]
      exact Measure.bind_bind Measurable.of_discrete.aemeasurable
        (Measure.measurable_dirac.comp measurable_fst).aemeasurable) tree
  simp only [F, ContinuousHom.comp_apply, Measure.bindContinuousLeft_apply,
    Kernel.evalContinuous_apply] at hf
  simp only [Kernel.deterministic_apply,
    Measure.dirac_bind (Measure.measurable_dirac.comp measurable_fst)] at hf
  change ((denote (fun x : α => Kernel.deterministic (fun s : Unit => (x, s))
    (measurable_const.prodMk measurable_id)) (AnswerMeasure.statelessKernel P).continuousAlgebra
      tree) ()).bind (fun out => Measure.dirac out.1) =
    denote Measure.dirac (AnswerMeasure.continuousAlgebra P α) tree at hf
  rw [Measure.bind_dirac_eq_map _ measurable_fst] at hf
  simpa only [runKernel_eq_denote, returnedMeasure_eq_denote] using hf

end PFunctor.Resumption
