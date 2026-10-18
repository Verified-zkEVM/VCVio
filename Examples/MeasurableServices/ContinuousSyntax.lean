/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.MeasurableServices.UniformTernary

/-!
# A continuous-answer program and its fair-bit implementation

The ideal program samples one real in `[0,1)` and returns its ternary cell.
Its syntax is the ordinary polynomial free monad. A local measurability
certificate admits the continuous answer; the resulting output law equals
that of the executable persistent-prefix threshold machine.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor UniformThreshold

namespace UniformTernary.ContinuousSyntax

/-- One operation returning a Borel real. -/
abbrev signature : PFunctor := PUnit y^ ℝ

/-- The answer sigma algebra is the Borel sigma algebra of the real line. -/
@[instance_reducible] def answerSpace : ∀ a : signature.A, MeasurableSpace (signature.B a) :=
  fun _ => inferInstanceAs (MeasurableSpace ℝ)

attribute [local instance] answerSpace

/-- Sample a uniform real and retain the trivial service state. -/
noncomputable def answer : KernelHandler signature Unit := fun _ =>
  Kernel.const Unit ((cellLaw Prefix.empty).map (fun u => (u, ())))

/-- A single real-valued query followed by the measurable ternary partition. -/
@[expose] noncomputable def program : FreeM signature (Fin 3) :=
  .liftBind PUnit.unit (fun u => .pure (bin u))

/-- Joint measurability of the selected return law, including the service state. -/
theorem admissible : FreeM.KernelAdmissible answer program := by
  refine ⟨fun _ => trivial, ?_⟩
  change Measurable (fun result : ℝ × Unit => Measure.dirac (bin result.1, result.2))
  exact Measure.measurable_dirac.comp ((measurable_bin.comp measurable_fst).prodMk measurable_snd)

/-- The explicitly certified continuous program returns the same uniform ternary law. -/
theorem uniform :
    (FreeM.runKernelOfAdmissible answer program admissible ()).map Prod.fst =
      uniformOn (Set.univ : Set (Fin 3)) := by
  rw [FreeM.runKernelOfAdmissible_apply (P := signature)]
  change (((cellLaw Prefix.empty).map (fun u => (u, ()))).bind
    (fun result : ℝ × Unit => Measure.dirac (bin result.1, result.2))).map Prod.fst = _
  have hm : Measurable (fun u : ℝ => (u, ())) := measurable_id.prodMk measurable_const
  have hr : Measurable (fun result : ℝ × Unit => Measure.dirac (bin result.1, result.2)) :=
    Measure.measurable_dirac.comp ((measurable_bin.comp measurable_fst).prodMk measurable_snd)
  rw [Measure.bind_map hm.aemeasurable hr.aemeasurable,
    Measure.bind_dirac_eq_map _ (measurable_bin.prodMk measurable_const),
    Measure.map_map measurable_fst (measurable_bin.prodMk measurable_const)]
  exact bin_uniform

/-- The ideal continuous-answer syntax and executable fair-bit machine agree on their result. -/
theorem eq_compiled :
    (FreeM.runKernelOfAdmissible answer program admissible ()).map Prod.fst =
      (𝒟[ITree.ofResumptionWithTau (compiled.denote ((), Prefix.empty))]).map Prod.fst :=
  uniform.trans compiled_uniform.symm

end UniformTernary.ContinuousSyntax
