/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.Reconstruction
public import VCVio.EvalDist.ITreeKernel

/-!
# Reconstruction for coinductive service clients

The local reconstruction contract commutes with least continuous interpretations.
It therefore preserves the joint result and reconstructed state of an arbitrary
interaction tree or resumption, including clients that diverge. The result follows
from continuous-algebra fusion and requires no termination assumption or measurable
structure on program syntax. The private state spaces may be continuous.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder

namespace PFunctor

variable {P : PFunctor} {S T α : Type*}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace α]

namespace KernelHandler.ReconstructionContract

variable {concrete : KernelHandler P S} {ideal : KernelHandler P T} {R : Kernel S T}
  (contract : ReconstructionContract concrete ideal R)

include contract

/-- Local reconstruction commutes with the joint kernel of a possibly divergent client. -/
theorem runKernel_itree (tree : ITree P α) :
    ITree.runKernel ideal tree ∘ₖ R =
      Kernel.retainLeft α R ∘ₖ ITree.runKernel concrete tree := by
  let := contract.isMarkov
  let retI : α → Kernel T (α × T) := fun x =>
    Kernel.deterministic (fun t => (x, t)) (measurable_const.prodMk measurable_id)
  let retC : α → Kernel S (α × S) := fun x =>
    Kernel.deterministic (fun s => (x, s)) (measurable_const.prodMk measurable_id)
  have hi := ITree.denote_fusion retI ideal.continuousAlgebra
    (concrete.continuousAlgebra (α := α × T)) (Kernel.compContinuousLeft R)
    (by
      ext s : 1
      rw [Kernel.compContinuousLeft_apply, Kernel.comp_apply]
      change (R s).bind (fun _ => (0 : Measure (α × T))) = 0
      simp)
    (by
      intro a next
      ext s : 1
      simp only [Kernel.compContinuousLeft_apply, Kernel.comp_apply,
        KernelHandler.continuousAlgebra_apply]
      rw [show ⇑(ideal.continuousAlgebra a next) =
        (fun t => (ideal a t).bind (fun out => next out.1 out.2)) from
          funext (KernelHandler.continuousAlgebra_apply ideal a next)]
      have hm : Measurable (fun out : P.B a × T => next out.1 out.2) :=
        measurable_from_prod_countable_right (fun b => (next b).measurable)
      rw [← Measure.bind_bind (ideal a).aemeasurable hm.aemeasurable]
      have hstep := congrArg (fun k : Kernel S (P.B a × T) => k s) (contract.step a)
      simp only [Kernel.comp_apply] at hstep
      rw [hstep, Measure.bind_bind (Kernel.retainLeft (P.B a) R).aemeasurable hm.aemeasurable]
      apply congrArg (Measure.bind (concrete a s))
      funext out
      exact Kernel.bind_retainLeft R _ hm out) tree
  have hc := ITree.denote_fusion retC concrete.continuousAlgebra
    (concrete.continuousAlgebra (α := α × T)) (Kernel.compContinuousRight (Kernel.retainLeft α R))
    (by
      ext s : 1
      rw [Kernel.compContinuousRight_apply, Kernel.comp_apply]
      change (0 : Measure (α × S)).bind (Kernel.retainLeft α R) = 0
      simp)
    (by
      intro a next
      ext s : 1
      simp only [Kernel.compContinuousRight_apply, Kernel.comp_apply,
        KernelHandler.continuousAlgebra_apply]
      exact Measure.bind_bind
        (measurable_from_prod_countable_right (fun b => (next b).measurable)).aemeasurable
        (Kernel.retainLeft α R).aemeasurable) tree
  rw [ITree.runKernel_eq_denote, ITree.runKernel_eq_denote]
  rw [← Kernel.compContinuousLeft_apply, ← Kernel.compContinuousRight_apply]
  change Kernel.compContinuousLeft R (ITree.denote retI ideal.continuousAlgebra tree) =
    Kernel.compContinuousRight (Kernel.retainLeft α R)
      (ITree.denote retC concrete.continuousAlgebra tree)
  rw [hi, hc]
  congr 1
  funext x
  ext s : 1
  simp only [Kernel.compContinuousLeft_apply, Kernel.compContinuousRight_apply, Kernel.comp_apply]
  change (R s).bind (fun t => Measure.dirac (x, t)) =
    (Measure.dirac (x, s)).bind (Kernel.retainLeft α R)
  rw [Measure.dirac_bind (Kernel.retainLeft α R).measurable,
    Kernel.retainLeft_apply, Measure.bind_dirac_eq_map _ measurable_prodMk_left]

/-- The reconstruction law transfers along the canonical resumption embedding. -/
theorem runKernel_resumption (tree : Resumption P α) :
    Resumption.runKernel ideal tree ∘ₖ R =
      Kernel.retainLeft α R ∘ₖ Resumption.runKernel concrete tree := by
  simpa only [ITree.runKernel_toITree] using contract.runKernel_itree tree.toITree

/-- Reconstructing the initial law commutes with a possibly divergent interaction tree. -/
theorem bind_state_laws_itree (μ : Measure S) (tree : ITree P α) :
    (μ.bind R).bind (ITree.runKernel ideal tree) =
      (μ.bind (ITree.runKernel concrete tree)).bind (Kernel.retainLeft α R) := by
  rw [Measure.bind_bind R.aemeasurable (ITree.runKernel ideal tree).aemeasurable,
    Measure.bind_bind (ITree.runKernel concrete tree).aemeasurable
      (Kernel.retainLeft α R).aemeasurable]
  exact congrArg (μ.bind ·) (congrArg DFunLike.coe (contract.runKernel_itree tree))

/-- Reconstructing the initial law commutes with an unbounded resumption. -/
theorem bind_state_laws_resumption (μ : Measure S) (tree : Resumption P α) :
    (μ.bind R).bind (Resumption.runKernel ideal tree) =
      (μ.bind (Resumption.runKernel concrete tree)).bind (Kernel.retainLeft α R) := by
  simpa only [ITree.runKernel_toITree] using contract.bind_state_laws_itree μ tree.toITree

/-- Hiding private states gives equal returned laws, including any missing mass. -/
theorem output_law_itree (μ : Measure S) (tree : ITree P α) :
    ((μ.bind R).bind (ITree.runKernel ideal tree)).map Prod.fst =
      (μ.bind (ITree.runKernel concrete tree)).map Prod.fst := by
  let := contract.isMarkov
  rw [contract.bind_state_laws_itree, Kernel.map_fst_bind_retainLeft]

/-- An unbounded adaptive client observes the same returned law under reconstruction. -/
theorem output_law_resumption (μ : Measure S) (tree : Resumption P α) :
    ((μ.bind R).bind (Resumption.runKernel ideal tree)).map Prod.fst =
      (μ.bind (Resumption.runKernel concrete tree)).map Prod.fst := by
  simpa only [ITree.runKernel_toITree] using contract.output_law_itree μ tree.toITree

/-- Reconstruction contracts are closed under inlining possibly divergent interaction trees. -/
theorem itreeHandler {Q : PFunctor} [∀ a, MeasurableSpace (Q.B a)]
    (implementation : (a : Q.A) → ITree P (Q.B a)) :
    ReconstructionContract (fun a => ITree.runKernel concrete (implementation a))
      (fun a => ITree.runKernel ideal (implementation a)) R :=
  ⟨contract.isMarkov, fun a => contract.runKernel_itree (implementation a)⟩

end KernelHandler.ReconstructionContract
end PFunctor
