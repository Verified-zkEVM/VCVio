/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.PFunctorKernel
public import ToMathlib.Probability.Kernel.RetainLeft

/-!
# Probabilistic reconstruction of private state

A reconstruction kernel gives a distribution of ideal states for each concrete state.
Each local operation commutes with reconstruction, retaining the common answer. This
intertwining law lifts to arbitrary adaptive free-monad clients and to initial state laws.
Unlike a pointwise state relation, it permits an ideal service to sample its randomness eagerly
while the concrete service reveals it only when queried.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.KernelHandler

variable {P : PFunctor} {S T : Type*}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace T]

/-- Local joint answer/state laws commute with a supplied probabilistic reconstruction. -/
structure ReconstructionContract (concrete : KernelHandler P S) (ideal : KernelHandler P T)
    (reconstruct : Kernel S T) : Prop where
  /-- Reconstruction is a probability kernel, so it neither fails nor discards mass. -/
  isMarkov : IsMarkovKernel reconstruct
  /-- Reconstructing before or after one operation yields the same joint law. -/
  step : ∀ a, ideal a ∘ₖ reconstruct = Kernel.retainLeft (P.B a) reconstruct ∘ₖ concrete a

namespace ReconstructionContract

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {concrete : KernelHandler P S} {ideal : KernelHandler P T} {R : Kernel S T}
  (contract : ReconstructionContract concrete ideal R)
  {α : Type*} [MeasurableSpace α]

include contract

/-- The local reconstruction law lifts to every adaptive client, retaining its result. -/
theorem runKernel (program : FreeM P α) :
    FreeM.runKernel ideal program ∘ₖ R =
      Kernel.retainLeft α R ∘ₖ FreeM.runKernel concrete program := by
  let := contract.isMarkov
  ext state : 1
  simp only [Kernel.comp_apply]
  induction program generalizing state with
  | pure x =>
      rw [show ⇑(FreeM.runKernel ideal (pure x)) =
        (fun t => Measure.dirac (x, t)) from funext (FreeM.runKernel_pure ideal x)]
      simp only [FreeM.runKernel_pure]
      rw [Measure.dirac_bind (Kernel.retainLeft α R).measurable,
        Kernel.retainLeft_apply, Measure.bind_dirac_eq_map _ measurable_prodMk_left]
  | lift_bind a next ih =>
      simp only [← FreeM.liftBind_eq]
      rw [show ⇑(FreeM.runKernel ideal (.liftBind a next)) =
        (fun t => (ideal a t).bind fun out => FreeM.runKernel ideal (next out.1) out.2)
        from funext (FreeM.runKernel_liftBind ideal a next), FreeM.runKernel_liftBind]
      rw [← Measure.bind_bind (ideal a).aemeasurable
        (FreeM.measurable_runKernel_continuation ideal next).aemeasurable]
      have hstep := congrArg (fun k : Kernel S (P.B a × T) => k state) (contract.step a)
      simp only [Kernel.comp_apply] at hstep
      rw [hstep, Measure.bind_bind (Kernel.retainLeft (P.B a) R).aemeasurable
        (FreeM.measurable_runKernel_continuation ideal next).aemeasurable,
        Measure.bind_bind (FreeM.measurable_runKernel_continuation concrete next).aemeasurable
        (Kernel.retainLeft α R).aemeasurable]
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall fun out => by
        dsimp only
        rw [Kernel.bind_retainLeft R _ (FreeM.measurable_runKernel_continuation ideal next)]
        exact ih out.1 out.2

/-- Reconstructing an initial law commutes with the entire client execution. -/
theorem bind_state_laws (μ : Measure S) (program : FreeM P α) :
    (μ.bind R).bind (FreeM.runKernel ideal program) =
      (μ.bind (FreeM.runKernel concrete program)).bind (Kernel.retainLeft α R) := by
  rw [Measure.bind_bind R.aemeasurable (FreeM.runKernel ideal program).aemeasurable,
    Measure.bind_bind (FreeM.runKernel concrete program).aemeasurable
      (Kernel.retainLeft α R).aemeasurable]
  exact congrArg (μ.bind ·) (congrArg DFunLike.coe (contract.runKernel program))

/-- Matching reconstructed initial laws give the same result distribution to every adaptive
client, after both private states are hidden. -/
theorem output_law (μ : Measure S) (program : FreeM P α) :
    ((μ.bind R).bind (FreeM.runKernel ideal program)).map Prod.fst =
      (μ.bind (FreeM.runKernel concrete program)).map Prod.fst := by
  let := contract.isMarkov
  rw [contract.bind_state_laws, Kernel.map_fst_bind_retainLeft]

/-- Reconstruction contracts are closed under inlining a handler with shared private state. -/
theorem freeHandler {Q : PFunctor} [∀ a, MeasurableSpace (Q.B a)]
    (implementation : (a : Q.A) → FreeM P (Q.B a)) :
    ReconstructionContract (fun a => FreeM.runKernel concrete (implementation a))
      (fun a => FreeM.runKernel ideal (implementation a)) R :=
  ⟨contract.isMarkov, fun a => contract.runKernel (implementation a)⟩

end ReconstructionContract

/-- A deterministic state projection is a reconstruction contract when each joint local
answer/state law pushes forward to the ideal law. -/
theorem ReconstructionContract.of_deterministic (concrete : KernelHandler P S)
    (ideal : KernelHandler P T) (f : S → T) (hf : Measurable f)
    (hstep : ∀ a s, (concrete a s).map (fun out => (out.1, f out.2)) = ideal a (f s)) :
    ReconstructionContract concrete ideal (Kernel.deterministic f hf) := by
  refine ⟨inferInstance, fun a => ?_⟩
  ext s : 1
  rw [Kernel.retainLeft_deterministic, Kernel.comp_apply, Kernel.comp_apply,
    Kernel.deterministic_apply, Measure.dirac_bind (ideal a).measurable]
  change ideal a (f s) = (concrete a s).bind (fun out => Measure.dirac (out.1, f out.2))
  exact (hstep a s).symm.trans
    (Measure.bind_dirac_eq_map _ (measurable_fst.prodMk (hf.comp measurable_snd))).symm

end PFunctor.KernelHandler
