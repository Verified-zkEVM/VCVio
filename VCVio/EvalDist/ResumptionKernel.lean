/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorKernel
public import ToMathlib.Probability.Kernel.OmegaCompletePartialOrder
public import PolyFun.PFunctor.Resumption.DomainLaws
public import PolyFun.PFunctor.Resumption.DomainTruncate

/-!
# Continuous stateful kernel interpretations of resumptions

A countable-answer service supplies a continuous algebra on result-and-state
kernels. Its least interpretation handles infinite clients while retaining
joint measurability in private state. No measurable structure on program syntax
and no uniform bound on a well-founded client's depth is required.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder

namespace PFunctor

universe uA uB uS uR

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uR}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] [MeasurableSpace S] [MeasurableSpace α]

/-- The joint answer-and-state service algebra is continuous in its continuation kernels. -/
noncomputable def KernelHandler.continuousAlgebra (K : KernelHandler P S) :
    Resumption.ContinuousAlgebra P (Kernel S (α × S)) := fun a =>
  (Kernel.compContinuousLeft (K a)).comp Kernel.uncurryCountable

/-- The service algebra samples an answer and successor state before selecting a continuation. -/
theorem KernelHandler.continuousAlgebra_apply (K : KernelHandler P S) (a : P.A)
    (next : P.B a → Kernel S (α × S)) (s : S) :
    K.continuousAlgebra a next s = (K a s).bind (fun result => next result.1 result.2) := by
  simp only [continuousAlgebra, ContinuousHom.comp_apply, Kernel.compContinuousLeft_apply,
    Kernel.comp_apply]
  exact congrArg (Measure.bind (K a s)) (funext fun x => Kernel.uncurryCountable_apply next x)

namespace Resumption

/-- The least joint result-and-state kernel of a possibly infinite service client. -/
noncomputable def runKernel (K : KernelHandler P S) (tree : Resumption P α) : Kernel S (α × S) :=
  denote (fun x => Kernel.deterministic (fun s => (x, s))
    (measurable_const.prodMk measurable_id)) K.continuousAlgebra tree

@[simp] theorem runKernel_pure (K : KernelHandler P S) (x : α) (s : S) :
    runKernel K (pure x) s = Measure.dirac (x, s) := by
  simp only [runKernel, denote_pure]
  rfl

/-- Stateful kernel interpretation satisfies the query equation without a termination bound. -/
theorem runKernel_query (K : KernelHandler P S) (a : P.A)
    (next : P.B a → Resumption P α) (s : S) :
    runKernel K (query a next) s =
      (K a s).bind (fun result => runKernel K (next result.1) result.2) := by
  rw [runKernel, denote_query, KernelHandler.continuousAlgebra_apply]
  rfl

/-- Every well-founded client agrees with the finite kernel interpretation. -/
theorem runKernel_toResumption (K : KernelHandler P S) (program : FreeM P α) :
    runKernel K program.toResumption = FreeM.runKernel K program := by
  induction program with
  | pure x => ext s : 1; simp
  | lift_bind a next ih =>
      change runKernel K (FreeM.toResumption (.liftBind a next)) =
        FreeM.runKernel K (.liftBind a next)
      rw [FreeM.toResumption_liftBind]
      ext s : 1
      rw [runKernel_query, FreeM.runKernel_liftBind]
      exact congrArg (Measure.bind (K a s)) (funext fun result => congrArg (fun κ => κ result.2)
        (ih result.1))

/-- The joint kernel is the increasing limit of finite cutoff folds. -/
theorem runKernel_eq_sup_truncations (K : KernelHandler P S) (tree : Resumption P α)
    (state : S) :
    runKernel K tree state = ⨆ n,
      foldTruncate (fun x => Kernel.deterministic (fun s : S => (x, s))
        (measurable_const.prodMk measurable_id)) K.continuousAlgebra n tree state := by
  rw [runKernel, denote_eq_sup_truncations]
  change (ωSup ((truncationChain
    (fun x : α => Kernel.deterministic (fun s : S => (x, s))
      (measurable_const.prodMk measurable_id)) K.continuousAlgebra).map
      (Pi.evalOrderHom tree))) state = _
  rw [Kernel.ωSup_apply]
  rfl

/-- Stateful sequencing is kernel composition, including unbounded execution. -/
theorem runKernel_bind {β : Type uR} [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (K : KernelHandler P S) (tree : Resumption P α) (next : α → Resumption P β) :
    runKernel K (tree.bind next) =
      Kernel.uncurryCountable (fun a => runKernel K (next a)) ∘ₖ runKernel K tree := by
  let continuation := Kernel.uncurryCountable (fun a => runKernel K (next a))
  have hf := denote_fusion (P := P)
    (fun x : α => Kernel.deterministic (fun s : S => (x, s))
      (measurable_const.prodMk measurable_id))
    K.continuousAlgebra K.continuousAlgebra (Kernel.compContinuousRight continuation)
    (by
      ext s : 1
      rw [Kernel.compContinuousRight_apply, Kernel.comp_apply]
      change (0 : Measure (α × S)).bind continuation = 0
      simp)
    (by
      intro a k
      ext s : 1
      simp only [Kernel.compContinuousRight_apply, Kernel.comp_apply,
        KernelHandler.continuousAlgebra_apply]
      rw [Measure.bind_bind
        (measurable_from_prod_countable_right (fun b => (k b).measurable)).aemeasurable
        continuation.aemeasurable]) tree
  rw [runKernel, denote_bind]
  change _ = continuation ∘ₖ _
  rw [Kernel.compContinuousRight_apply] at hf
  change _ = continuation ∘ₖ denote _ K.continuousAlgebra tree
  rw [hf]
  congr 1
  funext a
  ext s : 1
  rw [Kernel.compContinuousRight_apply, Kernel.comp_apply]
  change runKernel K (next a) s = (Measure.dirac (a, s)).bind continuation
  rw [Measure.dirac_bind continuation.measurable]
  exact (Kernel.uncurryCountable_apply (fun a => runKernel K (next a)) (a, s)).symm

/-- Subprobability service operations yield a subprobability returned-state kernel. -/
instance runKernel.instIsSubprobabilityKernel (K : KernelHandler P S)
    [∀ a, IsSubprobabilityKernel (K a)] (tree : Resumption P α) :
    IsSubprobabilityKernel (runKernel K tree) := by
  have h := (domainStep (fun x : α => Kernel.deterministic (fun s : S => (x, s))
      (measurable_const.prodMk measurable_id)) K.continuousAlgebra).fix_induction
    (fun meaning => ∀ t s, meaning t s Set.univ ≤ 1)
  apply IsSubprobabilityKernel.mk
  apply h
  · intro t s
    change (0 : Measure (α × S)) Set.univ ≤ 1
    simp
  · intro meaning hmean t s
    change (match dest t with
      | .inl value => Kernel.deterministic (fun s : S => (value, s)) _
      | .inr ⟨a, children⟩ => K.continuousAlgebra a (fun b => meaning (children b))) s Set.univ ≤ 1
    rcases dest t with value | ⟨a, children⟩
    · simp
    · dsimp only
      rw [KernelHandler.continuousAlgebra_apply]
      let : ∀ result : P.B a × S, IsSubprobabilityMeasure (meaning (children result.1) result.2) :=
        fun result => ⟨hmean _ _⟩
      have hm : Measurable (fun result : P.B a × S => meaning (children result.1) result.2) :=
        measurable_from_prod_countable_right (fun b => (meaning (children b)).measurable)
      let := isSubprobabilityMeasure_bind (μ := K a s) hm.aemeasurable
      exact measure_univ_le _
  · intro c hc t s
    change (ωSup (c.map (Pi.evalOrderHom t))) s Set.univ ≤ 1
    rw [Kernel.ωSup_apply]
    have hm : Monotone (fun n : ℕ => c n t s) := fun _ _ h => c.monotone h t s
    change (⨆ n, c n t s) Set.univ ≤ 1
    rw [Measure.iSup_apply_of_monotone _ hm _ MeasurableSet.univ]
    exact iSup_le fun n => hc n t s

end Resumption
end PFunctor
