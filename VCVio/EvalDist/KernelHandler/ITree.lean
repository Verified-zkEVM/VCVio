/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ITreeKernel
public import VCVio.EvalDist.ITreeMeasure
public import VCVio.EvalDist.KernelHandler.Realizes
public import PolyFun.ITree.Interp.Stateful

/-!
# Kernel adequacy for stateful coinductive handlers

The same local `Realizes` contract used for finite free clients determines the
joint returned law of an arbitrary interaction-tree client. The proof compares
least interpretations through the shared iteration rule. It does not identify
microstep clocks, condition on success, or assume almost-sure termination.
Joint measurability is an explicit obligation for continuous private state and
is automatic for countable separated state.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder PFunctor

namespace PFunctor.KernelHandler

universe u uQA
variable {P : PFunctor.{u, u}} {Q : PFunctor.{uQA, u}} {S α : Type u}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)]
  [∀ a, MeasurableSpace (Q.B a)] [∀ a, DiscreteMeasurableSpace (Q.B a)] [Q.AnswerMeasure]
  [MeasurableSpace S] [MeasurableSpace α]
  {K : KernelHandler P S} {handler : Handler.Stateful (ITree Q) S P}

/-- Local joint handler laws determine unbounded stateful interpretation when
its actual returned-state law is jointly measurable in private state. -/
theorem Realizes.interp_of_measurable (hh : K.Realizes handler)
    (hmeas : ∀ tree : ITree P α, Measurable fun s => 𝒟[(ITree.interp handler tree).run s])
    (tree : ITree P α) (state : S) :
    𝒟[(ITree.interp handler tree).run state] = ITree.runKernel K tree state := by
  have hhandler (a : P.A) (s : S) : 𝒟[handler a s] = K a s := hh a s
  let ret : α → Kernel S (α × S) := fun value =>
    Kernel.deterministic (fun s => (value, s)) (measurable_const.prodMk measurable_id)
  apply le_antisymm
  · rw [ITree.evalDist_eq_returnedMeasure, ITree.returnedMeasure_eq_denote,
      ITree.interp_run_eq_iter]
    apply ITree.denote_iter_le Measure.dirac (AnswerMeasure.continuousAlgebra Q (α × S))
      (StateT.stateBody (ITree.interpStep handler)) (fun out => ITree.runKernel K out.1 out.2) _
    rintro ⟨t, s⟩
    rcases ht : ITree.shape' t with ⟨head, children⟩
    cases head with
    | pure value =>
      obtain rfl := ITree.eq_pure_of_dest ht
      rw [ITree.stateBody_interpStep_pure, ITree.denote_pure, ITree.runKernel_pure]
      exact le_rfl
    | step =>
      obtain rfl := ITree.eq_step_of_dest ht
      rw [ITree.stateBody_interpStep_step, ITree.denote_pure, ITree.runKernel_step]
      exact le_rfl
    | query a =>
      obtain rfl := ITree.eq_query_of_dest ht
      rw [ITree.stateBody_interpStep_query, ITree.bind_eq_bind, ITree.denote_bind]
      simp only [ITree.denote_pure, Sum.elim_inl]
      rw [ITree.denote_eq_bind_returnedMeasure _ _
          (measurable_from_prod_countable_right
            (fun b => (ITree.runKernel K (children b)).measurable)),
        ← ITree.evalDist_eq_returnedMeasure, hhandler a s, ITree.runKernel_query]
  · let meaning : ITree P α → Kernel S (α × S) := fun t =>
      ⟨fun s => 𝒟[(ITree.interp handler t).run s], hmeas t⟩
    have hbound : ITree.denote ret K.continuousAlgebra ≤ meaning := by
      apply ITree.denote_le
      intro t
      change ∀ s, (ITree.domainStep ret K.continuousAlgebra meaning) t s ≤ meaning t s
      intro s
      simp only [ITree.domainStep, ContinuousHom.ofFun_apply]
      rcases ht : ITree.shape' t with ⟨head, children⟩
      cases head with
      | pure value =>
        obtain rfl := ITree.eq_pure_of_dest ht
        change Measure.dirac (value, s) ≤ 𝒟[(ITree.interp handler (ITree.pure value)).run s]
        rw [ITree.interp_run_pure, ITree.evalDist_eq_returnedMeasure, ITree.returnedMeasure_pure]
      | step =>
        obtain rfl := ITree.eq_step_of_dest ht
        change 𝒟[(ITree.interp handler (children PUnit.unit)).run s] ≤
          𝒟[(ITree.interp handler (ITree.step (children PUnit.unit))).run s]
        rw [ITree.interp_run_step]
        simp only [ITree.evalDist_eq_returnedMeasure, ITree.returnedMeasure_step, le_refl]
      | query a =>
        obtain rfl := ITree.eq_query_of_dest ht
        rw [KernelHandler.continuousAlgebra_apply]
        change (K a s).bind (fun out => 𝒟[(ITree.interp handler (children out.1)).run out.2]) ≤
          𝒟[(ITree.interp handler (ITree.query a children)).run s]
        have hcont : Measurable (fun out : P.B a × S =>
            𝒟[ITree.step ((ITree.interp handler (children out.1)).run out.2)]) := by
          simpa only [ITree.evalDist_eq_returnedMeasure, ITree.returnedMeasure_step] using
            measurable_from_prod_countable_right (fun b => hmeas (children b))
        rw [ITree.interp_run_query, evalDist_bind _ _ hcont, hhandler a s]
        simp only [ITree.evalDist_eq_returnedMeasure, ITree.returnedMeasure_step, le_refl]
    rw [ITree.runKernel_eq_denote]
    exact hbound tree state

/-- Countable separated private state discharges the measurability condition
for every client, including clients and service operations that diverge. -/
theorem Realizes.interp [Countable S] [MeasurableSingletonClass S]
    (hh : K.Realizes handler) (tree : ITree P α) (state : S) :
    𝒟[(ITree.interp handler tree).run state] = ITree.runKernel K tree state :=
  hh.interp_of_measurable (fun _ => Measurable.of_discrete) tree state

end PFunctor.KernelHandler
