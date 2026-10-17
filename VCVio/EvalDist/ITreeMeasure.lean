/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ResumptionMeasure.Domain
public import PolyFun.ITree.DomainLaws

/-!
# Measure semantics of interaction trees

Returned mass is the least continuous interpretation into measures. Silent
steps have no probabilistic effect, including the administrative steps of
composed service machines. Weak bisimulation preserves the resulting law,
while silent divergence contributes zero returned mass.
-/

public section

open MeasureTheory OmegaCompletePartialOrder PFunctor

namespace ITree

universe u uA

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, DiscreteMeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- The subprobability law of values eventually returned by an interaction tree. -/
noncomputable def returnedMeasure (tree : ITree P α) : Measure α :=
  denote Measure.dirac (AnswerMeasure.continuousAlgebra P α) tree

@[simp] theorem returnedMeasure_pure (a : α) :
    returnedMeasure (pure (F := P) a) = Measure.dirac a :=
  denote_pure _ _ _

@[simp] theorem returnedMeasure_step (tree : ITree P α) :
    returnedMeasure (step tree) = returnedMeasure tree :=
  denote_step _ _ _

theorem returnedMeasure_query (a : P.A) (next : P.B a → ITree P α) :
    returnedMeasure (query a next) =
      (AnswerMeasure.toMeasure a).bind (fun b => returnedMeasure (next b)) := by
  simpa only [returnedMeasure, AnswerMeasure.continuousAlgebra_apply] using
    denote_query Measure.dirac (AnswerMeasure.continuousAlgebra P α) a next

/-- An infinite silent computation returns no probability mass. -/
@[simp] theorem returnedMeasure_diverge :
    returnedMeasure (diverge : ITree P α) = 0 := denote_diverge _ _

/-- The coinductive interpretation has at most unit total returned mass. -/
theorem returnedMeasure_apply_univ_le_one (tree : ITree P α) :
    returnedMeasure tree Set.univ ≤ 1 := by
  apply (domainStep Measure.dirac (AnswerMeasure.continuousAlgebra P α)).fix_induction
    (fun meaning => ∀ t, meaning t Set.univ ≤ 1) ?_ ?_ ?_ tree
  · intro t
    change (0 : Measure α) Set.univ ≤ 1
    simp
  · intro meaning hmean t
    change (match shape' t with
      | .mk (.pure a) _ => Measure.dirac a
      | .mk .step k => meaning (k PUnit.unit)
      | .mk (.query a) k => (AnswerMeasure.continuousAlgebra P α a)
          (fun b => meaning (k b))) Set.univ ≤ 1
    rcases shape' t with ⟨head, children⟩
    cases head with
    | pure a => simp
    | step => exact hmean _
    | query a =>
      dsimp only
      rw [AnswerMeasure.continuousAlgebra_apply]
      let : ∀ b, IsSubprobabilityMeasure (meaning (children b)) := fun b => ⟨hmean _⟩
      let := isSubprobabilityMeasure_bind (μ := AnswerMeasure.toMeasure a)
        (Measurable.of_discrete (f := fun b => meaning (children b))).aemeasurable
      exact measure_univ_le _
  · intro c hc t
    change (⨆ n, c n t) Set.univ ≤ 1
    have hmon : Monotone (fun n : ℕ => c n t) := fun _ _ h => c.monotone h t
    rw [Measure.iSup_apply_of_monotone (fun n => c n t) hmon _ MeasurableSet.univ]
    exact iSup_le fun n => hc n t

/-- Weak bisimulation preserves returned laws and their missing mass. -/
theorem WeakBisim.returnedMeasure_eq {t s : ITree P α} (h : WeakBisim t s) :
    returnedMeasure t = returnedMeasure s :=
  h.denote_eq Measure.dirac (AnswerMeasure.continuousAlgebra P α)

/-- The canonical tau-free embedding preserves returned laws. -/
@[simp] theorem returnedMeasure_toITree (tree : Resumption P α) :
    returnedMeasure tree.toITree = Resumption.returnedMeasure tree := by
  rw [returnedMeasure, denote_toITree, ← Resumption.returnedMeasure_eq_denote]

/-- Sequencing commutes with the returned law for measurable continuations. -/
theorem returnedMeasure_bind (tree : ITree P α) (next : α → ITree P β)
    (hnext : Measurable fun a => returnedMeasure (next a)) :
    returnedMeasure (tree >>= next) =
      (returnedMeasure tree).bind (fun a => returnedMeasure (next a)) := by
  rw [bind_eq_bind, returnedMeasure, denote_bind]
  have hfusion := denote_fusion (P := P) (α := α) Measure.dirac
    (AnswerMeasure.continuousAlgebra P α) (AnswerMeasure.continuousAlgebra P β)
    (Measure.bindContinuousLeft hnext)
    (by
      rw [Measure.bindContinuousLeft_apply]
      change (0 : Measure α).bind (fun a => returnedMeasure (next a)) = 0
      simp)
    (by
      intro a k
      simp only [Measure.bindContinuousLeft_apply, AnswerMeasure.continuousAlgebra_apply]
      exact Measure.bind_bind Measurable.of_discrete.aemeasurable hnext.aemeasurable) tree
  simp only [Measure.bindContinuousLeft_apply] at hfusion
  simp_rw [Measure.dirac_bind hnext] at hfusion
  exact hfusion.symm

/-- Interaction trees use the common successful-output probability interface. -/
noncomputable instance instEvalDistSemantics : EvalDistSemantics (ITree P) where
  denote := returnedMeasure
  apply_univ_le_one := returnedMeasure_apply_univ_le_one

/-- The evaluation measure is the continuous returned-output interpretation. -/
theorem evalDist_eq_returnedMeasure (tree : ITree P α) :
    𝒟[tree] = returnedMeasure tree := by rfl

/-- Interaction-tree probability preserves measurable monadic sequencing. -/
noncomputable instance instLawfulEvalDistSemantics : LawfulEvalDistSemantics (ITree P) where
  denote_pure value := by
    rw [evalDist_eq_returnedMeasure, pure_eq_pure, returnedMeasure_pure]
  denote_bind := returnedMeasure_bind

end ITree
