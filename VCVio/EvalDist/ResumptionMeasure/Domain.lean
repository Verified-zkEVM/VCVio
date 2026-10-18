/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ResumptionMeasure
public import ToMathlib.MeasureTheory.Measure.OmegaCompletePartialOrder
public import PolyFun.PFunctor.Resumption.DomainTruncate
public import PolyFun.PFunctor.Resumption.DomainLaws

/-!
# Returned measures as continuous interpretations

The increasing returned-output law is PolyFun's least continuous-algebra
interpretation into Mathlib measures. This supplies query and substitution
laws and identifies the measure of every well-founded client without a uniform
query bound. Only primitive answers are discrete; result spaces are arbitrary.
-/

public section

open MeasureTheory OmegaCompletePartialOrder

universe u uA

namespace PFunctor

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, DiscreteMeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- The continuous query algebra induced by discrete primitive answer measures. -/
noncomputable def AnswerMeasure.continuousAlgebra (P : PFunctor.{uA, u})
    [∀ a, MeasurableSpace (P.B a)] [∀ a, DiscreteMeasurableSpace (P.B a)]
    [P.AnswerMeasure] (α : Type u) [MeasurableSpace α] :
    Resumption.ContinuousAlgebra P (Measure α) :=
  fun a => Measure.bindContinuousRight (AnswerMeasure.toMeasure a)

@[simp] theorem AnswerMeasure.continuousAlgebra_apply (a : P.A) (f : P.B a → Measure α) :
    continuousAlgebra P α a f = (AnswerMeasure.toMeasure a).bind f :=
  Measure.bindContinuousRight_apply _ _

/-- The ordinary finite interpretation is the corresponding polynomial fold. -/
theorem FreeM.denote_eq_foldFreeM (program : FreeM P α) :
    FreeM.denote program =
      program.foldFreeM Measure.dirac (fun a => AnswerMeasure.continuousAlgebra P α a) := by
  induction program with
  | pure value => simp
  | lift_bind a next ih =>
      change FreeM.denote (.liftBind a next) = _
      rw [FreeM.denote_liftBind _ _ Measurable.of_discrete.aemeasurable,
        FreeM.foldFreeM_lift_bind, AnswerMeasure.continuousAlgebra_apply]
      exact congrArg (Measure.bind (AnswerMeasure.toMeasure a)) (funext ih)

namespace Resumption

/-- Finite returned-output measures are continuous-algebra truncation folds. -/
theorem outputMeasure_eq_foldTruncate (fuel : ℕ) (tree : Resumption P α) :
    outputMeasure fuel tree =
      foldTruncate Measure.dirac (AnswerMeasure.continuousAlgebra P α) fuel tree := by
  induction fuel generalizing tree with
  | zero =>
    rw [foldTruncate_zero]
    rcases ht : dest tree with value | ⟨a, next⟩
    · have he : tree = pure value := eq_of_dest_eq (ht.trans (dest_pure value).symm)
      simp [he]
    · have he : tree = query a next := eq_of_dest_eq (ht.trans (dest_query a next).symm)
      simp only [he, outputMeasure_query_zero]
      rfl
  | succ fuel ih =>
    rw [foldTruncate_succ]
    rcases ht : dest tree with value | ⟨a, next⟩
    · have he : tree = pure value := eq_of_dest_eq (ht.trans (dest_pure value).symm)
      simp [he]
    · have he : tree = query a next := eq_of_dest_eq (ht.trans (dest_query a next).symm)
      rw [he, outputMeasure_query_succ]
      dsimp only
      rw [AnswerMeasure.continuousAlgebra_apply]
      exact congrArg (Measure.bind (AnswerMeasure.toMeasure a)) (funext fun b => ih (next b))

/-- The returned-output limit is the least continuous measure interpretation. -/
theorem returnedMeasure_eq_denote (tree : Resumption P α) :
    returnedMeasure tree = denote Measure.dirac (AnswerMeasure.continuousAlgebra P α) tree := by
  rw [denote_eq_sup_truncations]
  change (⨆ n, outputMeasure n tree) = ⨆ n,
    foldTruncate Measure.dirac (AnswerMeasure.continuousAlgebra P α) n tree
  simp_rw [outputMeasure_eq_foldTruncate]

/-- Every well-founded free program has the same finite and resumption denotation. -/
theorem returnedMeasure_toResumption (program : FreeM P α) :
    returnedMeasure program.toResumption = FreeM.denote program := by
  rw [returnedMeasure_eq_denote, denote_toResumption, FreeM.denote_eq_foldFreeM]

/-- A query's returned law is the bind of its answer measure and continuation laws. -/
theorem returnedMeasure_query (a : P.A) (next : P.B a → Resumption P α) :
    returnedMeasure (query a next) =
      (AnswerMeasure.toMeasure a).bind (fun b => returnedMeasure (next b)) := by
  simp_rw [returnedMeasure_eq_denote]
  simpa only [AnswerMeasure.continuousAlgebra_apply] using
    denote_query (D := Measure α) Measure.dirac (AnswerMeasure.continuousAlgebra P α) a next

/-- Returned measures respect sequencing into a measurably varying continuation. -/
theorem returnedMeasure_bind (tree : Resumption P α) (next : α → Resumption P β)
    (hnext : Measurable fun a => returnedMeasure (next a)) :
    returnedMeasure (tree >>= next) =
      (returnedMeasure tree).bind (fun a => returnedMeasure (next a)) := by
  rw [bind_eq_bind, returnedMeasure_eq_denote, denote_bind]
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
  simpa only [returnedMeasure_eq_denote] using hfusion.symm

/-- Resumptions expose their returned-output law through the common probability interface. -/
noncomputable instance instEvalDistSemantics : EvalDistSemantics (Resumption P) where
  denote := returnedMeasure
  apply_univ_le_one := returnedMeasure_apply_univ_le_one

/-- The public evaluation equation for a resumption. -/
theorem evalDist_eq_returnedMeasure (tree : Resumption P α) :
    𝒟[tree] = returnedMeasure tree := by rfl

/-- The returned-output interpretation preserves measurable monadic sequencing. -/
noncomputable instance instLawfulEvalDistSemantics : LawfulEvalDistSemantics (Resumption P) where
  denote_pure value := by
    rw [evalDist_eq_returnedMeasure, pure_eq_pure, returnedMeasure_pure]
  denote_bind := returnedMeasure_bind

end Resumption
end PFunctor
