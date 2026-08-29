/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.ProbabilityMassFunction.Measure
public import VCVio.EvalDist.PFunctor
public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# Primary and discrete compatibility for free-program measure semantics

The dependency-light native fold lives in `VCVio.EvalDist.PFunctorMeasure.Core`. This module
installs that fold as VCVio's primary `EvalDistSemantics` when an `IsMeasureSpec` is available and
connects it to the legacy discrete `IsProbabilitySpec` evaluator.

## Main statements

* `PFunctor.FreeM.denote_eq_toMeasure` — agreement with the `PMF` denotation of
  `VCVio.EvalDist.PFunctor`.
* `PFunctor.FreeM.denote_apply_setOf` — existing `Pr[...]` facts are measurable-event facts.
-/

@[expose] public section

open MeasureTheory ENNReal

universe u uA

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  {α β : Type u}

/-- Every free program denotes a subprobability measure, even before a measurability invariant is
available for its continuations. `Measure.bind_apply_le` gives exactly the one-sided bound needed
here; measurability is only needed to strengthen this to a probability-measure equality. -/
theorem denote_apply_univ_le_one [MeasurableSpace α] (program : FreeM P α) :
    denote program Set.univ ≤ 1 := by
  induction program with
  | pure _ => simp
  | lift_bind a cont ih =>
      refine (Measure.bind_apply_le _ MeasurableSet.univ).trans ?_
      calc
        (∫⁻ b, denote (cont b) Set.univ ∂IsMeasureSpec.toMeasure a) ≤
            ∫⁻ _b, 1 ∂IsMeasureSpec.toMeasure a := lintegral_mono ih
        _ = 1 := by simp

/-- The direct free-monad fold supplies the primary measure semantics whenever an
`IsMeasureSpec` is available. Its priority is above the generic finite-distribution adapter, so
installing a measure specification makes `𝒟[…]` unfold to `denote`; computations that only have
the legacy probability specification continue to use the adapter. -/
noncomputable instance (priority := 20) instEvalDistSemanticsFreeM :
    EvalDistSemantics (FreeM P) where
  denote := denote
  apply_univ_le_one := denote_apply_univ_le_one

/-- With a measure specification in scope, primary notation is definitionally the direct
free-monad measure fold. -/
@[simp]
theorem evalDist_eq_denote [MeasurableSpace α] (program : FreeM P α) :
    𝒟[program] = denote program := rfl

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Over a discrete-answer interface, the direct measure semantics satisfies the Giry monad
laws. -/
noncomputable instance (priority := 20) instLawfulEvalDistSemanticsFreeM :
    LawfulEvalDistSemantics (FreeM P) where
  denote_pure := denote_pure
  denote_bind := denote_bind

/-! ### Agreement with the `PMF` denotation

For a polynomial interface carrying both interpretations compatibly, the measure denotation is
the measure of the `PMF` denotation. This is what lets a `Pr[…]` statement proved against
`VCVio.EvalDist.PFunctor` be transported here rather than reproved. -/

theorem denote_eq_toMeasure [P.IsProbabilitySpec] [∀ a, Countable (P.B a)] [MeasurableSpace α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) :
    denote program = (program.liftM IsProbabilitySpec.toPMF).toMeasure := by
  induction program with
  | pure x => simpa using (PMF.toMeasure_pure x).symm
  | lift_bind a cont ih =>
      change Measure.bind (IsMeasureSpec.toMeasure a) (fun b => denote (cont b))
          = ((IsProbabilitySpec.toPMF a).bind
              fun u => (cont u).liftM IsProbabilitySpec.toPMF).toMeasure
      rw [PMF.toMeasure_bind, h a]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

/-- Every `PMF`-valued interpretation induces a measure-valued one, by taking the measure of
each answer distribution.

Deliberately not an instance, matching `PFunctor.IsUniformSpec.ofFintypeInhabited`: measure
semantics stay an explicit opt-in rather than being derived silently wherever a `PMF`
interpretation happens to be in scope. Introduce it with `letI` at a use site; the agreement
hypothesis of `denote_eq_toMeasure` then holds by `rfl`. -/
@[instance_reducible]
noncomputable def _root_.PFunctor.IsProbabilitySpec.toMeasureSpec (P : PFunctor.{uA, u})
    [∀ a, MeasurableSpace (P.B a)] [P.IsProbabilitySpec] : P.IsMeasureSpec where
  toMeasure a := (IsProbabilitySpec.toPMF a).toMeasure
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

/-- The measure of a singleton is the output probability.

This is the bridge that lets an existing `Pr[= x | _]` result be read off the measure
denotation instead of reproved against it. -/
theorem denote_apply_singleton [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (x : α) :
    denote program {x} = Pr[= x | program] := by
  rw [denote_eq_toMeasure h program,
    PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x)]
  rw [probOutput_def]
  exact (SPMF.liftM_apply _ x).symm

/-- The primary measure notation assigns the existing point probability to a singleton whenever
the measure and probability query specifications agree. -/
theorem evalDist_apply_singleton [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (x : α) :
    𝒟[program] {x} = Pr[= x | program] :=
  denote_apply_singleton h program x

/-- The measure denotation of a measurable predicate is the existing `Pr[...]` value.

The result keeps predicate notation convenient for discrete cryptographic proofs while presenting
the semantics to Mathlib as an ordinary measurable event. -/
theorem denote_apply_setOf [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (p : α → Prop) (hp : MeasurableSet {x | p x}) :
    denote program {x | p x} = Pr[p | program] := by
  rw [denote_eq_toMeasure h program,
    (program.liftM IsProbabilitySpec.toPMF).toMeasure_apply hp,
    probEvent_eq_tsum_indicator]
  apply tsum_congr
  intro x
  by_cases hx : p x
  · simp only [Set.indicator, Set.mem_ofPred_eq, hx, ↓reduceIte]
    rw [probOutput_def]
    exact (SPMF.liftM_apply _ x).symm
  · simp [Set.indicator, hx]

/-- The primary measure notation assigns the existing predicate probability to any measurable
event whenever the measure and probability query specifications agree. -/
theorem evalDist_apply_setOf [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (p : α → Prop) (hp : MeasurableSet {x | p x}) :
    𝒟[program] {x | p x} = Pr[p | program] :=
  denote_apply_setOf h program p hp

end FreeM
end PFunctor
