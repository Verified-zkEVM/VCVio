/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.ProbabilityTheory.FinRatPMF.Measure
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Native measure semantics for executable rational sampling

The rational sampler denotes a finite sum of weighted Dirac measures. Its interpretation
preserves pure and measurable bind on arbitrary measurable spaces and has total mass one.
Decidable events and singleton probabilities can be evaluated with rational arithmetic.
-/

public section

open MeasureTheory

universe u

namespace FinRatPMF.Raw

noncomputable instance : EvalDistSemantics Raw where
  denote := toMeasure
  apply_univ_le_one p := le_of_eq (toMeasure_apply_univ p)

instance : LawfulEvalDistSemantics Raw where
  denote_pure := toMeasure_pure
  denote_bind := toMeasure_bind

variable {α : Type u} [MeasurableSpace α]

/-- The denotation is the raw distribution's native measure. -/
theorem evalDist_eq_toMeasure (p : Raw α) : 𝒟[p] = p.toMeasure := rfl

/-- Executable rational sampling has total mass one. -/
theorem evalDist_apply_univ (p : Raw α) : 𝒟[p] Set.univ = 1 := toMeasure_apply_univ p

instance (p : Raw α) : IsProbabilityMeasure 𝒟[p] := inferInstanceAs
  (IsProbabilityMeasure p.toMeasure)

/-- Singleton mass is computable with rational arithmetic. -/
@[simp]
theorem evalDist_apply_singleton_eq_prob [MeasurableSingletonClass α] [DecidableEq α]
    (p : Raw α) (x : α) : 𝒟[p] {x} = ((p.prob x : NNReal) : ENNReal) :=
  toMeasure_apply_singleton p x

/-- Uniform rational sampling denotes the uniform probability measure. -/
@[simp]
theorem evalDist_uniform [MeasurableSingletonClass α] [FinEnum α] [Inhabited α] :
    𝒟[Raw.uniform (α := α)] = ProbabilityTheory.uniformOn Set.univ :=
  toMeasure_uniform

/-- A decidable event has the rational sum of its tickets' weights. -/
theorem evalDist_apply (p : Raw α) {event : Set α} (hevent : MeasurableSet event)
    [DecidablePred (· ∈ event)] :
    𝒟[p] event = (((p.toList.filter fun a ↦ a.1 ∈ event).map Prod.snd).sum : NNReal) :=
  toMeasure_apply p hevent

end FinRatPMF.Raw
