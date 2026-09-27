/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.MeasurableSpace.Option
public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.EvalDist.PFunctorMeasure

/-!
# Measure-level replay forking bound

The replay forking lemma is proved through VCVio's discrete probability surface.
This file transports its final success bound to the Mathlib measure denotation
of the same oracle programs. The seeded forking lemma is stated natively in
`VCVio.CryptoFoundations.SeededFork`.

These are compatibility corollaries rather than new forking arguments. The
measure semantics is the canonical one induced by the existing per-query
probability interpretation, stated on the primary measure `𝒟[…]`, and
`evalDist_apply` identifies its measurable success event with the probability
used by the original theorem.
-/

@[expose] public section

open MeasureTheory OracleSpec ENNReal Finset

namespace OracleComp

/-- The canonical measure semantics induced by an oracle specification's
existing probability semantics. This instance is local so measure semantics
remain an explicit opt-in outside this compatibility module. -/
noncomputable local instance measureSpecOfProbability
    {ι : Type} {spec : OracleSpec ι}
    [∀ i, MeasurableSpace (spec.Range i)] [IsProbabilitySpec spec] :
    PFunctor.IsMeasureSpec spec.toPFunctor :=
  PFunctor.IsProbabilitySpec.toMeasureSpec spec.toPFunctor

section replay

variable {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
  [∀ i, MeasurableSpace (spec.Range i)]
  [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [MeasurableSpace α]

/-- The replay/context forking bound, stated as the Mathlib measure of the
successful-result event. -/
theorem le_evalDist_isSome_contextFork
    [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      𝒟[contextFork main qb i cf] {result | result.isSome} := by
  rw [evalDist_apply _ Option.measurableSet_isSome]
  exact le_probEvent_isSome_contextFork main qb i cf hreach

end replay

end OracleComp
