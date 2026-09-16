/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Instances.FinRatPMF
public import VCVioTest.MeasureSemantics

/-!
# Computation probability notation canaries

These examples exercise the same `Pr{...}[...]` syntax with a finite computation,
an optional computation, and a continuous oracle interpreted only by measures.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp PFunctor
open scoped ENNReal

namespace VCVioTest.ProbabilityNotation

example (mx : ProbComp Bool) :
    Pr{let b ← mx}[b] = 𝒟[mx] {true} := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example (mx : OptionT ProbComp Bool) :
    Pr{let b ← mx}[b] = 𝒟[mx] {true} := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example (mx : FinRatPMF.Raw Bool) :
    Pr{let b ← mx}[b] = ((mx.prob true : NNReal) : ENNReal) := by
  rw [prEvent_eq_evalDist_of_discrete]
  change 𝒟[mx] {true} = _
  exact FinRatPMF.Raw.evalDist_apply_singleton_eq_prob mx true

example : FinRatPMF.Raw.coin.prob true = 1 / 2 := by
  simpa only [one_div] using FinRatPMF.Raw.prob_coin true

example (mx : ProbComp (Fin 3)) :
    Pr{let n ← mx; let value := n.val}[value = 1] =
      𝒟[mx] {n | n.val = 1} := by
  simpa only using prEvent_eq_evalDist_of_discrete mx (fun n => n.val = 1)

open VCVioTest.MeasureSemantics in
example :
    Pr{let x ← (FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)}[x > 0] =
      gaussianReal 0 1 {x | x > 0} := by
  change (Measure.bind (gaussianReal 0 1)
    (fun x : ℝ => Measure.dirac (x > 0))) {True} = _
  rw [Measure.bind_dirac_eq_map _ (by fun_prop),
    Measure.map_apply (by fun_prop) (measurableSet_singleton True)]
  simp

open VCVioTest.MeasureSemantics in
example :
    𝒟[(pure (1 : ℝ) : OptionT (FreeM gaussSpec) ℝ)] {1} = 1 := by
  simp

open VCVioTest.MeasureSemantics in
example :
    Pr{let x ← (pure (1 : ℝ) : OptionT (FreeM gaussSpec) ℝ)}[x = 1] = 1 := by
  simp

end VCVioTest.ProbabilityNotation
