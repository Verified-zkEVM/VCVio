/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.FinRatPMF
public import VCVio.EvalDist.ProbabilityNotation
import Mathlib.Tactic.NormNum

/-!
# Native rational sampling canaries

These examples use measure semantics without a discrete probability backend. They exercise
duplicate and zero-weight tickets, final event checks, continuous result spaces, and measurable
bind. Rational event evaluation remains executable.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace VCVioTest.FinRatPMF

private def tickets : FinRatPMF.Raw ℕ :=
  ⟨#[(1, 0), (2, 1 / 3), (2, 2 / 3)], by norm_num⟩

example : tickets.prob 2 = 1 := by
  norm_num [tickets, FinRatPMF.Raw.prob, FinRatPMF.Raw.probOfList, FinRatPMF.Raw.toList]

example : tickets.support = {2} := by
  norm_num [tickets, FinRatPMF.Raw.support, FinRatPMF.Raw.supportOfList,
    FinRatPMF.Raw.toList]

private theorem tickets_evalDist : 𝒟[tickets] = Measure.dirac 2 := by
  rw [FinRatPMF.Raw.evalDist_eq_toMeasure]
  simp [FinRatPMF.Raw.toMeasure, FinRatPMF.Raw.toList, tickets, ← add_smul]
  norm_num

example : Pr{let x ← tickets}[x = 2] = 1 := by
  rw [prEvent_eq_evalDist_of_discrete, tickets_evalDist]
  simp

/-- Pure real-valued rational sampling simplifies its final event by the generic pure API. -/
theorem prEvent_pure_real :
    Pr{let x ← (pure (3 : ℝ) : FinRatPMF.Raw ℝ)}[x > 0] = 1 := by simp

example (f : ℕ → FinRatPMF.Raw ℝ) : 𝒟[tickets >>= f] = 𝒟[f 2] := by
  rw [evalDist_bind_of_discrete, tickets_evalDist, Measure.dirac_bind .of_discrete]

example (g : ℕ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g x ∂𝒟[tickets] = g 2 := by
  rw [tickets_evalDist, lintegral_dirac' 2 hg]

end VCVioTest.FinRatPMF
