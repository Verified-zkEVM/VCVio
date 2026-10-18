/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Categorical.Semantics

/-! # Rational categorical laws through ordinary imports -/

public section

open MeasureTheory ProbabilityTheory PFunctor UniformThreshold
open scoped ENNReal

namespace CategoricalTest

universe u

/-- The syntax and kernel law allow result values in a different universe from the bit interface. -/
example {α : Type u} [MeasurableSpace α] (distribution : FinRatPMF.Raw α) :
    (FreeM.runKernel answerKernel (Categorical.client distribution) Prefix.empty).map Prod.fst =
      distribution.toMeasure := Categorical.concrete_law distribution

/-- Zero-weight tickets and duplicate values denote a single constant output. -/
@[expose] def duplicateTickets : FinRatPMF.Raw Nat :=
  ⟨#[(0, 0), (7, 1 / 3), (7, 2 / 3)], by norm_num⟩

example :
    (FreeM.runKernel answerKernel (Categorical.client duplicateTickets) Prefix.empty).map
      Prod.fst = Measure.dirac 7 := by
  rw [Categorical.concrete_law]
  simp [FinRatPMF.Raw.toMeasure, FinRatPMF.Raw.toList, duplicateTickets, ← add_smul]
  norm_num

/-- A Borel result space needs no discrete instance. -/
example (distribution : FinRatPMF.Raw ℝ) :
    (𝒟[ITree.ofResumptionWithTau
      ((Categorical.compiled distribution).denote ((), Prefix.empty))]).map Prod.fst =
        distribution.toMeasure := Categorical.compiled_law distribution

example (distribution : FinRatPMF.Raw Nat) (fuel : ℕ) :
    distribution.toMeasure.etvDist
      (𝒟[cappedClient (fun _ _ => fuel) (Categorical.client distribution) Prefix.empty].map
        Prod.fst) ≤ (distribution.toList.length - 1 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ fuel :=
  Categorical.capped_error_le distribution fuel

end CategoricalTest
