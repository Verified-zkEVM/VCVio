/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import ToMathlib.MeasureTheory.Measure.Coupling.Maximal
public import VCVio.EvalDist.DiscreteTVDist
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Discrete total variation on a finite type as half the L1 distance

For `ProbComp` computations with a finite output type, `discreteTVDist` is half the L1 distance of
the singleton probabilities, by `MeasureTheory.Measure.tvDist_eq_half_sum_abs`.
-/

public section

open MeasureTheory OracleComp

namespace discreteTVDist

/-- For `ProbComp` computations with a finite output type, `discreteTVDist` is half of the L1
distance of the singleton output probabilities. -/
theorem eq_half_sum_abs {α : Type} [Fintype α] (mx my : ProbComp α) :
    discreteTVDist mx my =
      (∑ x, |(Pr{let y ← mx}[y = x]).toReal - (Pr{let y ← my}[y = x]).toReal|) / 2 := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_singleton]
  exact Measure.tvDist_eq_half_sum_abs _ _

end discreteTVDist
