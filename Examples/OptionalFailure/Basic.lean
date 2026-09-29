/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Monad.Option

/-!
# Optional failure as missing mass

`OptionT ProbComp` carries two separately supplied interpretations: an operational support, for
qualitative reasoning about which values can be returned, and a successful-output measure, for
quantitative reasoning. Failure contributes no successful output, so it shows up as mass missing
from the measure; the failure-completed measure `Measure.withFailure` records that mass at `none`.

The example samples a Boolean uniformly and `guard`s on heads: half of the runs return `()`, and
the other half of the mass is missing.
-/

@[expose] public section

open OracleComp MeasureTheory ENNReal

namespace OptionalFailureExample

/-- Sample a Boolean uniformly; commit only on heads. -/
noncomputable def maybeHeads : OptionT ProbComp Unit := do
  let b ← $ᵗ Bool
  guard (b = true)

/-- The success branch has probability `1/2`. -/
theorem evalDist_maybeHeads : 𝒟[maybeHeads] {()} = 1 / 2 := by
  rw [maybeHeads, OptionT.evalDist_liftM_bind_guard, prEvent_eq_evalDist_singleton]
  simp

/-- Since `maybeHeads` returns `Unit`, its whole successful mass is the success probability. -/
theorem evalDist_maybeHeads_univ : 𝒟[maybeHeads] Set.univ = 1 / 2 := by
  rw [show (Set.univ : Set Unit) = {()} from Set.univ_unique, evalDist_maybeHeads]

/-- The failure-completed measure puts the missing half at `none`. -/
theorem withFailure_maybeHeads_none : (𝒟[maybeHeads]).withFailure {none} = 1 / 2 := by
  rw [Measure.withFailure_apply_none, evalDist_maybeHeads_univ, one_div, ENNReal.one_sub_inv_two]

/-- Qualitatively, `()` is a possible result: the support comes from the operational
interpretation, independently of how much mass the measure assigns it. -/
theorem mem_support_maybeHeads : () ∈ support maybeHeads := by
  simp [maybeHeads]

end OptionalFailureExample
