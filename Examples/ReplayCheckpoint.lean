/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Ordinary execution does not determine a replay experiment

Moving a checkpoint across a fair draw leaves the ordinary execution unchanged.
It changes whether two resumptions share that draw. Consequently even equality
of ordinary programs, after forgetting the checkpoint, cannot justify replay
replacement. A replay-preservation argument must retain the checkpoint boundary as part of its data.
-/

public section

namespace Examples.ReplayCheckpoint

open OracleComp MeasureTheory
open scoped ENNReal

/-- Erase a checkpoint by composing its prefix and continuation. -/
@[expose]
def run {S : Type} (before : ProbComp S) (resume : S → ProbComp Bool) : ProbComp Bool :=
  before >>= resume

/-- Compare two independent continuations resumed from one shared prefix state. -/
@[expose]
def agreement {S : Type} (before : ProbComp S) (resume : S → ProbComp Bool) : ProbComp Bool := do
  let state ← before
  let first ← resume state
  let second ← resume state
  return decide (first = second)

/-- Erasing the two different checkpoint placements gives the same program. -/
theorem ordinary_execution_equal :
    run ($ᵗ Bool) pure = run (pure ()) (fun _ => $ᵗ Bool) := by
  simp [run]

/-- A draw before the checkpoint is shared by both resumptions. -/
theorem shared_agreement : 𝒟[agreement ($ᵗ Bool) pure] {true} = 1 := by
  rw [← prEvent_eq_evalDist_singleton]
  prvcgen [agreement]
  simp

/-- Draws after the checkpoint are fresh in each resumption. -/
theorem fresh_agreement :
    𝒟[agreement (pure ()) (fun _ => $ᵗ Bool)] {true} = 1 / 2 := by
  simpa [agreement] using
    ProbComp.evalDist_decide_eq_uniformBool_half (fun _ => $ᵗ Bool) rfl

/-- Identical ordinary execution is insufficient for identical replay observations. -/
theorem replay_laws_differ :
    𝒟[agreement ($ᵗ Bool) pure] ≠
      𝒟[agreement (pure ()) (fun _ => $ᵗ Bool)] := by
  intro equal
  have event := congrArg (fun μ : Measure Bool => μ {true}) equal
  rw [shared_agreement, fresh_agreement] at event
  have inverse : (2 : ℝ≥0∞)⁻¹ = 1 := by simpa only [one_div] using event.symm
  rw [ENNReal.inv_eq_one] at inverse
  norm_num at inverse

end Examples.ReplayCheckpoint
