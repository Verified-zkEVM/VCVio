/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.FirstMoment
public import VCVio.OracleComp.QueryTracking.CountingOracle.FreshTrials
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A warm repeat or an additional fresh trial determined by the first response

A repeated query returns a cached bit and leaves both counters alone.
From any starting cache, expected successes equal half the expected number of fresh trials.
-/

public section

open OracleSpec OracleComp randomOracle.FreshTrials
open scoped ENNReal

namespace VCVioTest.FreshTrialMean

/-- Repeat the same address after true and switch to the other address after false. -/
def retry : OracleComp (Bool →ₒ Bool) Bool := do
  if ← query (spec := Bool →ₒ Bool) false then
    query (spec := Bool →ₒ Bool) false
  else query (spec := Bool →ₒ Bool) true

/-- Starting with either address already cached is allowed.
Only cache misses contribute to the expected trial and success counts. -/
theorem retry_mean (c : (Bool →ₒ Bool).QueryCache) :
    let m := (simulateQ (observe 2 {true} (fun _ _ => true)) retry).run (c, 0, 0)
    (∑' z, Pr{let u ← m}[u = z] * (z.2.2.2 : ℝ≥0∞)) =
      ENNReal.ofReal (1 / 2) * ∑' z, Pr{let u ← m}[u = z] * (z.2.2.1 : ℝ≥0∞) := by
  apply BernoulliMoment.expected_successes (countsTrials 2 _ _ _ ?_) retry _ rfl rfl
  have singleton : (fun y : Bool => y ∈ ({true} : Finset Bool)) = (· = true) := by
    funext y
    simp
  change prEvent ((fun y : Bool => y ∈ ({true} : Finset Bool)) <$> ($ᵗ Bool)) = _
  rw [singleton, SampleableType.prEvent_uniformSample_eq_singleton]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

end VCVioTest.FreshTrialMean
