/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics

/-!
# Events over several draws as triples

An event over several draws, `Pr{let x ← oa; let y ← ob x}[p x y]`, is the probability of a
proposition-valued computation. `prEvent_eq_wp` states it as the expectation of the indicator of
the result, and `vcstep` lowers its probability-one and lower-bound goals to triples with that
indicator as postcondition.
-/

public section

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal

namespace VCVioTest.ProgramLogic.EventLowering

example (mx : ProbComp Prop) : prEvent mx = wp mx (fun P => 𝟙⟦P⟧) :=
  prEvent_eq_wp mx

example
    (h : Triple 1 (do let b ← $ᵗ Bool; (fun c => (b || c) = true) <$> ($ᵗ Bool))
      (fun P => 𝟙⟦P⟧)) :
    Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b || c) = true] = 1 := by
  vcstep
  exact h

example (r : ℝ≥0∞)
    (h : Triple r (do let b ← $ᵗ Bool; (fun c => (b && c) = true) <$> ($ᵗ Bool))
      (fun P => 𝟙⟦P⟧)) :
    r ≤ Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) = true] := by
  vcstep
  exact h

end VCVioTest.ProgramLogic.EventLowering
