/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioFoxglove.Independence
public import VCVioFoxglove.Specs

/-!
# Guessing a fair bit, by independence

`ProbComp.evalDist_decide_eq_uniformBool_half` (`VCVio/OracleComp/Constructions/SampleableType/
Measure.lean`, 31 lines of measure bookkeeping) restated and proved in Foxglove: the guess's law
does not depend on the bit, so the bit and the guess are independent (`wp_bind_pair_sep`), and an
independent guess of a uniform bit is right half the time (`prEvent_eq_of_wp_sep_uniform`).
-/

@[expose] public section

namespace Foxglove.Examples

open Interp OracleComp

/-- **A fair hidden bit is guessed with probability one half** when the guess distribution does
not depend on that bit. -/
theorem evalDist_decide_eq_uniformBool_half (f : Bool → ProbComp Bool)
    (heq : 𝒟[f true] = 𝒟[f false]) :
    𝒟[do let b ← ($ᵗ Bool); let b' ← f b; return decide (b = b')] {true} = 1 / 2 := by
  let : MeasurableSpace Bool := ⊤
  -- the bit and the guess are independent: the guess has the same law for either bit
  have h := wp_bind_pair_sep (F := f) (wp_uniformSample Bool) fun b ↦
    wp_of_evalDist_eq (by cases b <;> simp [heq]) (wp_lawPMF (f true))
  have := prEvent_eq_of_wp_sep_uniform h
  rw [prEvent_eq_evalDist_decide] at this
  simpa [one_div] using this

end Foxglove.Examples
