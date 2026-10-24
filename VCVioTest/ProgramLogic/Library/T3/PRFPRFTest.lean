/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.PRF.PRF

/-!
# Tests for the PRF experiment handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.PRF.PRF`: repeated function
queries agree in both worlds, the frame of an opaque distinguisher, and fresh-point uniformity.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.PRF

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP PRFScheme ENNReal

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {K D R : Type}

/-- Two function queries at the same point, around a uniform draw. -/
abbrev twoQueries (d : D) (n : ℕ) : OracleComp (PRFOracleSpec D R) (R × R) := do
  let a ← functionQuery d
  let _ ← (PRFOracleSpec D R).query (Sum.inl n)
  let b ← functionQuery d
  return (a, b)

/-- In the real world both queries return the keyed value. -/
example (prf : PRFScheme K D R) (k : K) (d : D) (n : ℕ) :
    ⦃ True ⦄ simulateQ (prf.prfRealQueryImpl k) (twoQueries d n)
    ⦃ fun z => z.1 = prf.eval k d ∧ z.2 = prf.eval k d ⦄ := by
  vcgen

variable [DecidableEq D] [SampleableType R]

/-- In the ideal world the two queries agree, and the answer is cached. -/
example (d : D) (n : ℕ) :
    ⦃ fun _ => True ⦄ simulateQ (prfIdealQueryImpl (D := D) (R := R)) (twoQueries d n)
    ⦃ fun z c => z.1 = z.2 ∧ c d = some z.1 ⦄ := by
  vcgen
  grind

/-- An opaque distinguisher keeps every cached answer, so a later query at a cached point returns
it. -/
example {α : Type} (adv : OracleComp (PRFOracleSpec D R) α) (d : D) (u : R) :
    ⦃ fun c => c d = some u ⦄
      simulateQ (prfIdealQueryImpl (D := D) (R := R)) (do let _ ← adv; functionQuery d)
    ⦃ fun v _ => v = u ⦄ := by
  vcgen
  grind

/-- A fresh ideal query is uniform. -/
example [Fintype R] (d : D) (r : R) :
    Pr{let v ← (prfIdealQueryImpl (D := D) (R := R) (.inr d)).run' ∅}[v = r] =
      (Fintype.card R : ℝ≥0∞)⁻¹ :=
  prEvent_prfIdealQueryImpl_run'_eq_of_eq_none rfl r

/-- The real experiment's run is the ideal run from a cache that already agrees with the key. -/
example (prf : PRFScheme K D R) (adv : PRFAdversary D R) :
    prf.prfRealExperiment adv = prf.keygen >>= fun k =>
      (simulateQ (prfIdealQueryImpl (D := D) (R := R)) adv).run'
        (QueryCache.ofFn fun d => some (prf.eval k d)) := by
  simp only [prfRealExperiment]
  exact bind_congr fun k => (prfRealQueryImpl_eq_ideal_of_agree prf k (fun _ => rfl) adv).symm

end VCVioTest.ProgramLogic.Library.T3.PRF
