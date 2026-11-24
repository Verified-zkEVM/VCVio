/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.PRF.Perfect
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Checks for perfect PRFs and hops through the ideal world

The PRF whose key is its function table has advantage `0`. The constant PRF does not: one query
distinguishes it with advantage `1 / 2`, so `PRFScheme.prfAdvantage_eq_zero_of_evalDistEq` needs
its hypothesis. Against the same PRF, outputting the answer of that query and outputting its
negation agree in the ideal world and are at distance `1` in the real world, the sum of their
advantages, so the bound of `PRFScheme.absDiff_prfRealExperiment_le_of_ideal_eq` is attained.
-/

public section

open OracleComp OracleSpec PRFScheme
open scoped ENNReal

namespace VCVioTest.PRFIdealHops

/-- The PRF whose key is its function table. -/
@[expose] def tablePRF (D R : Type) [SampleableType (D → R)] : PRFScheme (D → R) D R where
  keygen := $ᵗ (D → R)
  eval f := f

example (adv : PRFAdversary (Fin 3) Bool) : (tablePRF (Fin 3) Bool).prfAdvantage adv = 0 :=
  prfAdvantage_eq_zero_of_evalDistEq _ (by simp [tablePRF]) adv

/-- The constant PRF. -/
@[expose] def constPRF : PRFScheme Unit Bool Bool where
  keygen := pure ()
  eval _ _ := true

/-- Query the function once and output its answer. -/
@[expose] def ask : PRFAdversary Bool Bool := functionQuery true

/-- Query the function once and output the negation of its answer. -/
@[expose] def askNot : PRFAdversary Bool Bool :=
  (Bool.not <$> functionQuery true : OracleComp (PRFOracleSpec Bool Bool) Bool)

theorem real_ask : Pr{let b ← constPRF.prfRealExperiment ask}[b = true] = 1 := by
  simp [prfRealExperiment, constPRF, ask]

theorem real_askNot : Pr{let b ← constPRF.prfRealExperiment askNot}[b = true] = 0 := by
  simp [prfRealExperiment, constPRF, askNot]

theorem ideal_ask : Pr{let b ← prfIdealExperiment ask}[b = true] = 2⁻¹ := by
  simp [prfIdealExperiment, ask, StateT.run'_eq, SampleableType.prEvent_uniformSample_eq_singleton]

theorem ideal_askNot : Pr{let b ← prfIdealExperiment askNot}[b = true] = 2⁻¹ := by
  simp [prfIdealExperiment, askNot, StateT.run'_eq,
    SampleableType.prEvent_uniformSample_eq_singleton]

theorem prfAdvantage_ask : constPRF.prfAdvantage ask = 2⁻¹ := by
  rw [prfAdvantage_eq_absDiff, real_ask, ideal_ask, ENNReal.absDiff,
    tsub_eq_zero_of_le (a := 2⁻¹) (by simp), add_zero]
  simp

theorem prfAdvantage_askNot : constPRF.prfAdvantage askNot = 2⁻¹ := by
  rw [prfAdvantage_eq_absDiff, real_askNot, ideal_askNot, ENNReal.absDiff_zero_left]

/-- The constant PRF is not perfect. -/
example : ¬ (constPRF.eval <$> constPRF.keygen =ᵈ ($ᵗ (Bool → Bool) : ProbComp (Bool → Bool))) :=
  fun h => by simpa [prfAdvantage_ask] using prfAdvantage_eq_zero_of_evalDistEq constPRF h ask

/-- The bound of the hop is attained: the two distinguishers agree in the ideal world and are at
distance `1 = 1 / 2 + 1 / 2` in the real world. -/
example : ENNReal.absDiff (Pr{let b ← constPRF.prfRealExperiment ask}[b = true])
      (Pr{let b ← constPRF.prfRealExperiment askNot}[b = true]) =
    constPRF.prfAdvantage ask + constPRF.prfAdvantage askNot := by
  rw [real_ask, real_askNot, prfAdvantage_ask, prfAdvantage_askNot, ENNReal.inv_two_add_inv_two,
    ENNReal.absDiff_zero_right]

example : ENNReal.absDiff (Pr{let b ← constPRF.prfRealExperiment ask}[b = true])
      (Pr{let b ← constPRF.prfRealExperiment askNot}[b = true]) ≤
    constPRF.prfAdvantage ask + constPRF.prfAdvantage askNot :=
  constPRF.absDiff_prfRealExperiment_le_of_ideal_eq ask askNot (ideal_ask.trans ideal_askNot.symm)

end VCVioTest.PRFIdealHops
