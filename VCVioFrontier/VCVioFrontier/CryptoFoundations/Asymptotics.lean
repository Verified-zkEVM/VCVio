/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Crypto.Game

public import CslibFrontier.Crypto.Game
public import ToMathlib.MeasureTheory.Measure.Bool
public import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Uniform security for Boolean games

Frontier observes the distance between two success probabilities in the nonnegative reals.
VCVio observes the distance between the masses of the success event in the extended
nonnegative reals. Coercion preserves this observation and superpolynomial decay.
-/

public section

namespace VCVioFrontier

open Filter Asymptotics MeasureTheory
open scoped ENNReal NNReal Topology

/-- Finite advantages have the same asymptotic decay in the two probability codomains. -/
theorem negligible_coe_iff (f : ℕ → ℝ≥0) :
    negligible (fun n ↦ (f n : ℝ≥0∞)) ↔ Cslib.Crypto.Negligible f := by
  rw [negligible_iff_superpolynomialDecay_toReal fun _ ↦ ENNReal.coe_ne_top]
  unfold Cslib.Crypto.Negligible SuperpolynomialDecay
  refine forall_congr' fun k ↦ ?_
  simpa using (NNReal.tendsto_coe (m := fun n : ℕ ↦ (n : ℝ≥0) ^ k * f n)
    (f := atTop) (x := 0))

/-- Passing from Boolean output laws to their measures preserves distinguishing advantage. -/
theorem boolDist_toMeasure_eq_advantage (p q : PMF Bool) :
    p.toMeasure.boolDist q.toMeasure = (Cslib.Crypto.Game.advantage p q : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (Measure.boolDist_ne_top _ _) ENNReal.coe_ne_top).mp
  rw [Measure.toReal_boolDist, ENNReal.coe_toReal, Cslib.Crypto.Game.coe_advantage,
    p.toMeasure_apply_singleton true (measurableSet_singleton _),
    q.toMeasure_apply_singleton true (measurableSet_singleton _)]
  rfl

/-- Frontier indistinguishability is security of the corresponding VCVio measure game,
with the admissibility test applied to the entire adversary family. -/
theorem secureAgainst_iff_indistinguishable {Adv : Type*} (left right : Adv → ℕ → Cslib.Crypto.Game)
    (admissible : Adv → Prop) :
    (SecurityGame.mk fun a n ↦ (left a n).toMeasure.boolDist (right a n).toMeasure).secureAgainst
      admissible ↔ Cslib.Crypto.Game.Indistinguishable left right admissible := by
  simp only [SecurityGame.secureAgainst, Cslib.Crypto.Game.Indistinguishable,
    boolDist_toMeasure_eq_advantage, negligible_coe_iff]

end VCVioFrontier
