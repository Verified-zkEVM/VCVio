/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio

/-!
# Discrete total variation and finite-support comparisons

A uniform bit against a fixed bit is the running example. Their distance is one half by the
finite-type L1 formula, the event bound is attained on the bit the fixed computation never
outputs, and a common continuation or an independent second draw stays within the stated bounds.
Singleton masses decide equality of the discrete measures of finitely supported computations.
-/

public section

open OracleComp

namespace VCVioTest.DiscreteTVDist

/-- A uniform bit is at distance one half from a fixed bit. -/
theorem discreteTVDist_uniform_pure_true :
    discreteTVDist ($ᵗ Bool) (pure true : ProbComp Bool) = 1 / 2 := by
  rw [discreteTVDist.eq_half_sum_abs]
  simp only [Fintype.sum_bool, SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num

/-- The event bound is attained: the fixed bit never outputs `false`, and the uniform bit does so
with exactly the distance between them. -/
example :
    Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[b = false] =
      Pr{let b ← (pure true : ProbComp Bool)}[b = false] +
        ENNReal.ofReal (discreteTVDist ($ᵗ Bool) (pure true : ProbComp Bool)) := by
  rw [discreteTVDist_uniform_pure_true, SampleableType.prEvent_uniformSample_eq_singleton]
  simp

/-- A common continuation, here negation, does not move the two bits further apart. -/
example :
    discreteTVDist (do let b ← ($ᵗ Bool : ProbComp Bool); pure (!b))
      (do let b ← (pure true : ProbComp Bool); pure (!b)) ≤ 1 / 2 :=
  (discreteTVDist.bind_le _ _ _).trans_eq discreteTVDist_uniform_pure_true

/-- Two independent uniform bits are within the sum of the coordinate distances of two fixed
bits. -/
example :
    discreteTVDist
      (do
        let a ← ($ᵗ Bool : ProbComp Bool)
        let b ← ($ᵗ Bool : ProbComp Bool)
        pure (a, b))
      (do
        let a ← (pure true : ProbComp Bool)
        let b ← (pure true : ProbComp Bool)
        pure (a, b)) ≤ 1 / 2 + 1 / 2 :=
  (discreteTVDist.pair_le _ _ _ _).trans_eq (by rw [discreteTVDist_uniform_pure_true])

/-- Negating a uniform bit leaves its discrete measure unchanged, decided on singleton masses. -/
example :
    (letI : MeasurableSpace Bool := ⊤;
      𝒟[(not <$> ($ᵗ Bool) : ProbComp Bool)] = 𝒟[($ᵗ Bool : ProbComp Bool)]) :=
  evalDist_eq_of_prEvent_eq_eq _ _ (Set.toFinite _) (Set.toFinite _) fun x => by
    obtain ⟨x, rfl⟩ : ∃ z, x = !z := ⟨!x, by simp⟩
    rw [prEvent_map_injective _ (Function.LeftInverse.injective Bool.not_not),
      SampleableType.prEvent_uniformSample_eq_singleton,
      SampleableType.prEvent_uniformSample_eq_singleton]

end VCVioTest.DiscreteTVDist
