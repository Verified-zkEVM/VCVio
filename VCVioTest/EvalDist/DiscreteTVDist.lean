/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio

/-!
# Discrete total variation and finite-support comparisons

The distance `discreteTVDist` is stated without a measurable-space hypothesis, contracts under a
common continuation, transfers event bounds, and computes on a finite type by half the L1 distance.
Singleton comparisons of finitely supported computations determine their discrete measures.
-/

open OracleComp

namespace VCVioTest.DiscreteTVDist

variable {α β : Type}

example (mx : ProbComp α) : discreteTVDist mx mx = 0 := by
  simp

example (mx my : ProbComp α) (k : α → ProbComp β) :
    discreteTVDist (mx >>= k) (my >>= k) ≤ discreteTVDist mx my :=
  discreteTVDist.bind_le mx my k

example (mx my : ProbComp α) (p : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← my}[p x] + ENNReal.ofReal (discreteTVDist mx my) :=
  prEvent_le_prEvent_add_ofReal_discreteTVDist mx my p

example (ma na : ProbComp α) (mb nb : ProbComp β) :
    discreteTVDist (do let a ← ma; let b ← mb; pure (a, b)) (do let a ← na; let b ← nb; pure (a, b))
      ≤ discreteTVDist ma na + discreteTVDist mb nb :=
  discreteTVDist.pair_le ma na mb nb

/-- A uniform bit is at distance one half from a fixed bit. -/
example : discreteTVDist ($ᵗ Bool) (pure true : ProbComp Bool) = 1 / 2 := by
  rw [discreteTVDist.eq_half_sum_abs]
  simp only [Fintype.sum_bool, SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num

/-- Equal singleton masses of finitely supported computations give equal discrete measures. -/
example (mx my : ProbComp α) (hx : (support mx).Finite) (hy : (support my).Finite)
    (h : ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x]) :
    (letI : MeasurableSpace α := ⊤; 𝒟[mx] = 𝒟[my]) :=
  evalDist_eq_of_prEvent_eq_eq mx my hx hy h

end VCVioTest.DiscreteTVDist
