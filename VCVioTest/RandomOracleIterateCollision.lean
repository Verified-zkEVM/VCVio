/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.IterateCollision
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Iterate-collision bound checks

With `n = 0` there is no pair of iterates, and the bound is `0`. With `n = 1` on `Bool` the event is
that the start is a fixed point of a uniform function, of probability `1 / 2`, which is the bound
`1 · 1 / |Bool|`: the bound is attained and cannot be lowered.
-/

public section

open OracleComp ENNReal

namespace VCVioTest.IterateCollision

example (s : Bool) :
    Pr{let g ← $ᵗ (Bool → Bool)}[∃ a b, a < b ∧ b ≤ 0 ∧ g^[a] s = g^[b] s] ≤ 0 :=
  (prEvent_iterate_collision_le s 0).trans_eq (by simp)

/-- With one step, the iterates collide exactly when the start is a fixed point. -/
theorem prEvent_iterate_collision_one :
    Pr{let g ← $ᵗ (Bool → Bool)}[∃ a b, a < b ∧ b ≤ 1 ∧ g^[a] true = g^[b] true] = 2⁻¹ := by
  rw [prEvent_congr _ _ (fun g => g true = true) fun g => ⟨fun ⟨a, b, hab, hb, he⟩ => by
    obtain rfl : b = 1 := by omega
    obtain rfl : a = 0 := by omega
    exact he.symm, fun h => ⟨0, 1, Nat.zero_lt_one, le_rfl, h.symm⟩⟩]
  rw [SampleableType.prEvent_uniformSample,
    show (Finset.univ.filter fun g : Bool → Bool => g true = true).card = 2 by decide,
    show Fintype.card (Bool → Bool) = 2 * 2 by decide, Nat.cast_mul,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc, Nat.cast_ofNat,
    ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top, mul_one]

/-- The bound at `n = 1` on `Bool` is `1 / 2`, the probability above. -/
example : ((1 : ℕ) : ℝ≥0∞) * ((1 : ℕ) / Nat.card Bool) = 2⁻¹ := by
  simp

end VCVioTest.IterateCollision
