/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Second-order Taylor bounds from a global bound on the second derivative

For `g : ℝ → ℝ` with derivative `g'` and second derivative `g''` everywhere, a bound `g'' ≤ M`
gives `g (x + h) - g x - h · g' x ≤ M h² / 2` (`Real.taylor_two_sub_le`), and `|g''| ≤ M` gives
the two-sided form (`Real.abs_taylor_two_sub_le`).
-/

public section

namespace Real

/-- With `g'' ≤ M` everywhere, `g (x + h) - g x - h · g' x ≤ M h² / 2`. -/
theorem taylor_two_sub_le {g g' g'' : ℝ → ℝ} {M : ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hM : ∀ x, g'' x ≤ M) (x h : ℝ) :
    g (x + h) - g x - h * g' x ≤ M * h ^ 2 / 2 := by
  set k : ℝ → ℝ := fun t => g (x + t) - g x - t * g' x - M * t ^ 2 / 2
  set k' : ℝ → ℝ := fun t => g' (x + t) - g' x - M * t
  have hk : ∀ t, HasDerivAt k (k' t) t := fun t => by
    have h1 := (hg (x + t)).comp t ((hasDerivAt_id t).const_add x)
    have h2 := ((hasDerivAt_id t).mul_const (g' x))
    have h3 := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
    have h4 := ((h1.sub_const (g x)).sub h2).sub h3
    convert h4 using 1
    · funext s; simp [k]
    · simp [k']; ring
  have hk' : ∀ t, HasDerivAt k' (g'' (x + t) - M) t := fun t => by
    have h1 := (hg' (x + t)).comp t ((hasDerivAt_id t).const_add x)
    have h4 := (h1.sub_const (g' x)).sub ((hasDerivAt_id t).const_mul M)
    convert h4 using 1
    · funext s; simp [k']
    · simp
  have hk'anti : Antitone k' := antitone_of_deriv_nonpos (fun t => (hk' t).differentiableAt)
    fun t => by rw [(hk' t).deriv]; linarith [hM (x + t)]
  have hk'0 : k' 0 = 0 := by simp [k']
  have hk0 : k 0 = 0 := by simp [k]
  have : k h ≤ 0 := by
    rcases le_total 0 h with h0 | h0
    · have hanti : AntitoneOn k (Set.Ici 0) :=
        antitoneOn_of_deriv_nonpos (convex_Ici 0)
            (fun t _ => (hk t).continuousAt.continuousWithinAt)
          (fun t _ => (hk t).differentiableAt.differentiableWithinAt) fun t ht => by
            rw [interior_Ici] at ht
            rw [(hk t).deriv, ← hk'0]; exact hk'anti (le_of_lt ht)
      exact hk0 ▸ hanti ((Set.mem_Ici.2 le_rfl)) h0 h0
    · have hmono : MonotoneOn k (Set.Iic 0) :=
        monotoneOn_of_deriv_nonneg (convex_Iic 0)
            (fun t _ => (hk t).continuousAt.continuousWithinAt)
          (fun t _ => (hk t).differentiableAt.differentiableWithinAt) fun t ht => by
            rw [interior_Iic] at ht
            rw [(hk t).deriv, ← hk'0]; exact hk'anti (le_of_lt ht)
      exact hk0 ▸ hmono h0 ((Set.mem_Iic.2 le_rfl)) h0
  simp only [k] at this; linarith

/-- **Taylor, order two.** With `|g''| ≤ M` everywhere, `|g (x + h) - g x - h · g' x| ≤ M h² / 2`.
-/
theorem abs_taylor_two_sub_le {g g' g'' : ℝ → ℝ} {M : ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hM : ∀ x, |g'' x| ≤ M) (x h : ℝ) :
    |g (x + h) - g x - h * g' x| ≤ M * h ^ 2 / 2 := by
  rw [abs_le]
  constructor
  · have := taylor_two_sub_le (g := fun y => -g y) (g' := fun y => -g' y) (g'' := fun y => -g'' y)
      (fun y => (hg y).neg) (fun y => (hg' y).neg) (fun y => by linarith [(abs_le.1 (hM y)).1]) x h
    linarith
  · exact taylor_two_sub_le hg hg' (fun y => (abs_le.1 (hM y)).2) x h

end Real
