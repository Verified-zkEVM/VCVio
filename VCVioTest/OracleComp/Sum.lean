/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Output-mass sums of oracle computations

The sum forms of `VCVio.OracleComp.EvalDist.Sum` on uniform sampling: masses sum to one, an event
is the sum of its outputs' masses, a bind event is a prefix-weighted sum, and `pure` and maps reduce
weighted sums.
-/

public section

open OracleComp
open scoped ENNReal

namespace VCVioTest.OracleCompSum

example (oa : ProbComp ℕ) : ∑' n, Pr{let y ← oa}[y = n] = 1 := by simp

example (oa : ProbComp ℕ) :
    Pr{let y ← oa}[2 ≤ y] = ∑' n, if 2 ≤ n then Pr{let y ← oa}[y = n] else 0 :=
  prEvent_eq_tsum_ite oa _

example (oa : ProbComp ℕ) (n : ℕ) (h : n ∉ support oa) : Pr{let y ← oa}[y = n] = 0 :=
  prEvent_eq_zero_of_not_mem_support oa h

example (oa : ProbComp ℕ) :
    Pr{let y ← oa}[2 ≤ y] ≤ ∑' n, Pr{let y ← oa}[y = n] * (n / 2 : ℝ≥0∞) :=
  prEvent_le_tsum_prEvent_mul_cost oa _ _ fun n hn ↦ by
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
    exact_mod_cast hn

example (f : Bool → ProbComp Bool) (p : Bool → Prop) :
    Pr{let y ← ($ᵗ Bool : ProbComp Bool) >>= f}[p y] =
      ∑' b, Pr{let z ← ($ᵗ Bool : ProbComp Bool)}[z = b] * Pr{let y ← f b}[p y] :=
  prEvent_bind_eq_tsum _ f p

example (f : Bool → ProbComp Bool) :
    Pr{let b ← ($ᵗ Bool : ProbComp Bool); let y ← f b}[y = true] =
      ∑' b, Pr{let z ← ($ᵗ Bool : ProbComp Bool)}[z = b] * Pr{let y ← f b}[y = true] :=
  prEvent_bind_eq_tsum_prEvent _ _

example (a : ℕ) (w : ℕ → ℝ≥0∞) :
    ∑' n, Pr{let y ← (pure a : ProbComp ℕ)}[y = n] * w n = w a := by simp

example (oa : ProbComp ℕ) (w : ℕ → ℝ≥0∞) :
    ∑' n, Pr{let y ← (· + 1) <$> oa}[y = n] * w n = ∑' n, Pr{let y ← oa}[y = n] * w (n + 1) :=
  tsum_prEvent_map_mul oa _ w

example (oa : ProbComp ℕ) (w : ℕ → ℝ≥0∞) (h : ∀ n ∈ support oa, w n = 2) :
    ∑' n, Pr{let y ← oa}[y = n] * w n = 2 :=
  tsum_prEvent_mul_of_const_on_support oa h

end VCVioTest.OracleCompSum
