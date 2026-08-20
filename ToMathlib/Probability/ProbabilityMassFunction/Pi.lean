/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Independent products of probability mass functions

`PMF.pi f` is the distribution on `ι → β` drawing each coordinate `i` independently from `f i`.
Mathlib's `PMF` API has `map`, `seq`, and `bind` but no product over an indexed family, so the
construction is built directly from `PMF.ofFintype` with the product weight; `Fintype.prod_sum`
turns the total mass into a product of per-coordinate masses, each of which is `1`.

Two facts are what callers need: the pointwise weight (`pi_apply`, definitionally the product) and
the marginal of a single coordinate (`sum_filter_pi`), which is where the product structure is
actually used.

Both index and value types are required to be finite. That is what `PMF.ofFintype` needs, and it
is the regime the coordinate-wise forking development works in; an infinite value type would
require the corresponding `tsum`-of-products identity instead.
-/

@[expose] public section

open Finset

open scoped ENNReal

namespace PMF

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- The distribution on `ι → β` drawing coordinate `i` from `f i`, independently across `i`. -/
noncomputable def pi (f : ι → PMF β) : PMF (ι → β) :=
  PMF.ofFintype (fun g => ∏ i, f i (g i)) <| by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun i _ => by
      rw [← tsum_fintype (L := .unconditional _)]; exact (f i).tsum_coe

omit [DecidableEq β] in
theorem pi_apply (f : ι → PMF β) (g : ι → β) : pi f g = ∏ i, f i (g i) := rfl

/-- The marginal of a single coordinate is exactly its intended factor.

Deleting every value but `b₀` at coordinate `i₀` is the same as restricting the sum to those
functions taking `b₀` there, and it turns the sum over functions into a product of per-coordinate
masses in which every coordinate but `i₀` contributes `1`. -/
theorem sum_filter_pi (f : ι → PMF β) (i₀ : ι) (b₀ : β) :
    ∑ g ∈ Finset.univ.filter fun g : ι → β => g i₀ = b₀, pi f g = f i₀ b₀ := by
  classical
  -- The weight family with every value but `b₀` deleted at coordinate `i₀`.
  set w : ι → β → ℝ≥0∞ :=
    fun i b => if i = i₀ then (if b = b₀ then f i₀ b₀ else 0) else f i b with hw
  have hsum : ∀ i : ι, ∑ b : β, w i b = if i = i₀ then f i₀ b₀ else 1 := by
    intro i
    by_cases hi : i = i₀
    · simp [hw, hi]
    · simp only [hw, if_neg hi]
      rw [← tsum_fintype (L := .unconditional _)]
      exact (f i).tsum_coe
  have hrestrict : ∀ g : ι → β,
      (∏ i, w i (g i)) = if g i₀ = b₀ then ∏ i, f i (g i) else 0 := by
    intro g
    by_cases hg : g i₀ = b₀
    · refine (if_pos hg) ▸ Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = i₀
      · subst hi; simp [hw, hg]
      · simp [hw, hi]
    · rw [if_neg hg]
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hw, hg])
  calc ∑ g ∈ Finset.univ.filter fun g : ι → β => g i₀ = b₀, pi f g
      = ∑ g : ι → β, if g i₀ = b₀ then ∏ i, f i (g i) else 0 := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun g _ => by rw [pi_apply]
    _ = ∑ g : ι → β, ∏ i, w i (g i) := (Finset.sum_congr rfl fun g _ => hrestrict g).symm
    _ = ∏ i, ∑ b : β, w i b := (Fintype.prod_sum _).symm
    _ = f i₀ b₀ := by rw [Finset.prod_congr rfl fun i _ => hsum i]; simp

/-- Two coordinates: the weight really is the product of the per-coordinate weights, so the
construction is independent rather than merely correct on marginals. -/
example (f : Fin 2 → PMF Bool) : pi f ![true, false] = f 0 true * f 1 false := by
  simp [pi_apply, Fin.prod_univ_two]

end PMF
